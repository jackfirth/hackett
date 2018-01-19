#lang hackett

(data Unit Unit)
(data Void (Void Void))
(data (Pair a b) (Pair a b))
(data (Either a b) (Left a) (Right b))

(defn absurd! : (∀ [a] {Void -> a})
  [[(Void v)] (absurd! v)])

;; elided due to lack of rank 2 types: impossible! : (forall a. a) -> Void

(class (Voidful f)
  [void* : (f Void)])

(class (Unitful f)
  [unit* : (f Unit)])

(class (Invariant f)
  [inv-map : (∀ [a b] {(Pair {a -> b} {b -> a}) -> (f a) -> (f b)})])

(class (Functor f)
  [map : (∀ [a b] {{a -> b} -> (f a) -> (f b)})])

(instance
 (∀ [f] (Functor f) => (Invariant f))
 [inv-map (λ [(Pair mapper _) x] (map mapper x))])

(class (Contravariant f)
  [contramap : (∀ [a b] {{b -> a} -> (f a) -> (f b)})])

(instance
 (∀ [f] (Contravariant f) => (Invariant f))
 [inv-map (λ [(Pair _ contramapper) x] (contramap contramapper x))])

(class (Unitful f) (Functor f) => (Applicative f)
  [unite : (∀ [a b] {(f a) -> (f b) -> (f (Pair a b))})])

(class (Voidful f) (Functor f) => (Alternative f)
  [choice : (∀ [a b] {(f a) -> (f b) -> (f (Either a b))})])

(class (Unitful f) (Contravariant f) => (Divisible f)
  [divide : (∀ [a b] {(f a) -> (f b) -> (f (Pair a b))})])

(class (Voidful f) (Contravariant f) => (Decidable f)
  [decide : (∀ [a b] {(f a) -> (f b) -> (f (Either a b))})])


;; Goodies

(defn pure : (∀ [f a] (Functor f) (Unitful f) => {a -> (f a)})
  [[v] (map (λ [_] v) unit*)])

(def vacuous : (∀ [f a] (Functor f) (Voidful f) => (f a))
  (map absurd! void*))

(def trivial : (∀ [f a] (Contravariant f) (Unitful f) => (f a))
  (contramap (const Unit) unit*))

(defn refute : (∀ [f a] (Contravariant f) (Voidful f) => {{a -> Void} -> (f a)})
  [[prove-impossible] (contramap prove-impossible void*)])
