-- Prove2me | solution 1 for Monotonicity_Theorem.cut_points_avoiding_finite_set
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T20:12:34.309067+00:00
-- url     : https://prove2.me/submissions/50101426-5f34-43a9-8dd1-f71bff65982c

import Definitions.Def_Monotonicity_Theorem_Framework

set_option autoImplicit false

open Monotonicity_Theorem

namespace CutPointsAux

variable {R : Type}

/-- One step of a cut-point chain: `u < v` and no listed value lies strictly between. -/
def Step (D : DenseLinearOrderNoEndpoints R) (L : List R) (u v : R) : Prop :=
  D.lt u v ∧ ∀ c ∈ L, ¬ (D.lt u c ∧ D.lt c v)

/-- `GoodChain D L a m b` says that `a :: m ++ [b]` is a chain of consecutive `Step`s. -/
def GoodChain (D : DenseLinearOrderNoEndpoints R) (L : List R) : R → List R → R → Prop
  | a, [], b => Step D L a b
  | a, c :: m, b => Step D L a c ∧ GoodChain D L c m b

lemma goodChain_lt (D : DenseLinearOrderNoEndpoints R) (L : List R) :
    ∀ (m : List R) (a b : R), GoodChain D L a m b → D.lt a b := by
  intro m
  induction m with
  | nil => intro a b h; exact h.1
  | cons c m ih => intro a b h; exact D.trans h.1.1 (ih c b h.2)

/-- A chain avoiding `L` also avoids `c :: L`, provided `c` is not strictly inside `(a,b)`. -/
lemma goodChain_weaken (D : DenseLinearOrderNoEndpoints R) (L : List R) (c : R) :
    ∀ (m : List R) (a b : R), GoodChain D L a m b → ¬ (D.lt a c ∧ D.lt c b) →
      GoodChain D (c :: L) a m b := by
  intro m
  induction m with
  | nil =>
      intro a b h hc
      refine ⟨h.1, ?_⟩
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hc
      · exact h.2 d hd
  | cons u m ih =>
      intro a b h hc
      have hub : D.lt u b := goodChain_lt D L m u b h.2
      refine ⟨⟨h.1.1, ?_⟩, ?_⟩
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · rintro ⟨h1, h2⟩
          exact hc ⟨h1, D.trans h2 hub⟩
        · exact h.1.2 d hd
      · refine ih u b h.2 ?_
        rintro ⟨h1, h2⟩
        exact hc ⟨D.trans h.1.1 h1, h2⟩

lemma goodChain_append (D : DenseLinearOrderNoEndpoints R) (L : List R) :
    ∀ (m₁ : List R) (a c : R) (m₂ : List R) (b : R),
      GoodChain D L a m₁ c → GoodChain D L c m₂ b → GoodChain D L a (m₁ ++ c :: m₂) b := by
  intro m₁
  induction m₁ with
  | nil => intro a c m₂ b h₁ h₂; exact ⟨h₁, h₂⟩
  | cons u m₁ ih => intro a c m₂ b h₁ h₂; exact ⟨h₁.1, ih u c m₂ b h₁.2 h₂⟩

/-- Every finite list of values can be avoided by the open pieces of some finite chain. -/
lemma exists_goodChain (D : DenseLinearOrderNoEndpoints R) :
    ∀ (L : List R) (a b : R), D.lt a b → ∃ m : List R, GoodChain D L a m b := by
  intro L
  induction L with
  | nil =>
      intro a b hab
      exact ⟨[], hab, by simp⟩
  | cons c L ih =>
      intro a b hab
      by_cases hc : D.lt a c ∧ D.lt c b
      · obtain ⟨m₁, h₁⟩ := ih a c hc.1
        obtain ⟨m₂, h₂⟩ := ih c b hc.2
        refine ⟨m₁ ++ c :: m₂, goodChain_append D (c :: L) m₁ a c m₂ b ?_ ?_⟩
        · exact goodChain_weaken D L c m₁ a c h₁ (fun h => D.irrefl c h.2)
        · exact goodChain_weaken D L c m₂ c b h₂ (fun h => D.irrefl c h.1)
      · obtain ⟨m, h⟩ := ih a b hab
        exact ⟨m, goodChain_weaken D L c m a b h hc⟩

/-- Turn a chain into a tuple of cut points. -/
lemma goodChain_to_tuple (D : DenseLinearOrderNoEndpoints R) (L : List R) :
    ∀ (m : List R) (a b : R), GoodChain D L a m b →
      ∃ k : Nat, ∃ q : Fin (k + 1) → R,
        q 0 = a ∧ q (Fin.last k) = b ∧ ∀ i : Fin k, Step D L (q i.castSucc) (q i.succ) := by
  intro m
  induction m with
  | nil =>
      intro a b h
      refine ⟨1, Fin.cons a (fun _ => b), Fin.cons_zero _ _, ?_, ?_⟩
      · show (Fin.cons a (fun _ => b) : Fin 2 → R) (Fin.succ (0 : Fin 1)) = b
        rw [Fin.cons_succ]
      · intro i
        refine Fin.cases ?_ (fun j => j.elim0) i
        show Step D L ((Fin.cons a (fun _ => b) : Fin 2 → R) (0 : Fin 2))
          ((Fin.cons a (fun _ => b) : Fin 2 → R) (Fin.succ (0 : Fin 1)))
        rw [Fin.cons_zero, Fin.cons_succ]
        exact h
  | cons u m ih =>
      intro a b h
      obtain ⟨k, q, hq0, hqlast, hqstep⟩ := ih u b h.2
      refine ⟨k + 1, Fin.cons a q, Fin.cons_zero _ _, ?_, ?_⟩
      · show (Fin.cons a q : Fin (k + 2) → R) (Fin.succ (Fin.last k)) = b
        rw [Fin.cons_succ, hqlast]
      · intro i
        refine Fin.cases ?_ ?_ i
        · show Step D L ((Fin.cons a q : Fin (k + 2) → R) (0 : Fin (k + 2)))
            ((Fin.cons a q : Fin (k + 2) → R) (Fin.succ (0 : Fin (k + 1))))
          rw [Fin.cons_zero, Fin.cons_succ, hq0]
          exact h.1
        · intro j
          have hc : (Fin.castSucc j.succ) = (Fin.castSucc j).succ := (Fin.succ_castSucc j).symm
          rw [hc, Fin.cons_succ, Fin.cons_succ]
          exact hqstep j

end CutPointsAux

open CutPointsAux in
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {F : Set (Power R 1)} (hF : IsFinite1 F) {a b : Power R 1} (hab : Lt1 D a b) :
    ∃ k : Nat, ∃ p : Fin (k + 1) → Power R 1,
      p 0 = a ∧ p (Fin.last k) = b ∧
      (∀ i : Fin k, Lt1 D (p i.castSucc) (p i.succ)) ∧
      (∀ i : Fin k, ∀ x : Power R 1,
        openInterval D (Endpoint.finite ((p i.castSucc) 0)) (Endpoint.finite ((p i.succ) 0)) x →
          ¬ F x) := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨m, hm⟩ := exists_goodChain D L (a 0) (b 0) hab
  obtain ⟨k, q, hq0, hqlast, hqstep⟩ := goodChain_to_tuple D L m (a 0) (b 0) hm
  have hpt : ∀ x : Power R 1, (fun _ : Fin 1 => x 0) = x := by
    intro x
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
  refine ⟨k, fun i => fun _ => q i, ?_, ?_, ?_, ?_⟩
  · simp only [hq0]; exact hpt a
  · simp only [hqlast]; exact hpt b
  · intro i; exact (hqstep i).1
  · intro i x hx hFx
    exact (hqstep i).2 (x 0) ((hL x).1 hFx) ⟨hx.1, hx.2⟩
