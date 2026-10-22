-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:18:00.64578+00:00
-- url     : https://prove2.me/submissions/9e911fea-b2ca-4ab4-97fd-f4f655b16f32

import Mathlib.Tactic
import Definitions.Def_allocationSum

open scoped BigOperators

namespace WWAlloc

/-- the summand of `allocationSum` -/
def aw {σ : Type*} [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (k : ℕ) (n : σ → Fin (k + 1)) : ℕ :=
  if ∑ i, (n i : ℕ) = k then
    ∏ i, (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
          else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
  else 0

theorem sum_supp {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p] (f : σ → ℕ)
    (h : ∀ i, ¬ p i → f i = 0) : ∑ i, f i = ∑ i : {i // p i}, f i.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp) f]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply h
  simpa using hi

theorem prod_supp {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p] (f : σ → ℕ)
    (h : ∀ i, ¬ p i → f i = 1) : ∏ i, f i = ∏ i : {i // p i}, f i.1 := by
  rw [← Finset.prod_subtype (Finset.univ.filter p) (by simp) f]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply h
  simpa using hi

end WWAlloc

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      OAI.PiExponent.LiteralAnalytic.allocationSum
        (fun i : {j : σ // e j ≠ 0} => e i.1) k := by
  classical
  have hL : OAI.PiExponent.LiteralAnalytic.allocationSum e k
      = ∑ n : σ → Fin (k + 1), WWAlloc.aw e k n := rfl
  have hR : OAI.PiExponent.LiteralAnalytic.allocationSum (fun i : {j : σ // e j ≠ 0} => e i.1) k
      = ∑ m : {j : σ // e j ≠ 0} → Fin (k + 1), WWAlloc.aw (fun i : {j : σ // e j ≠ 0} => e i.1) k m := rfl
  rw [hL, hR]
  -- restrict the left sum to functions vanishing off the support
  have h1 : ∑ n : σ → Fin (k + 1), WWAlloc.aw e k n
      = ∑ n : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0}, WWAlloc.aw e k n.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun n : σ → Fin (k + 1) => ∀ i, e i = 0 → n i = 0))
      (p := fun n : σ → Fin (k + 1) => ∀ i, e i = 0 → n i = 0) (by intro n; simp)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n _ hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hn
    obtain ⟨i, hi0, hi⟩ := hn
    unfold WWAlloc.aw
    split_ifs with hs
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [if_pos hi0, if_neg]
      intro h
      exact hi (Fin.ext h)
    · rfl
  rw [h1]
  let E : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0} ≃ ({j : σ // e j ≠ 0} → Fin (k + 1)) :=
    { toFun := fun n i => n.1 i.1
      invFun := fun m => ⟨fun i => if h : e i ≠ 0 then m ⟨i, h⟩ else 0, by
        intro i hi; simp [hi]⟩
      left_inv := by
        intro n
        apply Subtype.ext
        funext i
        by_cases h : e i ≠ 0
        · simp [h]
        · have : e i = 0 := by simpa using h
          simp [h, n.2 i this]
      right_inv := by
        intro m
        funext i
        simp [i.2] }
  refine Fintype.sum_equiv E _ _ ?_
  intro n
  have hn0 : ∀ i, ¬ (e i ≠ 0) → (n.1 i : ℕ) = 0 := by
    intro i hi
    have : e i = 0 := by simpa using hi
    simp [n.2 i this]
  unfold WWAlloc.aw
  rw [WWAlloc.sum_supp (fun i => e i ≠ 0) (fun i => (n.1 i : ℕ)) hn0]
  rw [WWAlloc.prod_supp (fun i => e i ≠ 0)
    (fun i => (if e i = 0 then (if (n.1 i : ℕ) = 0 then 1 else 0)
          else Nat.choose ((n.1 i : ℕ) + e i - 1) (n.1 i : ℕ)))]
  · have : ∀ i : {j : σ // e j ≠ 0}, ((E n i : Fin (k+1)) : ℕ) = (n.1 i.1 : ℕ) := fun i => rfl
    simp only [this]
  · intro i hi
    have : e i = 0 := by simpa using hi
    simp [this, n.2 i this]
