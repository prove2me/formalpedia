-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_shifted_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:31:18.201217+00:00
-- url     : https://prove2.me/submissions/8f3edf11-4e1e-4b0c-b8a0-856995470817

import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_mul
import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_add
import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Tactic.Push

open scoped ContDiff
open HunterPDE.Sobolev
set_option autoImplicit false

theorem sobolev_word_bridge {n : ℕ} (α : Fin n → ℕ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    iteratedPartial α u = HunterPDE.Shared.multiDeriv u α := by
  unfold iteratedPartial HunterPDE.Shared.multiDeriv HunterPDE.Shared.multiIndexList
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.flatMap_cons]
    rw [ih]
    generalize List.flatMap (fun i => List.replicate (α i) i) l = t
    induction α i with
    | zero => rfl
    | succ k ihk =>
      simp only [Function.iterate_succ_apply', List.replicate_succ, List.cons_append,
        HunterPDE.Shared.iteratedPartial]
      rw [ihk]
      rfl

theorem solution {n : ℕ}
    (η φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (δ β : Fin n → ℕ) (s : Finset (Fin n → ℕ))
    (hs : ∀ γ : Fin n → ℕ, (∀ i, γ i ≤ β i) → γ ∈ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial β (fun y => iteratedPartial δ η y * φ y) x =
      ∑ γ ∈ s, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
        (iteratedPartial (fun i => δ i + (β i - γ i)) η x *
          iteratedPartial γ φ x) := by
  classical
  have hd : ContDiff ℝ ∞ (iteratedPartial δ η) := by
    rw [sobolev_word_bridge, HunterPDE.Shared.multiDeriv]
    exact contDiffOn_univ.mp
      (HunterPDE.Shared.contDiffOn_iteratedPartial isOpen_univ hη.contDiffOn _)
  rw [HunterPDE.Sobolev.iteratedPartial_mul _ _ hd hφ β x]
  simp only [HunterPDE.Sobolev.iteratedPartial_add η hη]
  apply Finset.sum_subset
  · intro γ hγ
    exact hs γ (Finset.mem_Iic.mp hγ)
  · intro γ hγ hnot
    have hnotle : ¬ ∀ i, γ i ≤ β i := by
      simpa only [Finset.mem_Iic, Pi.le_def] using hnot
    push_neg at hnotle
    obtain ⟨i, hi⟩ := hnotle
    have hz : (∏ j, (Nat.choose (β j) (γ j) : ℝ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hz, zero_mul]
