-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.exists_unit_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:13.41202+00:00
-- url     : https://prove2.me/submissions/257fbbdb-0926-4697-b33f-2ad75278b846

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_rowOp_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    {s : Finset ι} {k : ι} {A : Matrix ι ι R} (hA : IsUnit A.det)
    (hF : Fixed (insert k s) A) (hk : k ∉ s) :
    ∃ w : ι → R, w k = 0 ∧ Fixed (insert k s) (rowOp k w * A) ∧
      IsUnit ((rowOp k w * A) k k) := by
  set B := A⁻¹ with hB
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hA
  have hsum : ∑ l, B k l * A l k = 1 := by
    have := congrFun (congrFun hBA k) k
    simpa [Matrix.mul_apply] using this
  have hzero : ∀ l, l ∉ insert k s → A l k = 0 := by
    intro l hl
    have hlk : l ≠ k := fun h => hl (h ▸ Finset.mem_insert_self _ _)
    rw [hF l k (Or.inl hl), Matrix.one_apply_ne hlk]
  have hsplit : ∑ l, B k l * A l k = B k k * A k k + ∑ l ∈ s, B k l * A l k := by
    rw [← Finset.sum_insert (f := fun l => B k l * A l k) hk]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    rw [hzero l hl, mul_zero]
  set b := ∑ l ∈ s, B k l * A l k with hb
  have hcop : IsCoprime (A k k) b := ⟨B k k, 1, by rw [one_mul, ← hsplit, hsum]⟩
  obtain ⟨t, ht⟩ := hR _ _ hcop
  set w : ι → R := fun l => if l ∈ s then t * B k l else 0 with hw
  have hwsum : ∀ j, ∑ l, w l * A l j = t * ∑ l ∈ s, B k l * A l j := by
    intro j
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]
    · apply Finset.sum_congr rfl
      intro l hl
      simp [hw, hl, mul_assoc]
    · intro l _ hl
      simp [hw, hl]
  refine ⟨w, by simp [hw, hk], ?_, ?_⟩
  · intro i j hij
    rw [rowOp_mul_apply]
    by_cases hi : i = k
    · subst hi
      have hj : j ∉ insert i s := by
        rcases hij with h | h
        · exact absurd (Finset.mem_insert_self _ _) h
        · exact h
      have hji : i ≠ j := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      rw [if_pos rfl, hwsum, hF i j (Or.inr hj), Finset.sum_eq_zero, mul_zero, add_zero]
      intro l hl
      have hlj : l ≠ j := fun h => hj (h ▸ Finset.mem_insert_of_mem hl)
      rw [hF l j (Or.inr hj), Matrix.one_apply_ne hlj, mul_zero]
    · rw [if_neg hi, add_zero]
      exact hF i j hij
  · rw [rowOp_mul_apply, if_pos rfl, hwsum]
    exact ht
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
