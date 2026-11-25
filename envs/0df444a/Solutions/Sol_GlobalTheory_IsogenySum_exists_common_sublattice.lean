-- Prove2me | solution 1 for GlobalTheory.IsogenySum.exists_common_sublattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:31.684241+00:00
-- url     : https://prove2.me/submissions/0094cb60-5223-4dd1-aa6c-7b3420166924

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y Y' : GT ι) (R : Finset (EuclideanSpace ℂ ι))
    (hR' : ∀ y ∈ lat Y'.b, ∃ r ∈ R, y - r ∈ lat Y.b) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι),
      lat b ≤ lat Y.b ∧ lat b ≤ lat Y'.b := by
  have hN : ∀ i, ∃ N : ℤ, N ≠ 0 ∧ N • Y'.b i ∈ lat Y.b := by
    intro i
    have hi : Y'.b i ∈ lat Y'.b := Submodule.subset_span ⟨i, rfl⟩
    choose r hr hr' using fun n : ℤ => hR' (n • Y'.b i) ((lat Y'.b).smul_mem n hi)
    obtain ⟨n, m, hnm, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => (⟨r n, hr n⟩ : R))
    have e' : r n = r m := congrArg Subtype.val e
    refine ⟨n - m, sub_ne_zero.2 hnm, ?_⟩
    have := (lat Y.b).sub_mem (hr' n) (hr' m)
    rw [e', sub_sub_sub_cancel_right] at this
    rwa [sub_smul]
  choose N hN0 hN using hN
  have hu : ∀ i, IsUnit (N i : ℝ) := fun i => (Int.cast_ne_zero.2 (hN0 i)).isUnit
  refine ⟨Y'.b.isUnitSMul hu, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact hN i
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact (lat Y'.b).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.IsogenySum
