-- Prove2me | solution 1 for GlobalTheory.DiscEval.isAdicComplete_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:17.05642+00:00
-- url     : https://prove2.me/submissions/83895cbe-e1d6-4fca-8636-f8c9108f944c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_pow_mem_map_maximalIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isAdicComplete_finite_algebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_map_maximalIdeal_le_maximal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory.DiscEval
theorem _root_.solution :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] L)) (integralClosure ℤ_[p] L) := by
  set S := integralClosure ℤ_[p] L
  set J := (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)
  have : IsAdicComplete J S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := ℤ_[p]) S
  have hJ : J ≤ maximalIdeal S :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[p]) S _ inferInstance
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ J := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := ℤ_[p]) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have he' : ∀ n, maximalIdeal S ^ ((e + 1) * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right e.le_succ).trans he) n
  have : IsPrecomplete (maximalIdeal S) S := ⟨fun u hu => by
    obtain ⟨l, hl⟩ := IsPrecomplete.prec' (I := J) (fun n => u ((e + 1) * n)) fun {m n} hmn =>
      (hu (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left (he' m))
    exact ⟨l, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans
      ((hl n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJ n)))⟩⟩
  exact ⟨⟩
end GlobalTheory.DiscEval
