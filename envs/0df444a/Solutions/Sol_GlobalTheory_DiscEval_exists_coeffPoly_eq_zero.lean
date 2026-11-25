-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_coeffPoly_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:42.97708+00:00
-- url     : https://prove2.me/submissions/d1dc21b3-084a-4483-a286-6de6c5fe8e67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {K : Type*} [Field K] {σ τ : Type*}
namespace GlobalTheory.DiscEval
theorem _root_.solution (G : MvPolynomial σ K⸨X⸩) :
    ∃ b : ℕ, ∀ m : ℤ, m < -(b : ℤ) → coeffPoly m G = 0 := by
  refine ⟨G.support.sup fun μ => (-(coeff μ G).order).toNat, fun m hm => ?_⟩
  ext μ
  rw [coeff_coeffPoly, coeff_zero]
  by_cases h : μ ∈ G.support
  · have := Finset.le_sup (f := fun μ => (-(coeff μ G).order).toNat) h
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  · simp [notMem_support_iff.1 h]
end GlobalTheory.DiscEval
