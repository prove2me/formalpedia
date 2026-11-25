-- Prove2me | solution 1 for GlobalTheory.DiscEval.norm_coeff_detProdPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:26.656182+00:00
-- url     : https://prove2.me/submissions/8b298ef1-65e8-409d-bd40-ced37bb5ff50

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
variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.DiscEval
theorem _root_.solution {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] (μ : EntryIndex n n →₀ ℕ) : ‖coeff μ (detProdPoly K n)‖ ≤ 1 := by
  have h : map (Int.castRingHom K) (detProdPoly ℤ n) = detProdPoly K n := by
    rw [detProdPoly, detProdPoly, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i j : 2
    simp
  rw [← h, coeff_map]
  exact IsUltrametricDist.norm_intCast_le_one K _
end GlobalTheory.DiscEval
