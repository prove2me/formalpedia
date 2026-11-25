-- Prove2me | solution 1 for GlobalTheory.DiscEval.algDisc_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:21.25309+00:00
-- url     : https://prove2.me/submissions/b2d3759c-254e-40d7-b1d6-c75151f6c826

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_exists_abs_norm_sub_lt

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
namespace GlobalTheory.DiscEval
theorem _root_.solution (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ algDisc p, |‖t‖ - r| < ε := by
  obtain ⟨x, hx0, hx1, hx⟩ := exists_abs_norm_sub_lt (C := PadicAlgCl p) h0 h1 hε
  rw [← PadicComplex.norm_extends] at hx0 hx1 hx
  exact ⟨x, ⟨⟨x, rfl⟩, hx0, hx1⟩, hx⟩
end GlobalTheory.DiscEval
