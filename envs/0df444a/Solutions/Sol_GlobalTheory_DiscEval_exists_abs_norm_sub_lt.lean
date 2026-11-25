-- Prove2me | solution 1 for GlobalTheory.DiscEval.exists_abs_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:07.685316+00:00
-- url     : https://prove2.me/submissions/6b6c567f-1e9f-4fd3-a1a6-085478128732

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames

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
namespace GlobalTheory.DiscEval
theorem _root_.solution {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {r ε : ℝ}
    (h0 : 0 < r) (h1 : r < 1) (hε : 0 < ε) : ∃ x : C, 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ |‖x‖ - r| < ε := by
  obtain ⟨x, hx, hx1⟩ := exists_lt_norm_lt_one_of_isAlgClosed (C := C) (max 0 (1 - ε))
    (max_lt one_pos (by linarith))
  rw [max_lt_iff] at hx
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one h0 h1.le hx.1 hx1
  have h2 : ‖x‖ ^ n ≤ 1 := pow_le_one₀ hx.1.le hx1.le
  refine ⟨x ^ (n + 1), by rw [norm_pow]; exact pow_pos hx.1 _, by rw [norm_pow]; linarith, ?_⟩
  rw [norm_pow, abs_lt]
  rw [pow_succ] at hn ⊢
  constructor <;> nlinarith
end GlobalTheory.DiscEval
