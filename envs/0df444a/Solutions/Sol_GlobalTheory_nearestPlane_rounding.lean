-- Prove2me | solution 1 for GlobalTheory.nearestPlane_rounding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:31.008899+00:00
-- url     : https://prove2.me/submissions/47875ac7-f6b8-47ba-af8f-9ff69cd49f49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NearestPlaneRounding
import Theorems.Thm_GlobalTheory_exists_int_comb_norm_sub_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Ext.NearestPlane := by
  intro V _ _ n v _ x hx
  obtain ⟨w, hw, hle⟩ := exists_int_comb_norm_sub_sq_le n v hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw
  refine ⟨c, ?_⟩
  have hsum : ∑ i, ((c i : ℤ) : ℝ) • v i = ∑ i, c i • v i := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hsum]
  linarith
end GlobalTheory
