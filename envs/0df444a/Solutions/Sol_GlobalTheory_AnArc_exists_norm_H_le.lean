-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_norm_H_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:44.090043+00:00
-- url     : https://prove2.me/submissions/87a91043-8299-4b07-add2-62781edb6e52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution : ∃ C, 0 ≤ C ∧ ∀ z w, ‖A.H z w‖ ≤ C * ‖z‖ * ‖w‖ := by
  refine ⟨∑ i, ∑ k, ‖A.Hm i k‖, by positivity, fun z w => ?_⟩
  simp only [H, hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => norm_sum_le_of_le _ fun k _ => ?_
  simp only [norm_mul, Pi.star_apply, norm_star]
  have h1 := norm_le_pi_norm z i
  have h2 := norm_le_pi_norm w k
  calc ‖z i‖ * (‖A.Hm i k‖ * ‖w k‖) ≤ ‖z‖ * (‖A.Hm i k‖ * ‖w‖) := by gcongr
    _ = _ := by ring
end GlobalTheory.AnArc
