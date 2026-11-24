-- Prove2me | solution 1 for GlobalTheory.FormalSeries.two_le_order_sub_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:27:06.949354+00:00
-- url     : https://prove2.me/submissions/354ca61f-66e1-41c9-8b0e-558045110519

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_two_le_order_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution [Fintype σ] {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    2 ≤ (f - ∑ j, coeff (Finsupp.single j 1) f • X j).order := by
  classical
  refine two_le_order_iff.mpr ⟨?_, fun k => ?_⟩
  · simp [map_sub, map_sum, hf]
  · simp [map_sub, map_sum, coeff_index_single_X]
end GlobalTheory.FormalSeries
