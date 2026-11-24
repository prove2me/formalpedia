-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.eta_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:04.095421+00:00
-- url     : https://prove2.me/submissions/a5cdda87-f88f-445e-ae9f-ce4818bd3cff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_norm_eq_of_sub_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta x = eta y := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have := norm_eq_of_sub_lt hy
  unfold eta
  rw [this]
end GlobalTheory.JR.LinDesc.Swap
