-- Prove2me | solution 1 for GlobalTheory.PerronKernel.le_of_forall_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:04.386835+00:00
-- url     : https://prove2.me/submissions/1b75d664-ed6a-4a76-9e8b-241bb392da8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution {x B K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (h : ∀ U : ℝ, c ≤ U → x ≤ B + K / U) : x ≤ B := by
  have h0 : Filter.Tendsto (fun U : ℝ => K / U) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim := h0.const_add B
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim ((Filter.eventually_ge_atTop c).mono fun U hU => h U hU)
end GlobalTheory.PerronKernel
