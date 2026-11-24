-- Prove2me | solution 1 for GlobalTheory.differentiable_of_continuous_of_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:55.417685+00:00
-- url     : https://prove2.me/submissions/5e7aa622-3355-48df-be36-e915232aad14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {q : V → ℂ} (hq : Continuous q)
    (hf : Differentiable ℂ fun v => cexp (q v)) : Differentiable ℂ q := by
  intro x
  have hc : Continuous fun v => (q v - q x).im := by fun_prop
  have hev : ∀ᶠ v in 𝓝 x, (q v - q x).im ∈ Ioo (-Real.pi) Real.pi :=
    hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simp [Real.pi_pos]))
  have he : q =ᶠ[𝓝 x] fun v => q x + log (cexp (q v) * cexp (-q x)) := by
    filter_upwards [hev] with v hv
    rw [← exp_add, ← sub_eq_add_neg, log_exp hv.1 hv.2.le]
    ring
  refine DifferentiableAt.congr_of_eventuallyEq ?_ he
  refine DifferentiableAt.const_add _ (DifferentiableAt.clog ((hf x).mul_const _) ?_)
  simp [← exp_add]
end GlobalTheory
