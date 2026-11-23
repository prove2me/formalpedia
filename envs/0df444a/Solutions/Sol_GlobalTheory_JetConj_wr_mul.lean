-- Prove2me | solution 1 for GlobalTheory.JetConj.wr_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:37.657185+00:00
-- url     : https://prove2.me/submissions/14841a12-f900-4f3e-ab6c-7b11d4553d80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
namespace GlobalTheory.JetConj
theorem _root_.solution {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    wr (fun w => f w * g w) z = wr f z * g z ^ 2 + f z ^ 2 * wr g z := by
  have e : deriv (fun w => f w * g w) =ᶠ[𝓝 z] fun w => deriv f w * g w + f w * deriv g w := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w a b
    exact (a.differentiableAt.hasDerivAt.fun_mul b.differentiableAt.hasDerivAt).deriv
  have a := hf.differentiableAt.hasDerivAt
  have b := hg.differentiableAt.hasDerivAt
  have a' := hf.deriv.differentiableAt.hasDerivAt
  have b' := hg.deriv.differentiableAt.hasDerivAt
  unfold wr
  rw [e.deriv.eq_of_nhds, e.eq_of_nhds, ((a'.fun_mul b).fun_add (a.fun_mul b')).deriv]
  ring
end GlobalTheory.JetConj
