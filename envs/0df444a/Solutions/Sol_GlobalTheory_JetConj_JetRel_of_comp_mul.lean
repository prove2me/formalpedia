-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.of_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:22.129797+00:00
-- url     : https://prove2.me/submissions/a56fbf9c-6e6c-435f-b780-d9f70fc72428

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_JetRel_comp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (hS : IsFieldGraph S) (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f')
    {c : ℂ} (hc0 : c ≠ 0) (hc : (c, c) ∈ S)
    (H : JetRel S (fun z => f (c * z)) (fun z => f' (c * z))) : JetRel S f f' := by
  have hc' : (c⁻¹, c⁻¹) ∈ S := hS.2 c c hc
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  simpa [mul_inv_cancel_left₀ hc0] using JetRel.comp_mul d1 d2 hc' H
end JetRel
end GlobalTheory.JetConj
