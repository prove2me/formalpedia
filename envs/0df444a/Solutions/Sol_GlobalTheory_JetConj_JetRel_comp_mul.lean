-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:17.406945+00:00
-- url     : https://prove2.me/submissions/7f013292-6ea3-4032-9fca-3bfdeca6ea23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_mul

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
theorem _root_.solution (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f') {c : ℂ} (hc : (c, c) ∈ S)
    (H : JetRel S f f') : JetRel S (fun z => f (c * z)) (fun z => f' (c * z)) := by
  obtain ⟨-, -, hd⟩ := H
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  refine ⟨d1.analyticAt 0, d2.analyticAt 0, fun n => ?_⟩
  simp only [iteratedDeriv_comp_const_mul hf.contDiff c, iteratedDeriv_comp_const_mul hf'.contDiff c, mul_zero]
  exact pair_mul (by simpa using S.pow_mem hc n) (hd n)
end JetRel
end GlobalTheory.JetConj
