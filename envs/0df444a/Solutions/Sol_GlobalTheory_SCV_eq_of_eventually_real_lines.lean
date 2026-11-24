-- Prove2me | solution 1 for GlobalTheory.SCV.eq_of_eventually_real_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:47.426344+00:00
-- url     : https://prove2.me/submissions/e6907a01-ea2f-482f-bd05-3b768c48a2e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Theorems.Thm_GlobalTheory_SCV_fderiv_eq_zero_of_real_lines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w :=
  hU.is_const_of_fderiv_eq_zero hU' hf
    (fun x hx => fderiv_eq_zero_of_real_lines hS (hf.differentiableAt (hU.mem_nhds hx)) (h x hx))
    hz hw
end GlobalTheory.SCV
