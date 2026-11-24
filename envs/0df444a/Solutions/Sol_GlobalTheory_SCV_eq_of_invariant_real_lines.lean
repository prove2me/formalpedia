-- Prove2me | solution 1 for GlobalTheory.SCV.eq_of_invariant_real_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:01.232859+00:00
-- url     : https://prove2.me/submissions/b228d60c-afde-4a67-9162-9894808eefeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Theorems.Thm_GlobalTheory_SCV_eq_of_eventually_real_lines

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
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ t : ℝ, z + (t : ℂ) • s ∈ U → f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_eventually_real_lines hS hU hU' hf (fun x hx s hs => ?_) hz hw
  have h1 : Tendsto (fun t : ℝ => x + (t : ℂ) • s) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact (h1.eventually (hU.mem_nhds hx)).mono fun t ht => h x hx s hs t ht
end GlobalTheory.SCV
