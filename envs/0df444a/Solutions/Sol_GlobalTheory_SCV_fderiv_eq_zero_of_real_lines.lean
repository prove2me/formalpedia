-- Prove2me | solution 1 for GlobalTheory.SCV.fderiv_eq_zero_of_real_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:13.971945+00:00
-- url     : https://prove2.me/submissions/5f863661-b02f-417c-ac5c-7fef224e5489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Theorems.Thm_GlobalTheory_SCV_fderiv_apply_eq_zero_of_frequently
import Theorems.Thm_GlobalTheory_SCV_frequently_nhdsNE_of_eventually_ofReal

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
theorem _root_.solution {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by
  have : (fderiv ℂ f x : E →ₗ[ℂ] V) = 0 :=
    LinearMap.ext_on hS fun s hs => fderiv_apply_eq_zero_of_frequently hf
      (frequently_nhdsNE_of_eventually_ofReal (p := fun t => f (x + t • s) = f x) (h s hs))
  ext v
  exact LinearMap.congr_fun this v
end GlobalTheory.SCV
