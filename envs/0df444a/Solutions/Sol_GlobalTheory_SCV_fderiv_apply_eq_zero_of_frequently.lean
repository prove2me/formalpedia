-- Prove2me | solution 1 for GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:22.13423+00:00
-- url     : https://prove2.me/submissions/6d51e41e-7d55-45f5-9178-98437537fced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace

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
theorem _root_.solution {f : E → V} {x s : E} (hf : DifferentiableAt ℂ f x)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (x + t • s) = f x) : fderiv ℂ f x s = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • s)) (fderiv ℂ f x s) 0 :=
    hf.hasFDerivAt.hasLineDerivAt s
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  refine tendsto_nhds_unique_of_frequently_eq h1 tendsto_const_nhds (h.mono fun t ht => ?_)
  simp [ht]
end GlobalTheory.SCV
