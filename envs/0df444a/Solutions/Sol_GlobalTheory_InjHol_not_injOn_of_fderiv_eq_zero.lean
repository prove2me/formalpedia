-- Prove2me | solution 1 for GlobalTheory.InjHol.not_injOn_of_fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:53.407778+00:00
-- url     : https://prove2.me/submissions/a46f6615-ebb7-4b63-8edd-10390b482565

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Nontrivial E] {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) (h0 : ∀ᶠ x in 𝓝 a, fderiv ℂ f x = 0) {s : Set E} (hs : s ∈ 𝓝 a) :
    ¬ InjOn f s := by
  intro hinj
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hf.eventually_analyticAt.and (h0.and hs))
  have hd : DifferentiableOn ℂ f (ball a r) := fun x hx =>
    (hb x hx).1.differentiableAt.differentiableWithinAt
  have hnb : (𝓝[≠] a).NeBot := Module.punctured_nhds_neBot ℂ E a
  obtain ⟨x, hx, hxa⟩ := ((show ∀ᶠ x in 𝓝[≠] a, x ∈ ball a r from
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr)).and self_mem_nhdsWithin).exists
  exact hxa (hinj (hb x hx).2.2 (mem_of_mem_nhds hs)
    (isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℂ) (convex_ball a r).isPreconnected hd
      (fun y hy => (hb y hy).2.1) hx (mem_ball_self hr)))
end GlobalTheory.InjHol
