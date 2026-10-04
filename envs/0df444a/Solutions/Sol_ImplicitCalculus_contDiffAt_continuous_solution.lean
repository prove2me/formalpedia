-- Prove2me | solution 1 for ImplicitCalculus.contDiffAt_continuous_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T19:52:49.994844+00:00
-- url     : https://prove2.me/submissions/5cb33769-c5ef-4dc0-bcfd-40bce6cbbad2

import Mathlib.Analysis.Calculus.ImplicitContDiff

open Filter
open scoped Topology ContDiff
set_option autoImplicit false

theorem solution {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (n : ℕ∞ω) (hn : n ≠ 0) (f : E × G → F) (r : E → G) (u : E)
    (hf : ContDiffAt 𝕜 n f (u, r u)) (hr : ContinuousAt r u)
    (hi : ((fderiv 𝕜 f (u, r u)).comp
      (ContinuousLinearMap.inr 𝕜 E G)).IsInvertible)
    (heq : ∀ᶠ x in 𝓝 u, f (x, r x) = f (u, r u)) :
    ContDiffAt 𝕜 n r u := by
  let ψ := hf.implicitFunction hn hi
  have hψ : ContDiffAt 𝕜 n ψ u := hf.contDiffAt_implicitFunction hn hi
  have hlocal := hf.eventually_apply_eq_iff_implicitFunction hn hi
  have ht : Tendsto (fun x => (x, r x)) (𝓝 u) (𝓝 (u, r u)) :=
    continuousAt_id.prodMk hr
  have hevent : r =ᶠ[𝓝 u] ψ := by
    filter_upwards [ht.eventually hlocal, heq] with x hx hroot
    exact (hx.mp hroot).symm
  exact hψ.congr_of_eventuallyEq hevent
