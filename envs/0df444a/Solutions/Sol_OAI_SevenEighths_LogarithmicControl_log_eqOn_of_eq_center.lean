-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.log_eqOn_of_eq_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:44.838129+00:00
-- url     : https://prove2.me/submissions/4dc72878-e3a4-4090-beb3-27eac69b9e98

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq
end OAI.SevenEighths.LogarithmicControl
