-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T17:58:44.972185+00:00
-- url     : https://prove2.me/submissions/7dd6c0a2-4439-44f1-a316-ce67de4f198e

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (hx : (fderiv ℝ F x).IsInvertible)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, (fderiv ℝ F y).IsInvertible ∧
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F x).inverse‖ < ε := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hc := (hF.continuous_fderiv one_ne_zero).continuousAt (x := x)
  have ho : ∀ᶠ y in 𝓝 x, (fderiv ℝ F y).IsInvertible :=
    hc.eventually (ContinuousLinearEquiv.isOpen.mem_nhds hx)
  have hi : ContinuousAt (fun y => (fderiv ℝ F y).inverse) x :=
    (hx.contDiffAt_map_inverse (n := 0)).continuousAt.comp hc
  have hn : ∀ᶠ y in 𝓝 x,
      ‖(fderiv ℝ F y).inverse - (fderiv ℝ F x).inverse‖ < ε := by
    simpa only [Metric.mem_ball,dist_eq_norm] using
      hi.eventually (Metric.ball_mem_nhds (fderiv ℝ F x).inverse hε)
  obtain ⟨δ,hδ,h⟩ := Metric.eventually_nhds_iff.mp (ho.and hn)
  exact ⟨δ,hδ,fun y hy => h (Metric.mem_ball.mp hy)⟩
#print axioms solution
