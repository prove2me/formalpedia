-- Prove2me | solution 1 for KerrBL.reg_eventually_Kerr
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T09:41:06.568694+00:00
-- url     : https://prove2.me/submissions/c731c2ac-7649-463e-9e5a-04ee9edbe854

import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Constructions
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open KerrBL Filter Topology

/- The regular domain is open: regularity at x persists near x. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) : ∀ᶠ y in 𝓝 x, RegKerr M a y := by
  obtain ⟨hS, hD, hs⟩ := hx
  have e_hS : ∀ᶠ y in 𝓝 x, Sig a (y 1) (Real.cos (y 2)) ≠ 0 :=
    (show ContinuousAt (fun y : Pt => Sig a (y 1) (Real.cos (y 2))) x by unfold Sig; apply Continuous.continuousAt; fun_prop).eventually_ne hS
  have e_hD : ∀ᶠ y in 𝓝 x, Del M a (y 1) ≠ 0 :=
    (show ContinuousAt (fun y : Pt => Del M a (y 1)) x by unfold Del; apply Continuous.continuousAt; fun_prop).eventually_ne hD
  have e_hs : ∀ᶠ y in 𝓝 x, Real.sin (y 2) ≠ 0 :=
    (show ContinuousAt (fun y : Pt => Real.sin (y 2)) x by apply Continuous.continuousAt; fun_prop).eventually_ne hs
  unfold RegKerr
  filter_upwards [e_hS, e_hD, e_hs] with y he_hS he_hD he_hs
  exact ⟨he_hS, he_hD, he_hs⟩
