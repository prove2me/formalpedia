-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_source_killed_density_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:43:37.506069+00:00
-- url     : https://prove2.me/submissions/928e5e69-1cf0-4d88-9e36-4d2647263c1b


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q → ∀ x : ℝ,
      Measurable (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y)) := by
  intro ψ W hW q hq x
  classical
  have hc := (hW q hq).2.2.2.1
  have hz := (hW q hq).2.1
  have hm : Measurable ((Ici (0 : ℝ)).piecewise (W q) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const measurableSet_Ici
  have he : (Ici (0 : ℝ)).piecewise (W q) (fun _ => 0) = W q := by
    funext z
    by_cases h : 0 ≤ z
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h, hz z (lt_of_not_ge h)]
  rw [he] at hm
  unfold killedHalflineDensity
  have hsub : Measurable (fun y : ℝ => W q (x-y)) :=
    hm.comp (measurable_const.sub measurable_id)
  have hexp : Measurable (fun y : ℝ => Real.exp (-(Phi ψ q)*y)) := by fun_prop
  exact ((hexp.mul measurable_const).sub hsub).ennreal_ofReal
