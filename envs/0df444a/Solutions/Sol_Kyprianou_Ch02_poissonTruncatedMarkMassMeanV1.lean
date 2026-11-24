-- Prove2me | solution 1 for Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:05:21.485158+00:00
-- url     : https://prove2.me/submissions/cbac91e0-546b-4bde-b6fb-f80b90a50510

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (n : ℕ) :
    (∫⁻ ω, ∫⁻ p : ℝ × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
      else 0 ∂(poissonRandomMeasure K Z ω) ∂P) =
      (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) := by
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min (1 : ℝ) |x|)
  let g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then w p.2 else 0
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (continuous_const.min continuous_abs).measurable
  have hg : Measurable g := Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))
    (hw.comp measurable_snd) measurable_const
  change (∫⁻ ω, ∫⁻ p, g p ∂(poissonRandomMeasure K Z ω) ∂P) =
    (n : ℝ≥0∞) * (∫⁻ x, w x ∂ν)
  rw [lintegral_lintegral_poissonRandomMeasure hd hg, lintegral_prod g hg.aemeasurable]
  have heq : (fun x : ℝ => ∫⁻ y : ℝ, g (x,y) ∂ν) =
      (Set.Ioc 0 (n : ℝ)).indicator (fun _ => ∫⁻ y, w y ∂ν) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) (n : ℝ)
    · simp [g, hx, Set.mem_Ioc.mp hx]
    · have h : ¬ (0 < x ∧ x ≤ (n : ℝ)) := hx
      simp [g, hx, h]
  rw [heq, lintegral_indicator measurableSet_Ioc, lintegral_const]
  simp [Measure.restrict_apply_univ, Real.volume_Ioc, mul_comm]
