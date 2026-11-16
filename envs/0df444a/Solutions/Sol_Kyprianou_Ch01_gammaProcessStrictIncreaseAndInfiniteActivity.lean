-- Prove2me | solution 1 for Kyprianou.Ch01.gammaProcessStrictIncreaseAndInfiniteActivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:47:22.545939+00:00
-- url     : https://prove2.me/submissions/5fa2e771-6137-4efd-a148-1f8787bcf67c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_gammaStrictMonoFromLaplace
import Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_isLevyMeasure
import Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_infiniteMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The gamma Lévy intensity is supported on positive jump magnitudes. -/
private theorem gamma_levy_negative_null
    (alpha beta : ℝ) :
    Kyprianou.Ch01.gammaLevyMeasure alpha beta (Set.Iic (0 : ℝ)) = 0 := by
  have hr : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic]
    have heq : Set.Iic (0 : ℝ) ∩ Set.Ioi (0 : ℝ) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => not_lt_of_ge h.1 h.2
    rw [heq]
    exact measure_empty
  exact (withDensity_absolutelyContinuous _ _) hr

/-- The total mass of the gamma Lévy measure occurs on positive jumps. -/
private theorem gamma_levy_positive_mass_top
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    Kyprianou.Ch01.gammaLevyMeasure alpha beta (Set.Ioi (0 : ℝ)) = ⊤ := by
  have hnull := gamma_levy_negative_null alpha beta
  have hsum := measure_add_measure_compl
    (μ := Kyprianou.Ch01.gammaLevyMeasure alpha beta)
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  rw [Set.compl_Ioi, hnull, add_zero] at hsum
  rw [hsum, Kyprianou.Ch01.gammaLevyMeasure_infiniteMass alpha beta ha hb]

/-- Decompose gamma-process strict increase and infinite activity into
    its distributional path argument and previously proved measure facts. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (hAlpha : 0 < alpha) (hBeta : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hGammaLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    (∀ᵐ ω ∂P, StrictMono (fun t : ℝ≥0 => X t ω)) ∧
      IsLevyMeasure (Kyprianou.Ch01.gammaLevyMeasure alpha beta) ∧
      (Kyprianou.Ch01.gammaLevyMeasure alpha beta)
        (Set.Ioi (0 : ℝ)) = (⊤ : ℝ≥0∞) := by
  exact ⟨Kyprianou.Ch01.gammaStrictMonoFromLaplace P X alpha beta
      hAlpha hBeta hX hGammaLaplace,
    Kyprianou.Ch01.gammaLevyMeasure_isLevyMeasure alpha beta hAlpha hBeta,
    gamma_levy_positive_mass_top alpha beta hAlpha hBeta⟩
