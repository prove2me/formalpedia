-- Prove2me | solution 1 for Kyprianou.Ch02.levyPoissonPathFiniteVariationResidualV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:58:43.114407+00:00
-- url     : https://prove2.me/submissions/def7ef8b-bbb1-411c-afbc-a57ddca35e4c

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_levyPoissonPathLocallySummableTimeRepresentationV1
import Theorems.Thm_Kyprianou_Ch02_locallySummableTimeRepresentationActualJumpsV2
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the actual jumps of the time-grouped canonical series. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |levyJumpPath hd hν b s ω -
          leftLim (fun u : ℝ≥0 => levyJumpPath hd hν b u ω) s|) ∧
      levyJumpPath hd hν b T ω =
        (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) * (T : ℝ) +
        ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (levyJumpPath hd hν b s ω -
            leftLim (fun u : ℝ≥0 => levyJumpPath hd hν b u ω) s) := by
  filter_upwards [Kyprianou.Ch02.levyPoissonPathLocallySummableTimeRepresentationV1
    P ν K Z hd hν b hfin] with ω hω
  obtain ⟨g, hs, heq⟩ := hω
  have hj := Kyprianou.Ch02.locallySummableTimeRepresentationActualJumpsV2
    (fun t => levyJumpPath hd hν b t ω) g
    (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) hs heq
  intro T
  have hterm (s : Set.Ioc (0 : ℝ≥0) T) :
      levyJumpPath hd hν b s ω -
        leftLim (fun u : ℝ≥0 => levyJumpPath hd hν b u ω) s = g s :=
    hj s s.property.1
  constructor
  · exact (hs T).congr (fun s => by rw [hterm s])
  · rw [heq T]
    congr 1
    exact tsum_congr (fun s => (hterm s).symm)
