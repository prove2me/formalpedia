-- Prove2me | solution 1 for Kyprianou.Ch02.levyPhysicalSmallJumpCampbellBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:12:41.43465+00:00
-- url     : https://prove2.me/submissions/be31061d-5dbe-41ec-8261-dab6129c1578

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpMassAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpMassCampbellIntensityV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Original-process physical small-jump Campbell bound separated into
    actual-jump mass measurability and its source Levy-measure intensity. -/
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    ∀ n : ℕ,
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
           ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
          (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure) := by
  intro n
  constructor
  · exact Kyprianou.Ch02.levyPhysicalSmallJumpMassAEMeasurableV1
      a σ levyMeasure hlevyMeasure P X hX hchar n
  · exact Kyprianou.Ch02.levyPhysicalSmallJumpMassCampbellIntensityV1
      a σ levyMeasure hlevyMeasure P X hX hchar n
