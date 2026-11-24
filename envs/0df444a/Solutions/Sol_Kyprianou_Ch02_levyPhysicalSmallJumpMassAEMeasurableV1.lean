-- Prove2me | solution 1 for Kyprianou.Ch02.levyPhysicalSmallJumpMassAEMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:19:34.153498+00:00
-- url     : https://prove2.me/submissions/876db4ab-1889-42c0-9e8a-d9450e46f245

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_cadlagSmallJumpMassBorelFunctionalV1
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer a measurable weighted jump-mass functional of cadlag paths
    through the a.e. measurable original Levy whole-path map. -/
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
           else 0)) P := by
  intro n
  obtain ⟨F, hF, hrep⟩ :=
    Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1 (n : ℝ≥0)
  have hwhole :=
    Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  have hmeas :
      AEMeasurable (fun ω : Ω => F (fun t : ℝ≥0 => X t ω)) P :=
    hF.comp_aemeasurable hwhole
  refine hmeas.congr ?_
  filter_upwards [hX.cadlag_ae] with ω hω
  exact hrep (fun t : ℝ≥0 => X t ω)
    (fun t => (hω t).1)
    (fun t _ => (hω t).2)
