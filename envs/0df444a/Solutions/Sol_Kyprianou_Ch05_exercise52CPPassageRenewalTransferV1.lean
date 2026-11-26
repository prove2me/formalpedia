-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPPassageRenewalTransferV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:22:14.665029+00:00
-- url     : https://prove2.me/submissions/21451204-292d-409f-a73c-6f148f5a5493
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_exercise52SubordinatorGapEventAEV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverPathLawV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CPRenewalGapEventAEV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Transfer the countable measurable gap event through equality of whole-path laws. -/
theorem solution
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P] (Q : Measure Lambda)
    [IsProbabilityMeasure Q]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)))
    (hLeft : IsLeftLimitVersion P X Xleft) :
    ∀ x u y : ℝ, 0 < x → 0 < u → 0 < y →
      P {omega : Omega | PassageFinite X deathX x omega ∧
        passageOvershoot X deathX x omega ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x omega ∈ Ioi y} =
      Q {w : Lambda | u < renewalOvershoot marks x w ∧
        y < renewalUndershoot marks x w} := by
  intro x u y hx hu hy
  let B : Set (NNReal → ℝ) := {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)}
  have hB : MeasurableSet B := exercise52RationalGapMeasurableV1 x u y
  have hXae := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX.1.1
  have hQm : Measurable (fun w : Lambda => fun t : NNReal =>
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) :=
    measurable_pi_iff.mpr fun t =>
      (Kyprianou.Ch01.compoundPoissonOfMeasurableSequences arrival marks
        hd.measurable_interarrival hd.measurable_mark).comp
        (measurable_id.prodMk measurable_const)
  have hLaw := exercise52CPDriverPathLawV1 P Q X deathX arrival marks F hPos hd hX hCP
  have hP := exercise52SubordinatorGapEventAEV1 P X Xleft deathX hX hLeft x u y hx hu hy
  have hR := exercise52CPRenewalGapEventAEV1 Q arrival marks F hPos hd x u y hx hu hy
  calc
    _ = P ((fun w t => X t w) ⁻¹' B) := by
      apply measure_congr
      filter_upwards [hP] with w hw
      exact propext hw
    _ = (P.map (fun w t => X t w)) B := (Measure.map_apply_of_aemeasurable hXae hB).symm
    _ = (Q.map (fun w (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w)) B := by rw [hLaw]
    _ = Q ((fun w (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) ⁻¹' B) :=
      Measure.map_apply hQm hB
    _ = _ := by
      apply measure_congr
      filter_upwards [hR] with w hw
      exact propext hw.symm
