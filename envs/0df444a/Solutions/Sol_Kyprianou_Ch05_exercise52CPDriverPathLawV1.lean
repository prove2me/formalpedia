-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPDriverPathLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:50:39.305845+00:00
-- url     : https://prove2.me/submissions/426f2556-e190-4226-aa91-ab530d8a71ca

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverLevyVersionV1
import Theorems.Thm_Kyprianou_Ch05_exercise52NonnegativeLaplaceMarginalEqV1
import Theorems.Thm_Kyprianou_Ch05_exercise52DriverLaplaceV1
import Theorems.Thm_Kyprianou_Ch05_exercise52PositiveDriverMarksAEV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
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
/-- Match nonnegative marginal Laplace laws, then use the existing Levy whole-path uniqueness result. -/
theorem solution
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P] (Q : Measure Lambda)
    [IsProbabilityMeasure Q]
    (X : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F))) :
    P.map (fun w t => X t w) =
      Q.map (fun w (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) := by
  obtain ⟨Z,hZ,hm,he⟩ := exercise52CPDriverLevyVersionV1 Q arrival marks F hd
  have hXm (t : NNReal) : AEMeasurable (X t) P :=
    (measurable_pi_apply t).comp_aemeasurable
      (Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX.1.1)
  have hLaw (t : NNReal) : P.map (X t) = Q.map (Z t) := by
    apply exercise52NonnegativeLaplaceMarginalEqV1 P Q (X t) (Z t) (hXm t) (hm t).aemeasurable
    · filter_upwards [hX.1.2] with w hw
      simpa only [hX.1.1.start_zero,Pi.zero_apply] using hw (show 0 ≤ t from bot_le)
    · filter_upwards [he,exercise52PositiveDriverMarksAEV1 Q arrival marks F hPos hd] with w hw hp
      rw [hw t]
      simpa [ProbabilityTheory.compoundPoisson,ProbabilityTheory.piecewisePath] using
        (Finset.sum_nonneg fun i (_ : i ∈ Finset.range (ProbabilityTheory.jumpCount
          (fun n => ProbabilityTheory.arrival arrival n w) (t : ℝ))) => (hp i).le)
    · intro theta ht
      rw [hCP t theta ht.le, ← exercise52DriverLaplaceV1 Q arrival marks F hd hPos t theta ht.le]
      apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [hw t]
  rw [Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1 P Q X Z hX.1.1 hZ hLaw]
  apply Measure.map_congr
  filter_upwards [he] with w hw
  funext t
  exact hw t
