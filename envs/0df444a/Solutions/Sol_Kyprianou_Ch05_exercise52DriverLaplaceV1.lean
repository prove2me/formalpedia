-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52DriverLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:52:31.715311+00:00
-- url     : https://prove2.me/submissions/7aa41b74-614b-4a36-8c46-f098a96950ed

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52CountMarkIndepV2
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_Kyprianou_Ch05_exercise52PositiveDriverMarksAEV1
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences
import Theorems.Thm_AvramDividend_Classical_chat06_laplace_random_mark_sum_without_pgf_assumption
import Theorems.Thm_Kyprianou_Ch05_exercise52FixedMarkLaplaceV1
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
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
/-- The driftless positive compound Poisson driver has the comparison Laplace transform. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hPos : F (Iic 0) = 0) (t : NNReal) (theta : ℝ) (hTheta : 0 ≤ theta) :
    (∫ w, Real.exp (-theta * ProbabilityTheory.compoundPoisson 0 arrival marks
        (t : ℝ) w) ∂Q) =
      Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)) := by
  let N := fun w => LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival arrival n w) (t : ℝ)
  have hN := exercise52CountMarkIndepV2 Q arrival marks F hd t
  have hLaw : HasLaw N (poissonMeasure (1*t)) Q :=
    ⟨hN.1.aemeasurable, levy_foundations_compoundPoissonJumpCountLaw hd one_pos t⟩
  have hPosAE := exercise52PositiveDriverMarksAEV1 Q arrival marks F hPos hd
  have hm : Measurable (fun w : Lambda =>
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) :=
    (Kyprianou.Ch01.compoundPoissonOfMeasurableSequences arrival marks
      hd.measurable_interarrival hd.measurable_mark).comp (measurable_id.prodMk measurable_const)
  have hsum (w : Lambda) : ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w =
      ∑ j ∈ Finset.range (N w), marks j w := by
    simp [N,ProbabilityTheory.compoundPoisson,ProbabilityTheory.piecewisePath]
    rfl
  have hInt : Integrable (fun w => Real.exp (-theta * ∑ j ∈ Finset.range (N w), marks j w)) Q := by
    simp_rw [← hsum]
    apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hm)).aestronglyMeasurable 1
    filter_upwards [hPosAE] with w hw
    change ‖Real.exp (-theta * ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le,hsum]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hTheta)
      (Finset.sum_nonneg fun i _ => (hw i).le))
  have h := AvramDividend.Classical.chat06_laplace_random_mark_sum_without_pgf_assumption
    Q N marks hN.1 hd.measurable_mark hN.2 (1*t) hLaw (-theta)
    (∫ z, Real.exp (-theta*z) ∂F) hInt
    (fun k => exercise52FixedMarkLaplaceV1 Q arrival marks F hd k (-theta))
  simp_rw [← hsum] at h
  rw [h]
  have hAE : ∀ᵐ z ∂F, z ∈ Ioi (0 : ℝ) := by
    rw [ae_iff]
    simp only [mem_Ioi,not_lt]
    exact hPos
  have hRestrict := Measure.restrict_eq_self_of_ae_mem hAE
  rw [hRestrict]
  have hE : Integrable (fun z : ℝ => Real.exp (-theta*z)) F := by
    apply Integrable.of_bound (Real.measurable_exp.comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable 1
    filter_upwards [hAE] with z hz
    change ‖Real.exp (-theta*z)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hTheta) hz.le)
  rw [integral_sub (integrable_const 1) hE]
  simp only [integral_const,one_smul,one_mul,Measure.real,measure_univ,ENNReal.toReal_one]
  congr 1
  ring
