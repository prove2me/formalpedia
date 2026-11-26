-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52NonnegativeLaplaceMarginalEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:52:29.172097+00:00
-- url     : https://prove2.me/submissions/69effb92-6835-4ce2-b21e-654053f3c743

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_measureEqOfFinitePositiveLaplace
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
/-- Nonnegative random variables with matching real Laplace moments have identical pushforward laws. -/
theorem solution
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (A : Omega → ℝ) (B : Lambda → ℝ)
    (ha : AEMeasurable A P) (hb : AEMeasurable B Q)
    (hpa : ∀ᵐ w ∂P, 0 ≤ A w) (hpb : ∀ᵐ w ∂Q, 0 ≤ B w)
    (hEq : ∀ theta : ℝ, 0 < theta →
      (∫ w, Real.exp (-theta*A w) ∂P) = (∫ w, Real.exp (-theta*B w) ∂Q)) :
    P.map A = Q.map B := by
  apply measureEqOfFinitePositiveLaplace
  · intro theta ht
    have hg : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-theta*z))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
    rw [lintegral_map' hg.aemeasurable ha]
    calc
      _ ≤ ∫⁻ _ : Omega, (1 : ENNReal) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hpa] with w hw
        exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
      _ < ⊤ := by simp
  · intro theta ht
    let g : ℝ → ℝ := fun z => Real.exp (-theta*z)
    have hg : Measurable g := Real.measurable_exp.comp (measurable_const.mul measurable_id)
    have hiA : Integrable (g ∘ A) P := by
      apply Integrable.of_bound (hg.comp_aemeasurable ha).aestronglyMeasurable 1
      filter_upwards [hpa] with w hw
      change ‖Real.exp (-theta*A w)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by change -theta*A w ≤ 0; nlinarith)
    have hiB : Integrable (g ∘ B) Q := by
      apply Integrable.of_bound (hg.comp_aemeasurable hb).aestronglyMeasurable 1
      filter_upwards [hpb] with w hw
      change ‖Real.exp (-theta*B w)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by change -theta*B w ≤ 0; nlinarith)
    have hge : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-theta*z))) :=
      ENNReal.measurable_ofReal.comp hg
    rw [lintegral_map' hge.aemeasurable ha, lintegral_map' hge.aemeasurable hb]
    change (∫⁻ w, ENNReal.ofReal (Real.exp (-theta*A w)) ∂P) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (-theta*B w)) ∂Q
    change Integrable (fun w => Real.exp (-theta*A w)) P at hiA
    change Integrable (fun w => Real.exp (-theta*B w)) Q at hiB
    rw [← ofReal_integral_eq_lintegral_ofReal hiA (Eventually.of_forall fun w => (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal hiB (Eventually.of_forall fun w => (Real.exp_pos _).le)]
    exact congrArg ENNReal.ofReal (hEq theta ht)
