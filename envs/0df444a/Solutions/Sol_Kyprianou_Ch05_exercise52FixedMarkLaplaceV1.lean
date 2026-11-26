-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52FixedMarkLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:43:41.713967+00:00
-- url     : https://prove2.me/submissions/0390f821-63de-4ea9-b9f9-ab57faed9a47

import Mathlib
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
/-- Independent identically distributed marks have a factorised finite-sum Laplace moment. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) (k : ℕ) (theta : ℝ) :
    (∫ w, Real.exp (theta * ∑ i ∈ Finset.range k, marks i w) ∂Q) =
      (∫ z, Real.exp (theta*z) ∂F)^k := by
  have hindY : iIndepFun marks Q :=
    iIndepFun.precomp (g := (Sum.inr : ℕ → ℕ ⊕ ℕ)) Sum.inr_injective hd.indep
  have hfin : iIndepFun (fun i : Fin k => marks i.val) Q :=
    hindY.precomp (g := fun i : Fin k => i.val) Fin.val_injective
  have hindE : iIndepFun (fun i : Fin k => fun w => Real.exp (theta * marks i.val w)) Q :=
    hfin.comp (fun _ (x : ℝ) => Real.exp (theta*x))
      (fun _ => Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hmeas : ∀ i : Fin k,
      AEStronglyMeasurable (fun w => Real.exp (theta * marks i.val w)) Q :=
    fun i => (Real.measurable_exp.comp
      (measurable_const.mul (hd.measurable_mark i.val))).aestronglyMeasurable
  have hp := hindE.integral_fun_prod_eq_prod_integral hmeas
  have he (w : Lambda) : Real.exp (theta * ∑ i ∈ Finset.range k, marks i w) =
      ∏ i : Fin k, Real.exp (theta * marks i.val w) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_range (fun i : ℕ => Real.exp (theta * marks i w))
  rw [funext he,hp]
  have hmark (i : Fin k) : (∫ w, Real.exp (theta * marks i.val w) ∂Q) =
      ∫ z, Real.exp (theta*z) ∂F := by
    rw [← (hd.law_mark i.val).map_eq]
    symm
    exact integral_map (hd.measurable_mark i.val).aemeasurable
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  simp_rw [hmark]
  simp
