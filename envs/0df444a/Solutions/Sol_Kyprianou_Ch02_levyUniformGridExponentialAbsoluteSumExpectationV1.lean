-- Prove2me | solution 1 for Kyprianou.Ch02.levyUniformGridExponentialAbsoluteSumExpectationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:18.289025+00:00
-- url     : https://prove2.me/submissions/cf58bd80-fc74-4c66-9863-6f88dc2c47b3

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Function Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    ∀ n : ℕ,
      (∫ ω, Real.exp (-(∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
           X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|)) ∂P) =
        (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1) := by
  intro n
  let h : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹
  let t : Fin (n + 1 + 1) → ℝ≥0 := fun i => (i.val : ℝ≥0) * h
  have ht : Monotone t := by
    intro i k hik
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hik) (by positivity)
  let D (i : Fin (n + 1)) : Ω → ℝ := increment X (t i.castSucc) (t i.succ)
  have hind : iIndepFun D P := hX.indep_increments (n + 1) t ht
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hD (i : Fin (n + 1)) : AEMeasurable (D i) P :=
    (hcoord (t i.succ)).sub (hcoord (t i.castSucc))
  let f : ℝ → ℝ := fun x => Real.exp (-|x|)
  have hf : Measurable f := (Real.continuous_exp.comp continuous_abs.neg).measurable
  have hprod := hind.integral_prod_comp hD (fun i =>
    (hf.aemeasurable : AEMeasurable f (P.map (D i))).aestronglyMeasurable)
  have hstat (i : Fin (n + 1)) :
      IdentDistrib (D i) (X h) P P := by
    have hh : t i.succ = t i.castSucc + h := by
      simp [t, Nat.cast_add, add_mul]
    have heq : increment X 0 h = X h := by
      funext ω
      simp [increment, hX.start_zero]
    change IdentDistrib (increment X (t i.castSucc) (t i.succ)) (X h) P P
    rw [hh, ← heq]
    exact hX.stationary_increments _ _
  have hfactor (i : Fin (n + 1)) :
      (∫ ω, f (D i ω) ∂P) = ∫ ω, f (X h ω) ∂P :=
    ((hstat i).comp hf).integral_eq
  change (∫ ω, Real.exp (-(∑ i : Fin (n + 1), |D i ω|)) ∂P) =
    (∫ ω, f (X h ω) ∂P) ^ (n + 1)
  simp only [← Finset.sum_neg_distrib, Real.exp_sum]
  change (∫ ω, ∏ i : Fin (n + 1), f (D i ω) ∂P) = _
  rw [show (∫ ω, ∏ i : Fin (n + 1), f (D i ω) ∂P) =
      ∏ i : Fin (n + 1), ∫ ω, f (D i ω) ∂P by simpa [Function.comp_def] using hprod]
  simp [hfactor]
