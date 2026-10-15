-- Prove2me | solution 1 for MultiItemRev.TwoIID.expectation_W_step
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-15T10:09:51.866557+00:00
-- url     : https://prove2.me/submissions/ef6cc1cb-b543-4db6-bc02-de1df8aec53a

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (p : ℝ≥0) :
    let μ := Measure.pi (fun _ : Fin 2 => ν)
    (∫⁻ x, ENNReal.ofReal
      (((min (x 0) (x 1) : ℝ≥0) : ℝ) * (if p ≤ x 0 then 1 else 0) -
        max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0) ∂μ) =
      ν {t | p ≤ t} * ∫⁻ t, ((min t p : ℝ≥0) : ℝ≥0∞) ∂ν := by
  classical
  show (∫⁻ x, ENNReal.ofReal
      (((min (x 0) (x 1) : ℝ≥0) : ℝ) * (if p ≤ x 0 then 1 else 0) -
        max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0) ∂Measure.pi (fun _ : Fin 2 => ν)) =
      ν {t | p ≤ t} * ∫⁻ t, ((min t p : ℝ≥0) : ℝ≥0∞) ∂ν
  -- Pointwise: the integrand is the threshold indicator times min(Z, p).
  -- Stated in if-form: `rw` on `Set.indicator` terms failed to match
  -- visibly-present patterns in the gate run, so indicator lemmas are
  -- used only via `exact` below (hconv).
  have hpoint : ∀ x : Fin 2 → ℝ≥0,
      ENNReal.ofReal
      (((min (x 0) (x 1) : ℝ≥0) : ℝ) * (if p ≤ x 0 then 1 else 0) -
        max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0) =
        (if p ≤ x 0 then (1 : ℝ≥0∞) else 0) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞) := by
    intro x
    by_cases hx : p ≤ x 0
    · simp only [if_pos hx]
      have hmin : min (min (x 0) (x 1)) p = min (x 1) p := by
        rw [min_assoc, min_eq_right (le_trans (min_le_right _ _) hx)]
      have hreal : ((min (x 0) (x 1) : ℝ≥0) : ℝ) * 1 -
            max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0 =
          ((min (x 1) p : ℝ≥0) : ℝ) := by
        have hsub : ((min (x 0) (x 1) : ℝ≥0) : ℝ) -
              max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0 =
            min ((min (x 0) (x 1) : ℝ≥0) : ℝ) (p : ℝ) := by
          rcases le_total ((min (x 0) (x 1) : ℝ≥0) : ℝ) (p : ℝ) with hab | hab
          · rw [min_eq_left hab, max_eq_right (sub_nonpos.mpr hab), sub_zero]
          · rw [min_eq_right hab, max_eq_left (sub_nonneg.mpr hab), sub_sub_cancel]
        rw [mul_one, hsub, ← NNReal.coe_min, hmin]
      rw [one_mul, hreal, ENNReal.ofReal_coe_nnreal]
    · simp only [if_neg hx]
      have hlt : ((min (x 0) (x 1) : ℝ≥0) : ℝ) < (p : ℝ) := by
        have hle : ((min (x 0) (x 1) : ℝ≥0) : ℝ) ≤ ((x 0 : ℝ≥0) : ℝ) := by
          exact_mod_cast min_le_left (x 0) (x 1)
        have hlt2 : ((x 0 : ℝ≥0) : ℝ) < (p : ℝ) := by
          exact_mod_cast lt_of_not_ge hx
        linarith
      have hmax : max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr hlt.le)
      rw [zero_mul, mul_zero, zero_sub, hmax, neg_zero, ENNReal.ofReal_zero]
  -- if-form = indicator-form, pointwise (indicator lemmas via `exact` only).
  have hconv : ∀ x : Fin 2 → ℝ≥0,
      (if p ≤ x 0 then (1 : ℝ≥0∞) else 0) = ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) (x 0)) := by
    intro x
    by_cases hx : p ≤ x 0
    · rw [if_pos hx]
      exact (Set.indicator_of_mem (show x 0 ∈ {t | p ≤ t} from hx)
        (1 : ℝ≥0 → ℝ≥0∞)).symm
    · rw [if_neg hx]
      exact (Set.indicator_of_notMem (show x 0 ∉ {t | p ≤ t} from hx)
        (1 : ℝ≥0 → ℝ≥0∞)).symm
  have hconv2 : ∀ x : Fin 2 → ℝ≥0,
      (if p ≤ x 0 then (1 : ℝ≥0∞) else 0) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞)
        = ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) (x 0)) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞) := by
    intro x
    rw [hconv x]
  have hA : MeasurableSet {t : ℝ≥0 | p ≤ t} := measurableSet_Ici
  have hFmeas : Measurable (fun z : ℝ≥0 × ℝ≥0 =>
      ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) z.1) * ((min z.2 p : ℝ≥0) : ℝ≥0∞)) := by
    apply Measurable.mul
    · exact (measurable_one.indicator hA).comp measurable_fst
    · exact ((measurable_id.min measurable_const).coe_nnreal_ennreal).comp
        measurable_snd
  have h1ae : AEMeasurable ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞)) ν :=
    (measurable_one.indicator hA).aemeasurable
  have h2ae : AEMeasurable (fun t : ℝ≥0 => ((min t p : ℝ≥0) : ℝ≥0∞)) ν :=
    ((measurable_id.min measurable_const).coe_nnreal_ennreal).aemeasurable
  have hcomp : (∫⁻ x, ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) (x 0)) *
        ((min (x 1) p : ℝ≥0) : ℝ≥0∞) ∂Measure.pi (fun _ : Fin 2 => ν)) =
      ∫⁻ z, ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) z.1) * ((min z.2 p : ℝ≥0) : ℝ≥0∞)
        ∂(ν.prod ν) := by
    have hMP : MeasurePreserving MeasurableEquiv.finTwoArrow
        (Measure.pi (fun _ : Fin 2 => ν)) (ν.prod ν) :=
      MeasureTheory.measurePreserving_finTwoArrow ν
    have h := hMP.lintegral_comp hFmeas
    rw [← h]
    apply MeasureTheory.lintegral_congr
    intro x
    rfl
  have hInt0 : (∫⁻ x, ENNReal.ofReal
      (((min (x 0) (x 1) : ℝ≥0) : ℝ) * (if p ≤ x 0 then 1 else 0) -
        max ((((min (x 0) (x 1) : ℝ≥0) : ℝ) - (p : ℝ))) 0) ∂Measure.pi (fun _ : Fin 2 => ν)) =
      ∫⁻ x, (if p ≤ x 0 then (1 : ℝ≥0∞) else 0) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin 2 => ν) :=
    MeasureTheory.lintegral_congr hpoint
  have hInt : (∫⁻ x, (if p ≤ x 0 then (1 : ℝ≥0∞) else 0) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin 2 => ν)) =
      ∫⁻ x, ({t | p ≤ t}.indicator (1 : ℝ≥0 → ℝ≥0∞) (x 0)) * ((min (x 1) p : ℝ≥0) : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin 2 => ν) :=
    MeasureTheory.lintegral_congr hconv2
  rw [hInt0, hInt, hcomp, MeasureTheory.lintegral_prod_mul h1ae h2ae,
    MeasureTheory.lintegral_indicator_one hA]
