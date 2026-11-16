-- Prove2me | solution 1 for Kyprianou.Ch01.gammaLevyMeasure_infiniteMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:18:27.31323+00:00
-- url     : https://prove2.me/submissions/6510efe3-8004-4195-99ce-b6dc7a135360

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem gammaLevyMeasure_infiniteMass_aux
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    gammaLevyMeasure alpha beta Set.univ = ⊤ := by
  by_contra hmass
  have hdef : gammaLevyMeasure alpha beta Set.univ =
      ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (beta * Real.exp (-alpha * x) / x) := by
    simp [gammaLevyMeasure, withDensity_apply]
  have hfin : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (beta * Real.exp (-alpha * x) / x)) ≠ ⊤ := by
    rw [← hdef]
    exact hmass
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => beta * Real.exp (-alpha * x) / x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hm : Measurable (fun x : ℝ => beta * Real.exp (-alpha * x) / x) := by
      measurability
    exact hm.aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => beta * Real.exp (-alpha * x) / x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (mul_nonneg hb.le (Real.exp_pos _).le) hx.le
  have hF : IntegrableOn
      (fun x : ℝ => beta * Real.exp (-alpha * x) / x)
      (Ioi (0 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1 hfin
  have hFsmall : IntegrableOn
      (fun x : ℝ => beta * Real.exp (-alpha * x) / x)
      (Ioo (0 : ℝ) 1) :=
    hF.mono Ioo_subset_Ioi_self le_rfl
  let c : ℝ := beta * Real.exp (-alpha)
  have hc : 0 < c := mul_pos hb (Real.exp_pos _)
  have hD : IntegrableOn
      (fun x : ℝ => c⁻¹ * (beta * Real.exp (-alpha * x) / x))
      (Ioo (0 : ℝ) 1) := hFsmall.const_mul _
  have hInv : IntegrableOn
      (fun x : ℝ => x⁻¹) (Ioo (0 : ℝ) 1) := by
    apply Integrable.mono' hD (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := hx.1
    have hboundExp : Real.exp (-alpha) ≤ Real.exp (-alpha * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha, hx.2.le]
    have hboundFactor : c ≤ beta * Real.exp (-alpha * x) :=
      mul_le_mul_of_nonneg_left hboundExp hb.le
    have hposFactor : 0 ≤ beta * Real.exp (-alpha * x) / x :=
      div_nonneg (le_of_lt (mul_pos hb (Real.exp_pos _))) hxpos.le
    have hposC : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    have hh := mul_le_mul_of_nonneg_left hboundFactor hposC
    have hinv : (1 : ℝ) / x ≤ c⁻¹ * (beta * Real.exp (-alpha * x) / x) := by
      have hinvC : c⁻¹ * c = 1 := inv_mul_cancel₀ hc.ne'
      have hbase : (1 : ℝ) ≤ c⁻¹ * (beta * Real.exp (-alpha * x)) := by
        nlinarith [hh, hinvC]
      calc
        (1 : ℝ) / x ≤ (c⁻¹ * (beta * Real.exp (-alpha * x))) / x :=
          (div_le_div_iff_of_pos_right hxpos).2 hbase
        _ = c⁻¹ * (beta * Real.exp (-alpha * x) / x) := by ring
    simpa [Real.norm_eq_abs, abs_of_pos hxpos,
      abs_of_nonneg (mul_nonneg hposC hposFactor),
      one_div] using hinv
  have hpow : IntegrableOn
      (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) := by
    simpa only [Real.rpow_neg_one] using hInv
  have hnecessary := (intervalIntegral.integrableOn_Ioo_rpow_iff (zero_lt_one : (0 : ℝ) < 1)).1 hpow
  norm_num at hnecessary


theorem solution
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    gammaLevyMeasure alpha beta Set.univ = ⊤ := by
  exact gammaLevyMeasure_infiniteMass_aux alpha beta ha hb
