-- Prove2me | solution 1 for NemytskiiLebesgue.pow_transfer_ennreal_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:46.970072+00:00
-- url     : https://prove2.me/submissions/f25ff40e-0f20-49df-b9a5-90b0e7866c54

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {a : ℝ} (ha : 0 ≤ a)
    {b : ℝ} (hb : 0 ≤ b)
    {c : ℝ} (hc : 0 < c)
    {d : ℝ} (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r)
    (hcarb : c * a ^ r < b) :
    ↱a ^ (d * r) ≤ ↱(c ^ (-d)) * ↱b ^ d := by
  have har : 0 ≤ a ^ r :=
    Real.rpow_nonneg ha r
  have hcd : 0 ≤ c ^ (-d) :=
    (Real.rpow_pos_of_pos hc (-d)).le
  have hadr : a ^ (d * r) ≤ c ^ (-d) * b ^ d := by
    rw [mul_comm,
        Real.rpow_mul ha,
        Real.rpow_neg hc.le,
        ←div_eq_inv_mul,
        le_div_iff₀ (Real.rpow_pos_of_pos hc d),
        ←Real.mul_rpow har hc.le]
    rw [←mul_nonneg_iff_of_pos_right hc] at har
    exact Real.rpow_le_rpow har ((mul_comm c (a ^ r) ▸ hcarb).le) hd.le
  convert ENNReal.ofReal_le_ofReal hadr using 1
  · apply ENNReal.ofReal_rpow_of_nonneg ha
    nlinarith
  · convert ENNReal.ofReal_mul hcd using 2
    rotate_left
    · exact ENNReal.ofReal_mul hcd
    · norm_num [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
        ENNReal.ofReal_rpow_of_nonneg hb hd.le]
end NemytskiiLebesgue
