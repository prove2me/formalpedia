-- Prove2me | solution 1 for NarrowDNF.WidthBound.width_le_exponential
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:50.321524+00:00
-- url     : https://prove2.me/submissions/45229066-6f11-41b3-8891-e5948364b235

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_WidthBound
import Theorems.Thm_NarrowDNF_WidthBound_ceil_width_le_exp

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound


noncomputable section
open NarrowDNF
open NarrowDNF.WidthBound
/-- The source's explicit width is bounded by one absolute exponential. -/
theorem solution {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε < 1) :
    (width K ε : ℝ) ≤ Real.exp (absoluteConstant * (K + 1)^2 / ε^2) := by
  let R : ℝ := (K + 1) / ε
  let c : ℝ := influenceCeil K
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hc : c ≤ K + 1 := (Nat.ceil_lt_add_one hK.le).le
  have hR : 1 ≤ R := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hR_sq : R ≤ R^2 := by nlinarith
  have hrecip : 1 / ε ≤ R := div_le_div_of_nonneg_right (by linarith) hε.le
  have hcr : c / ε ≤ R := div_le_div_of_nonneg_right hc hε.le
  have hcr0 : 0 ≤ c / ε := div_nonneg hc0 hε.le
  have hcr_sq : (c / ε)^2 ≤ R^2 := by nlinarith
  have hdegree : (degree K ε : ℝ) ≤ 4000 * R + 1 := by
    have hd := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4000 * c / ε)).le
    have heq : 4000 * c / ε = 4000 * (c / ε) := by ring
    rw [heq] at hd
    change (Nat.ceil (4000 * c / ε) : ℝ) ≤ _
    rw [heq]
    linarith
  have hdegree_sq : (degree K ε : ℝ) ≤ 4001 * R^2 := by nlinarith
  have hload : 160000000000 * c^2 / ε^2 ≤ 160000000000 * R^2 := by
    have heq : 160000000000 * c^2 / ε^2 = 160000000000 * (c / ε)^2 := by ring
    rw [heq]
    nlinarith
  have hexponent : 4 / ε + (degree K ε : ℝ) + 160000000000 * c^2 / ε^2 ≤
      absoluteConstant * (K + 1)^2 / ε^2 := by
    have heq : absoluteConstant * (K + 1)^2 / ε^2 = absoluteConstant * R^2 := by
      dsimp [R]
      ring
    rw [heq]
    unfold absoluteConstant
    have hrecip4 : 4 / ε ≤ 4 * R^2 := by
      calc
        4 / ε = 4 * (1 / ε) := by ring
        _ ≤ 4 * R := mul_le_mul_of_nonneg_left hrecip (by norm_num)
        _ ≤ 4 * R^2 := mul_le_mul_of_nonneg_left hR_sq (by norm_num)
    nlinarith [sq_nonneg R]
  exact (ceil_width_le_exp hε (by positivity) (degree K ε)).trans
    (Real.exp_le_exp.mpr hexponent)
