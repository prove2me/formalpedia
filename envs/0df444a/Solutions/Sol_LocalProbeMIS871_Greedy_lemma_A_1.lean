-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T02:58:01.729828+00:00
-- url     : https://prove2.me/submissions/78be44ca-bd17-4f3f-83e2-951f421e6bec

import Mathlib
import Definitions.Def_LocalProbeMIS871_Greedy_Coefficients

-- ===== Solutions.LPM.LA1a =====

set_option autoImplicit false

namespace LPM
open MeasureTheory Set intervalIntegral Real

theorem log_lower (b : ℝ) (hb : 0 < b) (hb4 : b ≤ 4) :
    1 / Real.log (1 + b) ≤ 1 / b + 1 / 2 - b / 48 := by
  set z := b / (b + 2) with hz
  have hz0 : 0 < z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hs := hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_pos hz0]; exact hz1)
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hle
  have e : Real.log (1 + z) - Real.log (1 - z) = Real.log (1 + b) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    rw [hz]; field_simp; ring
  rw [e] at hle
  norm_num at hle
  have hg : 0 < 2 * z + 2 * (1 / 3) * z ^ 3 := by positivity
  have hlog : 0 < Real.log (1 + b) := Real.log_pos (by linarith)
  calc 1 / Real.log (1 + b) ≤ 1 / (2 * z + 2 * (1 / 3) * z ^ 3) := by
        apply one_div_le_one_div_of_le hg; linarith
    _ ≤ 1 / b + 1 / 2 - b / 48 := by
        rw [hz]
        rw [div_le_iff₀ (by positivity)]
        have hb2 : 0 < b + 2 := by linarith
        field_simp
        nlinarith [mul_pos hb hb, mul_pos (mul_pos hb hb) hb, mul_pos hb hb2,
          mul_nonneg (mul_nonneg hb.le hb.le) (by linarith : (0:ℝ) ≤ 4 - b),
          mul_nonneg (mul_nonneg (mul_nonneg hb.le hb.le) hb.le) (by linarith : (0:ℝ) ≤ 4 - b),
          mul_nonneg hb.le (by linarith : (0:ℝ) ≤ 4 - b)]

end LPM

namespace LPM
open MeasureTheory Set intervalIntegral Real

theorem cont_pow_mul_log' (k : ℕ) : Continuous (fun x : ℝ => x ^ (k + 1) * Real.log x) := by
  have : (fun x : ℝ => x ^ (k + 1) * Real.log x) = fun x => x ^ k * (x * Real.log x) := by
    funext x; ring
  rw [this]
  exact (continuous_pow k).mul continuous_mul_log

theorem int_pow_neglog (m : ℕ) :
    ∫ z in (0 : ℝ)..1, z ^ (m + 1) * (-Real.log z) = 1 / ((m : ℝ) + 2) ^ 2 := by
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun z : ℝ => -(z ^ (m + 2) * Real.log z) / ((m : ℝ) + 2) + z ^ (m + 2) / ((m : ℝ) + 2) ^ 2)
      (x ^ (m + 1) * (-Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 := (((hasDerivAt_pow (m + 2) x).mul (Real.hasDerivAt_log hx0)).neg).div_const ((m : ℝ) + 2)
    have h2 := (hasDerivAt_pow (m + 2) x).div_const (((m : ℝ) + 2) ^ 2)
    refine (h1.add h2).congr_deriv ?_
    push_cast
    field_simp
    ring
  have hcont : ContinuousOn
      (fun z : ℝ => -(z ^ (m + 2) * Real.log z) / ((m : ℝ) + 2) + z ^ (m + 2) / ((m : ℝ) + 2) ^ 2)
      (Icc 0 1) :=
    (((cont_pow_mul_log' (m + 1)).neg.div_const _).add ((continuous_pow _).div_const _)).continuousOn
  have hint : IntervalIntegrable (fun z : ℝ => z ^ (m + 1) * (-Real.log z)) volume 0 1 := by
    have : (fun z : ℝ => z ^ (m + 1) * (-Real.log z)) = fun z => -(z ^ m * (z * Real.log z)) := by
      funext z; ring
    rw [this]
    exact ((continuous_pow m).mul continuous_mul_log).neg.intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hF hint]
  simp

theorem int_pow_log2 (m : ℕ) :
    ∫ z in (0 : ℝ)..1, z ^ (m + 2) * (Real.log z) ^ 2 = 2 / ((m : ℝ) + 3) ^ 3 := by
  have hm : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun z : ℝ => z ^ (m + 3) * (Real.log z) ^ 2 / ((m : ℝ) + 3) -
        2 * (z ^ (m + 3) * Real.log z) / ((m : ℝ) + 3) ^ 2 + 2 * z ^ (m + 3) / ((m : ℝ) + 3) ^ 3)
      (x ^ (m + 2) * (Real.log x) ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 := ((hasDerivAt_pow (m + 3) x).mul ((Real.hasDerivAt_log hx0).pow 2)).div_const
      ((m : ℝ) + 3)
    have h2 := (((hasDerivAt_pow (m + 3) x).mul (Real.hasDerivAt_log hx0)).const_mul 2).div_const
      (((m : ℝ) + 3) ^ 2)
    have h3 := ((hasDerivAt_pow (m + 3) x).const_mul 2).div_const (((m : ℝ) + 3) ^ 3)
    refine ((h1.sub h2).add h3).congr_deriv ?_
    push_cast
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hcont : ContinuousOn
      (fun z : ℝ => z ^ (m + 3) * (Real.log z) ^ 2 / ((m : ℝ) + 3) -
        2 * (z ^ (m + 3) * Real.log z) / ((m : ℝ) + 3) ^ 2 + 2 * z ^ (m + 3) / ((m : ℝ) + 3) ^ 3)
      (Icc 0 1) := by
    have e : (fun z : ℝ => z ^ (m + 3) * (Real.log z) ^ 2) =
        fun z => z ^ (m + 1) * (z * Real.log z) ^ 2 := by funext z; ring
    have c1 : Continuous (fun z : ℝ => z ^ (m + 3) * (Real.log z) ^ 2) := by
      rw [e]; exact (continuous_pow _).mul (continuous_mul_log.pow 2)
    exact (((c1.div_const _).sub (((cont_pow_mul_log' (m + 2)).const_mul 2).div_const _)).add
      (((continuous_pow _).const_mul 2).div_const _)).continuousOn
  have hint : IntervalIntegrable (fun z : ℝ => z ^ (m + 2) * (Real.log z) ^ 2) volume 0 1 := by
    have : (fun z : ℝ => z ^ (m + 2) * (Real.log z) ^ 2) = fun z => z ^ m * (z * Real.log z) ^ 2 := by
      funext z; ring
    rw [this]
    exact ((continuous_pow m).mul (continuous_mul_log.pow 2)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hF hint]
  simp

end LPM


-- ===== Solutions.LPM.LA1b =====

set_option autoImplicit false

namespace LPM
open MeasureTheory Set Real LocalProbeMIS871.Greedy

theorem rp4 (z : ℝ) : z ^ ((5 : ℝ) - 1) = z ^ 4 := by
  rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem uI_eq (z : ℝ) : uIntegrand 5 z = z ^ 4 * (-Real.log z) / Real.log (1 + 4 * z) := by
  unfold uIntegrand; rw [rp4, one_div, Real.log_inv]; norm_num

theorem wI_eq (z : ℝ) : wIntegrand 5 z = z ^ 4 * (Real.log z) ^ 2 / Real.log (1 + 4 * z) := by
  unfold wIntegrand; rw [rp4, one_div, Real.log_inv]; norm_num

theorem ioo_eq (f : ℝ → ℝ) : ∫ z in Ioo (0 : ℝ) 1, f z = ∫ z in (0 : ℝ)..1, f z := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem meas_uI : Measurable (uIntegrand 5) := by
  have : uIntegrand 5 = fun z => z ^ 4 * (-Real.log z) / Real.log (1 + 4 * z) := by
    funext z; exact uI_eq z
  rw [this]; fun_prop

theorem meas_wI : Measurable (wIntegrand 5) := by
  have : wIntegrand 5 = fun z => z ^ 4 * (Real.log z) ^ 2 / Real.log (1 + 4 * z) := by
    funext z; exact wI_eq z
  rw [this]; fun_prop

theorem bounds_pt (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    z ^ 4 * (-Real.log z) / Real.log 5 ≤ uIntegrand 5 z ∧
    uIntegrand 5 z ≤ (1/4) * (z ^ 3 * (-Real.log z)) + (1/2) * (z ^ 4 * (-Real.log z)) -
      (1/12) * (z ^ 5 * (-Real.log z)) ∧
    0 ≤ wIntegrand 5 z ∧
    wIntegrand 5 z ≤ (1/4) * (z ^ 3 * (Real.log z) ^ 2) + (1/2) * (z ^ 4 * (Real.log z) ^ 2) -
      (1/12) * (z ^ 5 * (Real.log z) ^ 2) := by
  obtain ⟨h0, h1⟩ := hz
  have hA : 0 ≤ z ^ 4 * (-Real.log z) := by
    have := Real.log_nonpos h0.le h1.le
    exact mul_nonneg (by positivity) (by linarith)
  have hB : 0 ≤ z ^ 4 * (Real.log z) ^ 2 := by positivity
  have hL : 0 < Real.log (1 + 4 * z) := Real.log_pos (by linarith)
  have hL5 : Real.log (1 + 4 * z) ≤ Real.log 5 := Real.log_le_log (by linarith) (by linarith)
  have hlow := log_lower (4 * z) (by linarith) (by linarith)
  have hinv : 1 / Real.log (1 + 4 * z) ≤ 1 / (4 * z) + 1 / 2 - z / 12 := by
    have : 4 * z / 48 = z / 12 := by ring
    rw [this] at hlow; exact hlow
  rw [uI_eq, wI_eq]
  have e1 : ∀ C : ℝ, C / Real.log (1 + 4 * z) = C * (1 / Real.log (1 + 4 * z)) := fun C => by ring
  refine ⟨?_, ?_, by positivity, ?_⟩
  · exact div_le_div_of_nonneg_left hA hL hL5
  · rw [e1]
    calc z ^ 4 * (-Real.log z) * (1 / Real.log (1 + 4 * z))
        ≤ z ^ 4 * (-Real.log z) * (1 / (4 * z) + 1 / 2 - z / 12) :=
          mul_le_mul_of_nonneg_left hinv hA
      _ = _ := by field_simp; ring
  · rw [e1]
    calc z ^ 4 * (Real.log z) ^ 2 * (1 / Real.log (1 + 4 * z))
        ≤ z ^ 4 * (Real.log z) ^ 2 * (1 / (4 * z) + 1 / 2 - z / 12) :=
          mul_le_mul_of_nonneg_left hinv hB
      _ = _ := by field_simp

theorem cont_neglog (k : ℕ) : Continuous (fun z : ℝ => z ^ (k + 1) * (-Real.log z)) := by
  have : (fun z : ℝ => z ^ (k + 1) * (-Real.log z)) = fun z => -(z ^ k * (z * Real.log z)) := by
    funext z; ring
  rw [this]; exact ((continuous_pow k).mul continuous_mul_log).neg

theorem cont_log2 (k : ℕ) : Continuous (fun z : ℝ => z ^ (k + 2) * (Real.log z) ^ 2) := by
  have : (fun z : ℝ => z ^ (k + 2) * (Real.log z) ^ 2) =
      fun z => z ^ k * (z * Real.log z) ^ 2 := by funext z; ring
  rw [this]; exact (continuous_pow k).mul (continuous_mul_log.pow 2)

end LPM

namespace LPM
open MeasureTheory Set Real LocalProbeMIS871.Greedy

theorem ii_neg (k : ℕ) : IntervalIntegrable (fun z : ℝ => z ^ (k + 1) * (-Real.log z)) volume 0 1 :=
  (cont_neglog k).intervalIntegrable _ _

theorem ii_l2 (k : ℕ) : IntervalIntegrable (fun z : ℝ => z ^ (k + 2) * (Real.log z) ^ 2) volume 0 1 :=
  (cont_log2 k).intervalIntegrable _ _

theorem I3 : ∫ z in (0:ℝ)..1, z ^ 3 * (-Real.log z) = 1 / 16 := by
  have := int_pow_neglog 2; norm_num at this ⊢; exact this
theorem I4 : ∫ z in (0:ℝ)..1, z ^ 4 * (-Real.log z) = 1 / 25 := by
  have := int_pow_neglog 3; norm_num at this ⊢; exact this
theorem I5 : ∫ z in (0:ℝ)..1, z ^ 5 * (-Real.log z) = 1 / 36 := by
  have := int_pow_neglog 4; norm_num at this ⊢; exact this
theorem J3 : ∫ z in (0:ℝ)..1, z ^ 3 * (Real.log z) ^ 2 = 1 / 32 := by
  have := int_pow_log2 1; norm_num at this ⊢; exact this
theorem J4 : ∫ z in (0:ℝ)..1, z ^ 4 * (Real.log z) ^ 2 = 2 / 125 := by
  have := int_pow_log2 2; norm_num at this ⊢; exact this
theorem J5 : ∫ z in (0:ℝ)..1, z ^ 5 * (Real.log z) ^ 2 = 1 / 108 := by
  have := int_pow_log2 3; norm_num at this ⊢; exact this

theorem lemma_A_1_proof :
    IntegrableOn (uIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    IntegrableOn (wIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    (0 < coeffU 5 ∧ coeffU 5 < 1 / 5) ∧
    1 / 160 ≤ Real.log 4 - 1 - 5 * coeffW 5 := by
  have c3 : Continuous fun z : ℝ => z ^ 3 * (-Real.log z) := cont_neglog 2
  have c4 : Continuous fun z : ℝ => z ^ 4 * (-Real.log z) := cont_neglog 3
  have c5 : Continuous fun z : ℝ => z ^ 5 * (-Real.log z) := cont_neglog 4
  have d3 : Continuous fun z : ℝ => z ^ 3 * (Real.log z) ^ 2 := cont_log2 1
  have d4 : Continuous fun z : ℝ => z ^ 4 * (Real.log z) ^ 2 := cont_log2 2
  have d5 : Continuous fun z : ℝ => z ^ 5 * (Real.log z) ^ 2 := cont_log2 3
  set Ub : ℝ → ℝ := fun z => (1/4) * (z ^ 3 * (-Real.log z)) + (1/2) * (z ^ 4 * (-Real.log z)) -
      (1/12) * (z ^ 5 * (-Real.log z)) with hUb
  set Wb : ℝ → ℝ := fun z => (1/4) * (z ^ 3 * (Real.log z) ^ 2) + (1/2) * (z ^ 4 * (Real.log z) ^ 2) -
      (1/12) * (z ^ 5 * (Real.log z) ^ 2) with hWb
  have cUb : Continuous Ub := ((c3.const_mul _).add (c4.const_mul _)).sub (c5.const_mul _)
  have cWb : Continuous Wb := ((d3.const_mul _).add (d4.const_mul _)).sub (d5.const_mul _)
  have iUb : IntegrableOn Ub (Ioo 0 1) := (cUb.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have iWb : IntegrableOn Wb (Ioo 0 1) := (cWb.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hu : IntegrableOn (uIntegrand 5) (Ioo 0 1) := by
    refine Integrable.mono' iUb meas_uI.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    obtain ⟨hl, hu', _, _⟩ := bounds_pt z hz
    have : 0 ≤ z ^ 4 * (-Real.log z) / Real.log 5 := by
      have := Real.log_nonpos hz.1.le hz.2.le
      exact div_nonneg (mul_nonneg (by have := hz.1; positivity) (by linarith))
        (Real.log_nonneg (by norm_num))
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans this hl)]; exact hu'
  have hw : IntegrableOn (wIntegrand 5) (Ioo 0 1) := by
    refine Integrable.mono' iWb meas_wI.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    obtain ⟨_, _, h0, hw'⟩ := bounds_pt z hz
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hw'
  have hIUb : ∫ z in Ioo (0:ℝ) 1, Ub z = 1/4 * (1/16) + 1/2 * (1/25) - 1/12 * (1/36) := by
    rw [ioo_eq, hUb]
    simp only
    have i12 : IntervalIntegrable (fun z : ℝ => 1/4 * (z ^ 3 * (-Real.log z)) + 1/2 * (z ^ 4 * (-Real.log z)))
        volume 0 1 := ((c3.const_mul _).add (c4.const_mul _)).intervalIntegrable 0 1
    have i1 : IntervalIntegrable (fun z : ℝ => 1/4 * (z ^ 3 * (-Real.log z))) volume 0 1 :=
      (c3.const_mul _).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun z : ℝ => 1/2 * (z ^ 4 * (-Real.log z))) volume 0 1 :=
      (c4.const_mul _).intervalIntegrable 0 1
    have i3 : IntervalIntegrable (fun z : ℝ => 1/12 * (z ^ 5 * (-Real.log z))) volume 0 1 :=
      (c5.const_mul _).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub i12 i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, I3, I4, I5]
  have hIWb : ∫ z in Ioo (0:ℝ) 1, Wb z = 1/4 * (1/32) + 1/2 * (2/125) - 1/12 * (1/108) := by
    rw [ioo_eq, hWb]
    simp only
    have i12 : IntervalIntegrable (fun z : ℝ => 1/4 * (z ^ 3 * (Real.log z) ^ 2) + 1/2 * (z ^ 4 * (Real.log z) ^ 2))
        volume 0 1 := ((d3.const_mul _).add (d4.const_mul _)).intervalIntegrable 0 1
    have i1 : IntervalIntegrable (fun z : ℝ => 1/4 * (z ^ 3 * (Real.log z) ^ 2)) volume 0 1 :=
      (d3.const_mul _).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun z : ℝ => 1/2 * (z ^ 4 * (Real.log z) ^ 2)) volume 0 1 :=
      (d4.const_mul _).intervalIntegrable 0 1
    have i3 : IntervalIntegrable (fun z : ℝ => 1/12 * (z ^ 5 * (Real.log z) ^ 2)) volume 0 1 :=
      (d5.const_mul _).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub i12 i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, J3, J4, J5]
  have huU : ∫ z in Ioo (0:ℝ) 1, uIntegrand 5 z ≤ ∫ z in Ioo (0:ℝ) 1, Ub z :=
    setIntegral_mono_on hu iUb measurableSet_Ioo (fun z hz => (bounds_pt z hz).2.1)
  have hwW : ∫ z in Ioo (0:ℝ) 1, wIntegrand 5 z ≤ ∫ z in Ioo (0:ℝ) 1, Wb z :=
    setIntegral_mono_on hw iWb measurableSet_Ioo (fun z hz => (bounds_pt z hz).2.2.2)
  have iA : IntegrableOn (fun z : ℝ => z ^ 4 * (-Real.log z) / Real.log 5) (Ioo 0 1) :=
    ((c4.div_const _).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have huL : ∫ z in Ioo (0:ℝ) 1, z ^ 4 * (-Real.log z) / Real.log 5 ≤
      ∫ z in Ioo (0:ℝ) 1, uIntegrand 5 z :=
    setIntegral_mono_on iA hu measurableSet_Ioo (fun z hz => (bounds_pt z hz).1)
  have hAval : ∫ z in Ioo (0:ℝ) 1, z ^ 4 * (-Real.log z) / Real.log 5 = (1/25) / Real.log 5 := by
    rw [integral_div, ioo_eq, I4]
  rw [hAval] at huL
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨hu, hw, ⟨?_, ?_⟩, ?_⟩
  · unfold coeffU
    have : 0 < (1/25) / Real.log 5 := by positivity
    linarith
  · unfold coeffU; rw [hIUb] at huU; norm_num at huU ⊢; linarith
  · unfold coeffW; rw [hIWb] at hwW; rw [hl4]; norm_num at hwW ⊢; linarith

end LPM


open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution :
    IntegrableOn (uIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    IntegrableOn (wIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    (0 < coeffU 5 ∧ coeffU 5 < 1 / 5) ∧
    1 / 160 ≤ Real.log 4 - 1 - 5 * coeffW 5 :=
  LPM.lemma_A_1_proof

