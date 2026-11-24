-- Prove2me | solution 4 for GrothendieckConstant.grothendieckConst_le_cubic_quintic
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T22:26:05.935182+00:00
-- url     : https://prove2.me/submissions/903dfe31-cf00-49ee-8fb4-6854b4cecca3

import Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_euler_circle_mean
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_cq_head_coefficient_enclosures
import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap

open Filter MeasureTheory GrothendieckLB GrothendieckLB.Supplement
open scoped Topology Interval Real

namespace FifthEulerTail

private noncomputable def E (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z

private lemma euler_analytic {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1)) (k : ℕ) :
    AnalyticOnNhd ℂ (E^[k] F) (Metric.ball 0 1) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro z hz
    exact analyticAt_id.mul (ih.deriv z hz)

private lemma euler_jet {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    iteratedDeriv n (E G) 0 = n * iteratedDeriv n G 0 := by
  cases n with
  | zero => simp [E]
  | succ n =>
    unfold E
    rw [iteratedDeriv_fun_mul (by fun_prop) hG.deriv.contDiffAt]
    simp only [iteratedDeriv_fun_id_zero]
    rw [Finset.sum_eq_single 1]
    · simp [← iteratedDeriv_succ']
    · intro i _ hi
      simp [hi]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (by omega)))

private lemma iter_euler_jet {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1)) (k n : ℕ) :
    iteratedDeriv n (E^[k] F) 0 = (n : ℂ)^k * iteratedDeriv n F 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', euler_jet (euler_analytic hF k 0 (by simp)), ih, pow_succ]
    ring

private lemma mean_norm (f : ℂ → ℂ) (r : ℝ) :
    ‖Real.circleAverage f 0 r‖ ≤ Real.circleAverage (fun z => ‖f z‖) 0 r := by
  simp only [Real.circleAverage, norm_smul, Real.norm_eq_abs, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))]
  exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm (by positivity))
    (by positivity)

private lemma cauchy_mean_bound {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 1))
    (n : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖iteratedDeriv n G 0 / (n.factorial : ℂ)‖ * r^n ≤
      Real.circleAverage (fun z => ‖G z‖) 0 r := by
  let g (z : ℂ) := (z^n)⁻¹ * G z
  have hcl : DifferentiableOn ℂ G (Metric.closedBall 0 r) :=
    hG.mono (Metric.closedBall_subset_ball hr1)
  have hi := hcl.circleIntegral_one_div_sub_center_pow_smul hr n
  have hca : Real.circleAverage g 0 r = iteratedDeriv n G 0 / n.factorial := by
    rw [Real.circleAverage_eq_circleIntegral hr.ne']
    have hg : (fun z : ℂ => (z-0)⁻¹ • g z) =
        (fun z : ℂ => (1/(z-0)^(n+1)) • G z) := by
      funext z
      simp [g, smul_eq_mul, pow_succ, mul_assoc, mul_left_comm, mul_comm]
    rw [hg, hi]
    simp only [smul_eq_mul]
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hng : Real.circleAverage (fun z => ‖g z‖) 0 r =
      (r^n)⁻¹ * Real.circleAverage (fun z => ‖G z‖) 0 r := by
    calc
      _ = Real.circleAverage (fun z => (r^n)⁻¹ • ‖G z‖) 0 r := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hzr : ‖z‖ = r := by simpa [Metric.mem_sphere, abs_of_pos hr] using hz
        simp [g, norm_mul, norm_inv, norm_pow, hzr, smul_eq_mul]
      _ = _ := Real.circleAverage_fun_smul
  have h := mean_norm g r
  rw [hca, hng, ← div_eq_inv_mul] at h
  exact (le_div_iff₀ (pow_pos hr n)).mp h

private lemma real_jet {F : ℂ → ℂ} {H : ℝ → ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1))
    (hr : ∀ t : ℝ, |t| < 1 → F (t : ℂ) = (H t : ℂ)) (n : ℕ) :
    taylorCoeff n H = (iteratedDeriv n F 0 / (n.factorial : ℂ)).re := by
  have hd (m : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv m F) (Metric.ball 0 1) := by
    induction m with
    | zero => simpa using hF
    | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have he (m : ℕ) : ∀ t : ℝ, |t| < 1 → iteratedDeriv m H t = (iteratedDeriv m F (t : ℂ)).re := by
    induction m with
    | zero => intro t ht; simp [hr t ht]
    | succ m ih =>
      intro t ht
      have ht' : (t : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simpa [Real.norm_eq_abs] using ht
      have hnear : ∀ᶠ y in 𝓝 t, |y| < 1 := (isOpen_lt continuous_abs continuous_const).mem_nhds ht
      have hl := hnear.mono fun y hy => ih y hy
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact (show iteratedDeriv m H =ᶠ[𝓝 t] (fun x : ℝ => (iteratedDeriv m F (x : ℂ)).re) from hl).deriv_eq.trans
        ((hd m _ ht').differentiableAt.hasDerivAt.real_of_complex.deriv)
  rw [taylorCoeff, he n 0 (by norm_num)]
  simp [← Complex.ofReal_natCast, Complex.div_ofReal_re]

private lemma coefficient_decay {H : ℝ → ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F (t : ℂ) = (H t : ℂ))
    (hmean : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
      Real.circleAverage (fun z => ‖(E^[5] F) z‖) 0 r ≤ 416000) (n : ℕ) :
    |(n : ℝ)^5 * taylorCoeff n H| ≤ 416000 := by
  have hf := hF.analyticOnNhd Metric.isOpen_ball
  let G := E^[5] F
  let B := ‖iteratedDeriv n G 0 / (n.factorial : ℂ)‖
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < r :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hr1 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), r < 1 := self_mem_nhdsWithin
  have hb : B ≤ 416000 := by
    have ht : Tendsto (fun r : ℝ => B*r^n) (nhdsWithin 1 (Set.Iio 1)) (𝓝 B) := by
      have ht0 : Tendsto (fun r : ℝ => B*r^n) (nhdsWithin 1 (Set.Iio 1)) (𝓝 (B*(1:ℝ)^n)) :=
        tendsto_const_nhds.mul (continuousWithinAt_id.tendsto.pow n)
      simpa only [one_pow,mul_one] using ht0
    apply le_of_tendsto ht
    filter_upwards [hpos, hr1, hmean] with r hr hr' hmr
    exact (cauchy_mean_bound (euler_analytic hf 5).differentiableOn n hr hr').trans hmr
  calc
    _ = (n : ℝ)^5 * |(iteratedDeriv n F 0 / (n.factorial : ℂ)).re| := by
      rw [real_jet hf hreal n, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^5)]
    _ ≤ (n : ℝ)^5 * ‖iteratedDeriv n F 0 / (n.factorial : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = B := by
      dsimp only [B,G]
      rw [iter_euler_jet hf 5 n, mul_div_assoc, norm_mul, norm_pow]
      simp
    _ ≤ _ := hb

private theorem reciprocal_fifth_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 2) ^ 5 ≤ 1 / (8 * x ^ 4) - 1 / (8 * (x + 2) ^ 4) := by
  have hp : 8 * x ^ 4 + x ^ 4 * (x + 2) ≤ (x + 2) ^ 5 := by
    have h : 0 ≤ 40 * x^3 + 80 * x^2 + 80 * x + 32 := by positivity
    nlinarith only [h]
  apply (le_sub_iff_add_le).2
  apply sub_nonneg.mp
  have hden : x + 2 ≠ 0 := by positivity
  have hid :
      1 / (8 * x ^ 4) - (1 / (x + 2) ^ 5 + 1 / (8 * (x + 2) ^ 4)) =
        ((x + 2) ^ 5 - (8 * x ^ 4 + x ^ 4 * (x + 2))) / (8 * x ^ 4 * (x + 2) ^ 5) := by
    field_simp [hx.ne', hden] <;> ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hp) (by positivity)

private theorem reciprocal_fifth_sum (N : ℝ) (hN : 0 < N) (k : ℕ) :
    (∑ j ∈ Finset.range k, 1 / (N + 2 * ((j : ℝ) + 1)) ^ 5) ≤
      1 / (8 * N ^ 4) - 1 / (8 * (N + 2 * (k : ℝ)) ^ 4) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h := reciprocal_fifth_step (N + 2 * (k : ℝ)) (by positivity)
    rw [show N + 2 * (k : ℝ) + 2 = N + 2 * ((k : ℝ) + 1) by ring] at h
    linarith only [ih, h]

private lemma tail_direct :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    Summable (fun j : ℕ => |taylorCoeff (2*j+253) H|) ∧
      (∑' j : ℕ, |taylorCoeff (2*j+253) H|) ≤ 416000 / (8*(251:ℝ)^4) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  obtain ⟨F, hF, hr, hm⟩ := cq_fifth_euler_circle_mean
  let L (j : ℕ) : ℝ := 251 + 2*((j:ℝ)+1)
  have hj (j : ℕ) : |taylorCoeff (2*j+253) H| ≤ 416000 * (1/(L j)^5) := by
    have h := coefficient_decay (H:=H) hF hr hm (2*j+253)
    have he : ((2*j+253 : ℕ) : ℝ) = L j := by dsimp [L]; push_cast; ring
    have hp : 0 < (L j)^5 := by dsimp [L]; positivity
    rw [he,abs_mul,abs_of_pos hp] at h
    rw [mul_one_div,le_div_iff₀ hp,mul_comm]
    exact h
  have hsums (n : ℕ) : (∑ j ∈ Finset.range n, |taylorCoeff (2*j+253) H|) ≤
      416000 / (8*(251:ℝ)^4) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, 416000*(1/(L j)^5) := Finset.sum_le_sum fun j _ => hj j
      _ = 416000*(∑ j ∈ Finset.range n, 1/(L j)^5) := (Finset.mul_sum ..).symm
      _ ≤ 416000*(1/(8*(251:ℝ)^4)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (reciprocal_fifth_sum 251 (by norm_num) n).trans (sub_le_self _ (by positivity))
      _ = _ := by ring
  have hs : Summable (fun j : ℕ => |taylorCoeff (2*j+253) H|) :=
    summable_of_sum_range_le (fun j => abs_nonneg _) hsums
  exact ⟨hs, Real.tsum_le_of_sum_range_le (fun j => abs_nonneg _) hsums⟩

end FifthEulerTail

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement

private theorem compare_cubic_quintic_radius :
    Real.pi / (2 * (0.881545409 : ℝ)) ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  have hsqrt : Real.sqrt 2 ≤ (1.41421357 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.8813736 := by
    apply (Real.log_le_iff_le_exp (show 0 < 1 + Real.sqrt 2 by positivity)).2
    calc
      1 + Real.sqrt 2 ≤ 1 + 1.41421357 := by linarith only [hsqrt]
      _ ≤ ∑ j ∈ Finset.range 11, (0.8813736 : ℝ) ^ j / (j.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp 0.8813736 := Real.sum_le_exp_of_nonneg (by norm_num) 11
  have hpos : 0 < Real.log (1 + Real.sqrt 2) :=
    Real.log_pos (lt_add_of_pos_right _ (by positivity))
  apply le_sub_iff_add_le.mpr
  calc
    Real.pi / (2 * (0.881545409 : ℝ)) + 3.47 * 10 ^ (-4 : ℤ) ≤
        Real.pi / (2 * (0.8813736 : ℝ)) := by
      norm_num <;> linarith only [Real.pi_gt_d2]
    _ ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (mul_pos (by norm_num) hpos)
        (mul_le_mul_of_nonneg_left hlog (by norm_num))

private theorem scheme_bound : grothendieckConst ≤ Real.pi/(2*0.881545409) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2*j+3) H|
  obtain ⟨S, hS⟩ := exists_limitingScheme_cqCorr 0.136419125 0.34101124 0.05276111
  change S.corr = H at hS
  obtain ⟨hlin, hencl⟩ := cq_head_coefficient_enclosures
  have hlinear : (0.881573822049 : ℝ) ≤ taylorCoeff 1 H := by
    exact (by norm_num : (0.881573822049 : ℝ) ≤ 88157382204959954858 / 10^20).trans hlin
  have hhead : (∑ j ∈ Finset.range 125, a j) ≤ 0.000011328860 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 125, ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ)/10^20 :=
        Finset.sum_le_sum fun j hj => hencl j (Finset.mem_range.mp hj)
      _ = ((∑ j ∈ Finset.range 125, (cqHeadUnits[j]?.getD 0 : ℕ)) : ℕ)/ (10:ℝ)^20 := by
        rw [← Finset.sum_div, Nat.cast_sum]
      _ ≤ _ := by
        let total : ℕ := ∑ j ∈ Finset.range 125, (cqHeadUnits[j]?.getD 0 : ℕ)
        change (total : ℝ)/(10:ℝ)^20 ≤ _
        have hu : total ≤ 1132886000000000 := by decide +kernel
        have hc : (total : ℝ) ≤ (1132886000000000 : ℝ) := by exact_mod_cast hu
        calc
          _ ≤ (1132886000000000:ℝ)/10^20 := div_le_div_of_nonneg_right hc (by positivity)
          _ ≤ _ := by norm_num
  obtain ⟨htail_sum, htail⟩ := FifthEulerTail.tail_direct
  have hshift (j : ℕ) : a (j + 125) = |taylorCoeff (2 * j + 253) H| := by
    dsimp only [a]
    rw [show 2 * (j + 125) + 3 = 2 * j + 253 by omega]
  have hsum : Summable a := by
    apply (summable_nat_add_iff (f := a) 125).1
    simpa only [hshift] using htail_sum
  have hmass : (∑' j, a j) ≤ 0.000024431 := by
    rw [← hsum.sum_add_tsum_nat_add 125]
    have hh : (∑' j : ℕ, a (j+125)) ≤ 416000/(8*(251:ℝ)^4) := by
      simpa only [hshift] using htail
    linarith only [hhead,hh]
  have hgap : 0.881545409 + (∑' j, a j) < taylorCoeff 1 H := by
    linarith only [hmass, hlinear]
  have hsumS : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|) := by
    rw [hS]
    exact hsum
  have hgapS : 0.881545409 + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) <
      taylorCoeff 1 S.corr := by
    rw [hS]
    exact hgap
  exact limitingScheme_bound_of_coefficient_gap S 0.881545409 (by norm_num) hsumS hgapS

theorem solution :
    grothendieckConst ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  exact scheme_bound.trans compare_cubic_quintic_radius
