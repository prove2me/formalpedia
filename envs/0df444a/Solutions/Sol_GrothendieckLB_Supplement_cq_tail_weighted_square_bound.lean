-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_tail_weighted_square_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:16:25.717798+00:00
-- url     : https://prove2.me/submissions/081ab2e4-27d8-4147-b4f2-d2bb576cdcfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_sixth_euler_circle_mean
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter MeasureTheory GrothendieckLB GrothendieckLB.Supplement
open scoped Topology Interval Real

namespace SixthEulerTail

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
      Real.circleAverage (fun z => ‖(E^[6] F) z‖) 0 r ≤ 40000000) (n : ℕ) :
    |(n : ℝ)^6 * taylorCoeff n H| ≤ 40000000 := by
  have hf := hF.analyticOnNhd Metric.isOpen_ball
  let G := E^[6] F
  let B := ‖iteratedDeriv n G 0 / (n.factorial : ℂ)‖
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < r :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hr1 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1), r < 1 := self_mem_nhdsWithin
  have hb : B ≤ 40000000 := by
    have ht : Tendsto (fun r : ℝ => B*r^n) (nhdsWithin 1 (Set.Iio 1)) (𝓝 B) := by
      have ht0 : Tendsto (fun r : ℝ => B*r^n) (nhdsWithin 1 (Set.Iio 1)) (𝓝 (B*(1:ℝ)^n)) :=
        tendsto_const_nhds.mul (continuousWithinAt_id.tendsto.pow n)
      simpa only [one_pow,mul_one] using ht0
    apply le_of_tendsto ht
    filter_upwards [hpos, hr1, hmean] with r hr hr' hmr
    exact (cauchy_mean_bound (euler_analytic hf 6).differentiableOn n hr hr').trans hmr
  calc
    _ = (n : ℝ)^6 * |(iteratedDeriv n F 0 / (n.factorial : ℂ)).re| := by
      rw [real_jet hf hreal n, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^6)]
    _ ≤ (n : ℝ)^6 * ‖iteratedDeriv n F 0 / (n.factorial : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ = B := by
      dsimp only [B,G]
      rw [iter_euler_jet hf 6 n, mul_div_assoc, norm_mul, norm_pow]
      simp
    _ ≤ _ := hb

private theorem reciprocal_sixth_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 2) ^ 6 ≤ 1 / (10 * x ^ 5) - 1 / (10 * (x + 2) ^ 5) := by
  have hp : 10 * x ^ 5 + x ^ 5 * (x + 2) ≤ (x + 2) ^ 6 := by
    have h : 0 ≤ 60 * x^4 + 160 * x^3 + 240 * x^2 + 192 * x + 64 := by positivity
    nlinarith only [h]
  apply (le_sub_iff_add_le).2
  apply sub_nonneg.mp
  have hden : x + 2 ≠ 0 := by positivity
  have hid :
      1 / (10 * x ^ 5) - (1 / (x + 2) ^ 6 + 1 / (10 * (x + 2) ^ 5)) =
        ((x + 2) ^ 6 - (10 * x ^ 5 + x ^ 5 * (x + 2))) / (10 * x ^ 5 * (x + 2) ^ 6) := by
    field_simp [hx.ne', hden] <;> ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hp) (by positivity)

private theorem reciprocal_sixth_sum (N : ℝ) (hN : 0 < N) (k : ℕ) :
    (∑ j ∈ Finset.range k, 1 / (N + 2 * ((j : ℝ) + 1)) ^ 6) ≤
      1 / (10 * N ^ 5) - 1 / (10 * (N + 2 * (k : ℝ)) ^ 5) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h := reciprocal_sixth_step (N + 2 * (k : ℝ)) (by positivity)
    rw [show N + 2 * (k : ℝ) + 2 = N + 2 * ((k : ℝ) + 1) by ring] at h
    linarith only [ih, h]

end SixthEulerTail

open SixthEulerTail

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    ∀ n : ℕ, (∑ j ∈ Finset.range n,
      ((251 : ℝ) + 2 * ((j : ℝ) + 1)) ^ 6 *
        (GrothendieckLB.taylorCoeff (2 * j + 253) H) ^ 2) ≤ (14.443 : ℝ) ^ 2 := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  obtain ⟨F,hF,hr,hm⟩ := cq_sixth_euler_circle_mean
  have hd (m : ℕ) : |(m : ℝ)^6 * taylorCoeff m H| ≤ 40000000 :=
    coefficient_decay hF hr hm m
  dsimp only
  intro n
  let L (j : ℕ) : ℝ := 251 + 2 * ((j:ℝ)+1)
  have hj (j : ℕ) : (L j)^6 * (taylorCoeff (2*j+253) H)^2 ≤ (40000000:ℝ)^2 * (1/(L j)^6) := by
    have h := hd (2*j+253)
    have he : ((2*j+253 : ℕ) : ℝ) = L j := by dsimp [L]; push_cast; ring
    rw [he] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 40000000)).mpr h
    rw [sq_abs] at hs
    have hp : 0 < (L j)^6 := by dsimp [L]; positivity
    rw [mul_one_div, le_div_iff₀ hp]
    nlinarith only [hs]
  calc
    _ ≤ ∑ j ∈ Finset.range n, (40000000:ℝ)^2 * (1/(L j)^6) := Finset.sum_le_sum fun j _ => hj j
    _ = (40000000:ℝ)^2 * (∑ j ∈ Finset.range n, 1/(L j)^6) := (Finset.mul_sum ..).symm
    _ ≤ (40000000:ℝ)^2 * (1/(10*251^5)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (reciprocal_sixth_sum 251 (by norm_num) n).trans (sub_le_self _ (by positivity))
    _ ≤ _ := by norm_num
