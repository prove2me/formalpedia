-- Prove2me | solution 1 for LL_Decomp530a.leaf_rademacher_gamma_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T11:26:31.329906+00:00
-- url     : https://prove2.me/submissions/59dd8ade-6a3f-4bf4-985b-d0be2e09a671

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_RademacherGamma_p5_gauss_bounds
import Theorems.Thm_RademacherGamma_gaussian_sum_ge

namespace SolGammaHelpers

open Real MeasureTheory Filter Set
open scoped Topology

private lemma P5_gauss_bounds (a₀ δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    let h : ℝ → ℝ := fun w => Real.exp (-(w - δ) ^ 2 * t) - Real.exp (-(w + δ) ^ 2 * t)
    let h' : ℝ → ℝ := fun w =>
      -2 * (w - δ) * t * Real.exp (-(w - δ) ^ 2 * t) +
        2 * (w + δ) * t * Real.exp (-(w + δ) ^ 2 * t)
    let f3 : ℝ → ℝ := fun u => -4 * t ^ 2 * u * (2 * u ^ 2 * t - 3) * Real.exp (-u ^ 2 * t)
    let h''' : ℝ → ℝ := fun w => f3 (w - δ) - f3 (w + δ)
    Summable (fun k : ℕ => h (a₀ + 1 / 2 + k)) ∧
    |(∑' k : ℕ, h (a₀ + 1 / 2 + k)) - (∫ v in (a₀ - δ)..(a₀ + δ), Real.exp (-v ^ 2 * t)) -
      (1 / 24) * h' a₀ + (7 / 5760) * h''' a₀| ≤ (1 / 24) * (2 * δ) * t ^ 2 * √t :=
  RademacherGamma_p5_gauss_bounds a₀ δ t hδ ht
private lemma gaussian_sum_ge {y δ t : ℝ}
    (hy : 1 / 4 ≤ y) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (ht : 0 < t) :
    2 * δ * Real.exp (-y ^ 2 * t) ≤
      ∑' k : ℕ, (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
  RademacherGamma_gaussian_sum_ge hy hδ0 hδ1 ht

/-! ### Stage 4: Main `Complex.Gamma` ratio theorem -/

private lemma integral_Ioi_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-c * t) = c⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -Real.exp (-c * t) / c) (Real.exp (-c * x)) x := by
    intro x _
    have harg : HasDerivAt (fun t : ℝ => -c * t) (-c) x :=
      ((hasDerivAt_id' x).const_mul (-c)).congr_deriv (by ring)
    refine (harg.exp.neg.div_const c).congr_deriv ?_
    field_simp [hc.ne']
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Set.Ioi 0) MeasureTheory.volume :=
    integrableOn_exp_mul_Ioi (by linarith only [hc] : -c < 0) 0
  have htend : Filter.Tendsto (fun t : ℝ => -Real.exp (-c * t) / c) Filter.atTop (nhds 0) := by
    have ht1 : Filter.Tendsto (fun t : ℝ => Real.exp (-c * t)) Filter.atTop (nhds 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
      simpa only [Function.comp_def, id_eq, neg_mul] using this
    have ht2 := (ht1.neg.div_const c)
    simpa only [neg_zero, zero_div] using ht2
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hftc, mul_zero, Real.exp_zero]
  ring

private noncomputable def gamma_g (x α u : ℝ) : ℝ :=
  2 * Real.log ‖Complex.Gamma (((x + α : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I) /
    Complex.Gamma ((x : ℂ) + (Real.sqrt u : ℂ) * Complex.I)‖ -
    α * Real.log ((x + 1 / 2) ^ 2 + u)

private noncomputable def gamma_gN (x α : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  2 * α * Real.log n +
    ∑ k ∈ Finset.range (n + 1), (Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u)) -
    α * Real.log ((x + 1 / 2) ^ 2 + u)

private noncomputable def gamma_w (x α : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u) +
    α * (Real.log ((k + 1 : ℝ) ^ 2 + u) - Real.log ((k : ℝ) ^ 2 + u))

private lemma c_re_add_im_normSq (r v : ℝ) :
    ‖(r : ℂ) + (v : ℂ) * Complex.I‖ ^ 2 = r ^ 2 + v ^ 2 := by
  have heq : ((r : ℂ) + (v : ℂ) * Complex.I) = ⟨r, v⟩ := by apply Complex.ext <;> simp
  rw [heq, ← Complex.normSq_eq_norm_sq, Complex.normSq_mk, sq, sq]

private lemma c_re_add_im_ne_zero {r v : ℝ} (hv : 0 < v) :
    (r : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.zero_im] at him
  linarith only [hv, him]

private lemma gamma_log_ratio_seq_tendsto {x α u : ℝ} (hu : 0 < u) :
    Filter.Tendsto (fun n : ℕ => gamma_gN x α n u) Filter.atTop (nhds (gamma_g x α u)) := by
  set z₀ : ℂ := (x : ℂ) + (Real.sqrt u : ℂ) * Complex.I
  set z₁ : ℂ := ((x + α : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I
  have hsq : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hz₀_ne : ∀ m : ℕ, z₀ ≠ -(m : ℂ) := by
    intro m h
    have him := congrArg Complex.im h
    simp only [z₀, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.neg_im,
      Complex.natCast_im, neg_zero] at him
    linarith only [hsq, him]
  have hΓ₀_ne : Complex.Gamma z₀ ≠ 0 := Complex.Gamma_ne_zero hz₀_ne
  have hz₁_ne : ∀ m : ℕ, z₁ ≠ -(m : ℂ) := by
    intro m h
    have him := congrArg Complex.im h
    simp only [z₁, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.neg_im,
      Complex.natCast_im, neg_zero] at him
    linarith only [hsq, him]
  have hΓ₁_ne : Complex.Gamma z₁ ≠ 0 := Complex.Gamma_ne_zero hz₁_ne
  have ht_div : Filter.Tendsto (fun n : ℕ => Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n)
      Filter.atTop (nhds (Complex.Gamma z₁ / Complex.Gamma z₀)) :=
    (Complex.GammaSeq_tendsto_Gamma z₁).div (Complex.GammaSeq_tendsto_Gamma z₀) hΓ₀_ne
  have ht_norm : Filter.Tendsto (fun n : ℕ => ‖Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n‖)
      Filter.atTop (nhds ‖Complex.Gamma z₁ / Complex.Gamma z₀‖) :=
    ht_div.norm
  have hnorm_pos : 0 < ‖Complex.Gamma z₁ / Complex.Gamma z₀‖ :=
    norm_pos_iff.mpr (div_ne_zero hΓ₁_ne hΓ₀_ne)
  have ht_log : Filter.Tendsto
      (fun n : ℕ => 2 * Real.log ‖Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n‖ -
        α * Real.log ((x + 1 / 2) ^ 2 + u))
      Filter.atTop (nhds (gamma_g x α u)) := by
    have ht1 := ((Real.continuousAt_log hnorm_pos.ne').tendsto.comp ht_norm).const_mul 2
    exact ht1.sub_const (α * Real.log ((x + 1 / 2) ^ 2 + u))
  refine ht_log.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac_ne : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hzk₀ : ∀ k : ℕ, z₀ + k ≠ 0 := fun k => by
    have heq : z₀ + k = ((x + k : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I := by
      dsimp [z₀]; push_cast; ring
    rw [heq]; exact c_re_add_im_ne_zero hsq
  have hzk₁ : ∀ k : ℕ, z₁ + k ≠ 0 := fun k => by
    have heq : z₁ + k = ((x + α + k : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I := by
      dsimp [z₁]; push_cast; ring
    rw [heq]; exact c_re_add_im_ne_zero hsq
  have hprod₀ : ∏ k ∈ Finset.range (n + 1), (z₀ + k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hzk₀ k
  have hprod₁ : ∏ k ∈ Finset.range (n + 1), (z₁ + k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hzk₁ k
  have hseq_eq : Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n =
      ((n : ℂ) ^ z₁ / (n : ℂ) ^ z₀) * ∏ k ∈ Finset.range (n + 1), ((z₀ + k) / (z₁ + k)) := by
    simp only [Complex.GammaSeq]
    rw [Finset.prod_div_distrib]
    field_simp [hnc_ne, hfac_ne, hprod₀, hprod₁]
  have hnorm_eq : ‖Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n‖ =
      (n : ℝ) ^ α * ∏ k ∈ Finset.range (n + 1), (‖z₀ + k‖ / ‖z₁ + k‖) := by
    rw [hseq_eq, norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast_cpow_of_pos hn]
    have hre₀ : z₀.re = x := by dsimp [z₀]; simp
    have hre₁ : z₁.re = x + α := by dsimp [z₁]; simp
    rw [hre₀, hre₁, ← Real.rpow_sub hn_pos (x + α) x, show x + α - x = α by ring]
    congr 1
    rw [Complex.norm_prod]
    refine Finset.prod_congr rfl fun k _ => norm_div _ _
  have hpos_prod : ∏ k ∈ Finset.range (n + 1), (‖z₀ + k‖ / ‖z₁ + k‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => div_ne_zero (norm_ne_zero_iff.mpr (hzk₀ k))
      (norm_ne_zero_iff.mpr (hzk₁ k))
  have hlog_eq : Real.log ‖Complex.GammaSeq z₁ n / Complex.GammaSeq z₀ n‖ =
      α * Real.log n + ∑ k ∈ Finset.range (n + 1), (Real.log ‖z₀ + k‖ - Real.log ‖z₁ + k‖) := by
    rw [hnorm_eq, Real.log_mul (Real.rpow_pos_of_pos hn_pos α).ne' hpos_prod,
      Real.log_rpow hn_pos, Real.log_prod fun k _ =>
        div_ne_zero (norm_ne_zero_iff.mpr (hzk₀ k)) (norm_ne_zero_iff.mpr (hzk₁ k))]
    congr 1
    refine Finset.sum_congr rfl fun k _ =>
      Real.log_div (norm_ne_zero_iff.mpr (hzk₀ k)) (norm_ne_zero_iff.mpr (hzk₁ k))
  have hlog_sq : ∀ k : ℕ, 2 * (Real.log ‖z₀ + k‖ - Real.log ‖z₁ + k‖) =
      Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u) := by
    intro k
    have hsq0 : ‖z₀ + k‖ ^ 2 = (x + k) ^ 2 + u := by
      have heq : z₀ + k = ((x + k : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I := by
        dsimp [z₀]; push_cast; ring
      rw [heq, c_re_add_im_normSq, Real.sq_sqrt hu.le]
    have hsq1 : ‖z₁ + k‖ ^ 2 = (x + α + k) ^ 2 + u := by
      have heq : z₁ + k = ((x + α + k : ℝ) : ℂ) + (Real.sqrt u : ℂ) * Complex.I := by
        dsimp [z₁]; push_cast; ring
      rw [heq, c_re_add_im_normSq, Real.sq_sqrt hu.le]
    rw [← hsq0, ← hsq1, Real.log_pow, Real.log_pow]
    push_cast; ring
  dsimp [gamma_gN]
  rw [hlog_eq, mul_add, Finset.mul_sum]
  simp_rw [hlog_sq]
  ring

private lemma log_one_add_bounds {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ Real.log (1 + h) ∧ Real.log (1 + h) ≤ h ∧ 0 ≤ h - Real.log (1 + h) ∧ h - Real.log (1 + h) ≤ h ^ 2 := by
  have hpos : 0 < 1 + h := by linarith only [hh]
  have h0 : 0 ≤ Real.log (1 + h) := Real.log_nonneg (by linarith only [hh])
  have hub : Real.log (1 + h) ≤ h := by linarith only [Real.log_le_sub_one_of_pos hpos]
  have hlb := Real.one_sub_inv_le_log_of_pos hpos
  have hdiff : h - (1 - (1 + h)⁻¹) = h ^ 2 / (1 + h) := by
    field_simp [hpos.ne']; ring
  have hdiv : h ^ 2 / (1 + h) ≤ h ^ 2 := div_le_self (sq_nonneg h) (by linarith only [hh])
  refine ⟨h0, hub, by linarith only [hub], by linarith only [hlb, hdiff, hdiv]⟩

private lemma gamma_w_bound (x α : ℝ) (hx : -(1 / 4 : ℝ) < x) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ u : ℝ, 0 ≤ u → |gamma_w x α k u| ≤ C / (k : ℝ) ^ 2 := by
  set K₀ : ℕ := Nat.ceil (2 * |x| + 2) + 1
  have hK₀_ge : (2 * |x| + 2 : ℝ) ≤ K₀ := by
    have := Nat.le_ceil (2 * |x| + 2)
    dsimp [K₀]; push_cast; linarith only [this]
  set B₀ : ℝ := 3 + 16 / 9 * (2 * (|x| + K₀) + 1)
  set C_tail : ℝ := 265 + 4 * (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2 + |1 - 2 * x - α|)
  refine ⟨max C_tail (B₀ * (K₀ : ℝ) ^ 2), le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro k hk u hu
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hxk : (3 / 4 : ℝ) ≤ x + k := by linarith only [hx, hk1]
  have ha₁_pos : 0 < (x + k) ^ 2 + u := by positivity
  have ha₂_pos : 0 < (k : ℝ) ^ 2 + u := by positivity
  set a₁ := (x + k) ^ 2 + u
  set b₁ := (x + α + k) ^ 2 + u
  set h₁ := (2 * α * (x + k) + α ^ 2) / a₁
  have hb₁_eq : b₁ = a₁ * (1 + h₁) := by
    dsimp [a₁, b₁, h₁]; field_simp [ha₁_pos.ne']; ring
  have hh₁_nn : 0 ≤ h₁ := by
    have : 0 ≤ 2 * α * (x + k) + α ^ 2 := by positivity
    exact div_nonneg this ha₁_pos.le
  have hlog₁ : Real.log ((x + α + k) ^ 2 + u) - Real.log ((x + k) ^ 2 + u) = Real.log (1 + h₁) := by
    change Real.log b₁ - Real.log a₁ = Real.log (1 + h₁)
    rw [hb₁_eq, Real.log_mul ha₁_pos.ne' (by linarith only [hh₁_nn])]
    ring
  set a₂ := (k : ℝ) ^ 2 + u
  set b₂ := (k + 1 : ℝ) ^ 2 + u
  set h₂ := (2 * (k : ℝ) + 1) / a₂
  have hb₂_eq : b₂ = a₂ * (1 + h₂) := by
    dsimp [a₂, b₂, h₂]; field_simp [ha₂_pos.ne']; ring
  have hh₂_nn : 0 ≤ h₂ := by positivity
  have hlog₂ : Real.log ((k + 1 : ℝ) ^ 2 + u) - Real.log ((k : ℝ) ^ 2 + u) = Real.log (1 + h₂) := by
    change Real.log b₂ - Real.log a₂ = Real.log (1 + h₂)
    rw [hb₂_eq, Real.log_mul ha₂_pos.ne' (by linarith only [hh₂_nn])]
    ring
  have hw_eq : gamma_w x α k u = α * Real.log (1 + h₂) - Real.log (1 + h₁) := by
    dsimp [gamma_w]
    rw [hlog₂]
    linarith only [hlog₁]
  rw [hw_eq]
  rcases log_one_add_bounds hh₁_nn with ⟨hl1_0, hl1_ub, hl1_d0, hl1_d⟩
  rcases log_one_add_bounds hh₂_nn with ⟨hl2_0, hl2_ub, hl2_d0, hl2_d⟩
  by_cases hkK : k < K₀
  · have hk_lt : (k : ℝ) < K₀ := by exact_mod_cast hkK
    have h₁_bd : h₁ ≤ 16 / 9 * (2 * (|x| + K₀) + 1) := by
      have ha₁_lb : (9 / 16 : ℝ) ≤ a₁ := by
        dsimp [a₁]; nlinarith only [hxk, hu]
      have hnum : 2 * α * (x + k) + α ^ 2 ≤ 2 * (|x| + K₀) + 1 := by
        have hx_abs : x ≤ |x| := le_abs_self x
        have hα2 : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
        have h1 : 2 * α * (x + k) ≤ 2 * (|x| + K₀) := by
          have : 0 ≤ x + k := by linarith only [hxk]
          nlinarith only [hα1, this, hx_abs, hk_lt]
        linarith only [h1, hα2]
      calc h₁ = (2 * α * (x + k) + α ^ 2) / a₁ := rfl
        _ ≤ (2 * (|x| + K₀) + 1) / (9 / 16) :=
          div_le_div₀ (by positivity) hnum (by norm_num) ha₁_lb
        _ = 16 / 9 * (2 * (|x| + K₀) + 1) := by ring
    have h₂_bd : h₂ ≤ 3 := by
      have ha₂_lb : (k : ℝ) ^ 2 ≤ a₂ := by dsimp [a₂]; linarith only [hu]
      have ha₂_lb1 : (1 : ℝ) ≤ a₂ := le_trans (by nlinarith only [hk1]) ha₂_lb
      have hnum : 2 * (k : ℝ) + 1 ≤ 3 * a₂ := by
        have hk2_ge : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
        linarith only [hk2_ge, ha₂_lb, ha₂_lb1]
      exact (div_le_iff₀ ha₂_pos).mpr hnum
    have hw_abs : |α * Real.log (1 + h₂) - Real.log (1 + h₁)| ≤ B₀ := by
      rw [abs_le]
      have h1 : α * Real.log (1 + h₂) ≤ 3 := by nlinarith only [hα0, hα1, hl2_0, hl2_ub, h₂_bd]
      have h2 : 0 ≤ α * Real.log (1 + h₂) := mul_nonneg hα0.le hl2_0
      dsimp [B₀]
      constructor <;> linarith only [h1, h2, hl1_0, hl1_ub, h₁_bd]
    have hdiv : B₀ ≤ B₀ * (K₀ : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
      have hsq : (k : ℝ) ^ 2 ≤ (K₀ : ℝ) ^ 2 := by nlinarith only [hk_pos, hk_lt]
      exact mul_le_mul_of_nonneg_left hsq hB₀
    exact le_trans hw_abs (le_trans hdiv (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)))
  · have hk_ge : K₀ ≤ k := le_of_not_gt hkK
    have hk_ge_r : (K₀ : ℝ) ≤ k := by exact_mod_cast hk_ge
    have hxk_half : (k : ℝ) / 2 ≤ x + k := by
      have : -|x| ≤ x := neg_abs_le x
      linarith only [this, hK₀_ge, hk_ge_r]
    have hxk_ub : x + k ≤ 3 / 2 * k := by
      have : x ≤ |x| := le_abs_self x
      linarith only [this, hK₀_ge, hk_ge_r]
    have ha₁_lb : (k : ℝ) ^ 2 / 4 + u ≤ a₁ := by
      have : (k : ℝ) ^ 2 / 4 ≤ (x + k) ^ 2 := by nlinarith only [hk_pos, hxk_half]
      dsimp [a₁]; linarith only [this]
    have ha₁_lb0 : (k : ℝ) ^ 2 / 4 ≤ a₁ := by linarith only [ha₁_lb, hu]
    have h₁_bd : h₁ ≤ 16 / k := by
      have hnum : 2 * α * (x + k) + α ^ 2 ≤ 4 * k := by
        have h1 : 2 * α * (x + k) ≤ 3 * k := by nlinarith only [hα1, hxk_ub, hxk]
        have hα2 : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
        linarith only [h1, hα2, hk1]
      calc h₁ = (2 * α * (x + k) + α ^ 2) / a₁ := rfl
        _ ≤ (4 * k) / ((k : ℝ) ^ 2 / 4) :=
          div_le_div₀ (by positivity) hnum (by positivity) ha₁_lb0
        _ = 16 / k := by field_simp [hk_pos.ne']; ring
    have h₂_bd : h₂ ≤ 3 / k := by
      have ha₂_lb : (k : ℝ) ^ 2 ≤ a₂ := by dsimp [a₂]; linarith only [hu]
      have hnum : 2 * (k : ℝ) + 1 ≤ 3 * k := by linarith only [hk1]
      calc h₂ = (2 * (k : ℝ) + 1) / a₂ := rfl
        _ ≤ (3 * k) / (k : ℝ) ^ 2 :=
          div_le_div₀ (by positivity) hnum (by positivity) ha₂_lb
        _ = 3 / k := by field_simp [hk_pos.ne']
    have h1_sq : h₁ ^ 2 ≤ 256 / (k : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ hh₁_nn h₁_bd 2
      linarith only [h, show (16 / (k : ℝ)) ^ 2 = 256 / (k : ℝ) ^ 2 by ring]
    have h2_sq : α * h₂ ^ 2 ≤ 9 / (k : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ hh₂_nn h₂_bd 2
      have h9 : h₂ ^ 2 ≤ 9 / (k : ℝ) ^ 2 := by
        linarith only [h, show (3 / (k : ℝ)) ^ 2 = 9 / (k : ℝ) ^ 2 by ring]
      nlinarith only [hα0, hα1, h9]
    have hlin_diff : |α * h₂ - h₁| ≤
        4 * (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2 + |1 - 2 * x - α|) / (k : ℝ) ^ 2 := by
      have hident : α * h₂ - h₁ =
          α * ((2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2 + (1 - 2 * x - α) * u) /
            (a₂ * a₁) := by
        dsimp [h₁, h₂, a₁, a₂]
        field_simp [ha₁_pos.ne', ha₂_pos.ne']; ring
      have hnum_abs : |α * ((2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2 + (1 - 2 * x - α) * u)| ≤
          (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2) * (k : ℝ) ^ 2 + |1 - 2 * x - α| * u := by
        have ha_abs : |α| ≤ 1 := by rw [abs_of_pos hα0]; exact hα1.le
        have h1 : |(2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2 + (1 - 2 * x - α) * u| ≤
            |2 * x + 1 - α| * (k : ℝ) ^ 2 + |2 * x * (x + 1)| * k + x ^ 2 + |1 - 2 * x - α| * u := by
          have t1 := abs_add_le ((2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2) ((1 - 2 * x - α) * u)
          have t2 := abs_add_le ((2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k) (x ^ 2)
          have t3 := abs_add_le ((2 * x + 1 - α) * (k : ℝ) ^ 2) (2 * x * (x + 1) * k)
          rw [abs_mul, abs_of_nonneg hu] at t1
          rw [abs_of_nonneg (sq_nonneg x)] at t2
          rw [abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ)), abs_mul, abs_of_nonneg hk_pos.le] at t3
          linarith only [t1, t2, t3]
        have hk_le_k2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
        have h1_le_k2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
        have h2 : |2 * x * (x + 1)| * k ≤ |2 * x * (x + 1)| * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hk_le_k2 (abs_nonneg _)
        have h3 : x ^ 2 ≤ x ^ 2 * (k : ℝ) ^ 2 := by nlinarith only [sq_nonneg x, h1_le_k2]
        rw [abs_mul]
        calc |α| * |(2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2 + (1 - 2 * x - α) * u|
            ≤ 1 * (|2 * x + 1 - α| * (k : ℝ) ^ 2 + |2 * x * (x + 1)| * (k : ℝ) ^ 2 + x ^ 2 * (k : ℝ) ^ 2 +
                |1 - 2 * x - α| * u) :=
              mul_le_mul ha_abs (by linarith only [h1, h2, h3]) (abs_nonneg _) zero_le_one
          _ = (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2) * (k : ℝ) ^ 2 + |1 - 2 * x - α| * u := by ring
      have hden_1 : ((k : ℝ) ^ 2 * (k : ℝ) ^ 2 / 4) ≤ a₂ * a₁ := by
        have h_a2 : (k : ℝ) ^ 2 ≤ a₂ := by dsimp [a₂]; linarith only [hu]
        have hm := mul_le_mul h_a2 ha₁_lb0 (by positivity) (by positivity)
        linarith only [hm, show (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 / 4) = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 / 4 by ring]
      have hden_2 : a₂ * ((k : ℝ) ^ 2 / 4) ≤ a₂ * a₁ :=
        mul_le_mul_of_nonneg_left ha₁_lb0 ha₂_pos.le
      have hfrac1 : (k : ℝ) ^ 2 / (a₂ * a₁) ≤ 4 / (k : ℝ) ^ 2 := by
        calc (k : ℝ) ^ 2 / (a₂ * a₁)
            ≤ (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 * (k : ℝ) ^ 2 / 4) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_1
          _ = 4 / (k : ℝ) ^ 2 := by field_simp [hk_pos.ne']
      have hfrac2 : u / (a₂ * a₁) ≤ 4 / (k : ℝ) ^ 2 := by
        have hua : u ≤ a₂ := by dsimp [a₂]; linarith only [sq_nonneg (k : ℝ)]
        calc u / (a₂ * a₁)
            ≤ a₂ / (a₂ * ((k : ℝ) ^ 2 / 4)) :=
              div_le_div₀ ha₂_pos.le hua (by positivity) hden_2
          _ = 4 / (k : ℝ) ^ 2 := by field_simp [ha₂_pos.ne', hk_pos.ne']
      rw [hident, abs_div, abs_of_pos (mul_pos ha₂_pos ha₁_pos)]
      calc |α * ((2 * x + 1 - α) * (k : ℝ) ^ 2 + 2 * x * (x + 1) * k + x ^ 2 + (1 - 2 * x - α) * u)| / (a₂ * a₁)
          ≤ ((|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2) * (k : ℝ) ^ 2 + |1 - 2 * x - α| * u) / (a₂ * a₁) :=
            div_le_div_of_nonneg_right hnum_abs (mul_pos ha₂_pos ha₁_pos).le
        _ = (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2) * ((k : ℝ) ^ 2 / (a₂ * a₁)) +
              |1 - 2 * x - α| * (u / (a₂ * a₁)) := by ring
        _ ≤ (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2) * (4 / (k : ℝ) ^ 2) +
              |1 - 2 * x - α| * (4 / (k : ℝ) ^ 2) := by
            gcongr
        _ = 4 * (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2 + |1 - 2 * x - α|) / (k : ℝ) ^ 2 := by ring
    have htri : |α * Real.log (1 + h₂) - Real.log (1 + h₁)| ≤
        |α * h₂ - h₁| + α * (h₂ - Real.log (1 + h₂)) + (h₁ - Real.log (1 + h₁)) := by
      have h1 : α * Real.log (1 + h₂) - Real.log (1 + h₁) =
          (α * h₂ - h₁) + (h₁ - Real.log (1 + h₁)) - α * (h₂ - Real.log (1 + h₂)) := by ring
      rw [h1]
      have t1 := abs_sub ((α * h₂ - h₁) + (h₁ - Real.log (1 + h₁))) (α * (h₂ - Real.log (1 + h₂)))
      have t2 := abs_add_le (α * h₂ - h₁) (h₁ - Real.log (1 + h₁))
      rw [abs_of_nonneg (mul_nonneg hα0.le hl2_d0)] at t1
      rw [abs_of_nonneg hl1_d0] at t2
      linarith only [t1, t2]
    have h2_bd' : α * (h₂ - Real.log (1 + h₂)) ≤ 9 / (k : ℝ) ^ 2 := by
      nlinarith only [hα0, hl2_d, h2_sq]
    calc |α * Real.log (1 + h₂) - Real.log (1 + h₁)|
        ≤ 4 * (|2 * x + 1 - α| + |2 * x * (x + 1)| + x ^ 2 + |1 - 2 * x - α|) / (k : ℝ) ^ 2 +
            9 / (k : ℝ) ^ 2 + 256 / (k : ℝ) ^ 2 := by linarith only [htri, hlin_diff, h2_bd', hl1_d, h1_sq]
      _ = C_tail / (k : ℝ) ^ 2 := by dsimp [C_tail]; ring
      _ ≤ max C_tail (B₀ * (K₀ : ℝ) ^ 2) / (k : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

private lemma sum_Ico_sub_succ (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico 1 (n + 1), (f (k + 1) - f k) = f (n + 1) - f 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : 1 ≤ m
    · rw [Finset.sum_Ico_succ_top (by omega), ih hm]; ring
    · have hm0 : m = 0 := by omega
      subst hm0; simp

private lemma gamma_log_ratio_tendsto_zero {x α : ℝ} (hx : -(1 / 4 : ℝ) < x) (hα0 : 0 < α) (hα1 : α < 1) :
    Filter.Tendsto (gamma_g x α) Filter.atTop (nhds 0) := by
  rcases gamma_w_bound x α hx hα0 hα1 with ⟨C, hC0, hCbd⟩
  have hsum_inv : Summable (fun k : ℕ => 1 / ((k + 1 : ℝ) ^ 2)) := by
    have hs := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
    simpa [Function.comp_def, Nat.cast_succ] using hs
  have hsum_bd : Summable (fun k : ℕ => C / ((k + 1 : ℝ) ^ 2)) := by
    simpa [div_eq_mul_inv, one_div] using hsum_inv.mul_left C
  have hsum_w : ∀ u : ℝ, 0 ≤ u → Summable (fun k : ℕ => gamma_w x α (k + 1) u) := fun u hu => by
    refine Summable.of_norm_bounded hsum_bd fun k => ?_
    simpa [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using hCbd (k + 1) (by omega) u hu
  have hg_rep : ∀ u : ℝ, 0 < u →
      gamma_g x α u = (∑' k : ℕ, gamma_w x α (k + 1) u) +
        (Real.log (x ^ 2 + u) - Real.log ((x + α) ^ 2 + u)) +
        α * (Real.log (1 + u) - Real.log ((x + 1 / 2) ^ 2 + u)) := by
    intro u hu
    have hseq := gamma_log_ratio_seq_tendsto (x := x) (α := α) hu
    have hsum_part : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, gamma_w x α (k + 1) u)
        Filter.atTop (nhds (∑' k : ℕ, gamma_w x α (k + 1) u)) :=
      (hsum_w u hu.le).hasSum.tendsto_sum_nat
    have hrat_lim : Filter.Tendsto (fun n : ℕ => (((n + 1 : ℝ) ^ 2 + u) / (n : ℝ) ^ 2))
        Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ 2 + u * (1 / (n : ℝ)) ^ 2)
          Filter.atTop (nhds ((1 + 0) ^ 2 + u * 0 ^ 2)) := by
        have hinv : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_atTop_nhds_zero_nat
        exact ((tendsto_const_nhds.add hinv).pow 2).add ((hinv.pow 2).const_mul u)
      have hlim1 : (1 + (0 : ℝ)) ^ 2 + u * (0 : ℝ) ^ 2 = 1 := by norm_num
      rw [hlim1] at h1
      refine h1.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hn0]
    have hlog_lim : Filter.Tendsto (fun n : ℕ => α * Real.log (((n + 1 : ℝ) ^ 2 + u) / (n : ℝ) ^ 2))
        Filter.atTop (nhds 0) := by
      have ht := ((Real.continuousAt_log one_ne_zero).tendsto.comp hrat_lim).const_mul α
      simpa [Real.log_one] using ht
    have hcomb : Filter.Tendsto (fun n : ℕ => gamma_gN x α n u) Filter.atTop
        (nhds ((∑' k : ℕ, gamma_w x α (k + 1) u) +
          (Real.log (x ^ 2 + u) - Real.log ((x + α) ^ 2 + u)) +
          α * (Real.log (1 + u) - Real.log ((x + 1 / 2) ^ 2 + u)))) := by
      have htot := ((hsum_part.add_const (Real.log (x ^ 2 + u) - Real.log ((x + α) ^ 2 + u))).add_const
        (α * (Real.log (1 + u) - Real.log ((x + 1 / 2) ^ 2 + u)))).sub hlog_lim
      rw [sub_zero] at htot
      refine htot.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      have hsum_rng : ∑ k ∈ Finset.range (n + 1),
            (Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u)) =
          (Real.log (x ^ 2 + u) - Real.log ((x + α) ^ 2 + u)) +
            ∑ k ∈ Finset.Ico 1 (n + 1),
              (Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u)) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ n)]
        simp
      have htel := sum_Ico_sub_succ (fun k : ℕ => Real.log ((k : ℝ) ^ 2 + u)) n hn
      simp only [Nat.cast_add, Nat.cast_one, one_pow] at htel
      have hw_sum : ∑ k ∈ Finset.range n, gamma_w x α (k + 1) u =
          ∑ k ∈ Finset.Ico 1 (n + 1), gamma_w x α k u := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k => gamma_w x α k u) 0 n 1]
      have hw_exp : ∑ k ∈ Finset.Ico 1 (n + 1), gamma_w x α k u =
          (∑ k ∈ Finset.Ico 1 (n + 1),
            (Real.log ((x + k) ^ 2 + u) - Real.log ((x + α + k) ^ 2 + u))) +
          α * (Real.log ((n + 1 : ℝ) ^ 2 + u) - Real.log (1 + u)) := by
        simp only [gamma_w, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [htel]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hlog_diff : Real.log (((n + 1 : ℝ) ^ 2 + u) / (n : ℝ) ^ 2) =
          Real.log ((n + 1 : ℝ) ^ 2 + u) - 2 * Real.log n := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
        push_cast; ring
      dsimp [gamma_gN]
      rw [hsum_rng, hw_sum, hw_exp, hlog_diff]
      ring
    exact tendsto_nhds_unique hseq hcomb
  have hratio_lim : ∀ a b : ℝ,
      Filter.Tendsto (fun u : ℝ => Real.log ((a + u) / (b + u))) Filter.atTop (nhds 0) := by
    intro a b
    have h1 : Filter.Tendsto (fun u : ℝ => (a * u⁻¹ + 1) / (b * u⁻¹ + 1)) Filter.atTop (nhds 1) := by
      have hinv : Filter.Tendsto (fun u : ℝ => u⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      have ht := ((hinv.const_mul a).add_const 1).div ((hinv.const_mul b).add_const 1) (by norm_num)
      convert ht using 1
      · rfl
      · norm_num
    have h2 : Filter.Tendsto (fun u : ℝ => Real.log ((a * u⁻¹ + 1) / (b * u⁻¹ + 1)))
        Filter.atTop (nhds 0) := by
      have ht := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
      simpa only [Function.comp_def, Real.log_one] using ht
    refine h2.congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun u hu => ?_⟩
    have hu0 : u ≠ 0 := by linarith only [hu]
    congr 1; field_simp [hu0]
  have hlog_pair : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Filter.Tendsto (fun u : ℝ => Real.log (a + u) - Real.log (b + u)) Filter.atTop (nhds 0) := by
    intro a b ha hb
    refine (hratio_lim a b).congr' ?_
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun u hu => ?_⟩
    rw [Real.log_div (by linarith only [ha, hu]) (by linarith only [hb, hu])]
  have htsum_lim : Filter.Tendsto (fun u : ℝ => ∑' k : ℕ, gamma_w x α (k + 1) u) Filter.atTop (nhds 0) := by
    have h_zero : (0 : ℝ) = ∑' _ : ℕ, (0 : ℝ) := tsum_zero.symm
    rw [h_zero]
    refine tendsto_tsum_of_dominated_convergence (bound := fun k : ℕ => C / ((k + 1 : ℝ) ^ 2)) hsum_bd ?_ ?_
    · intro k
      have hp1 := hlog_pair ((x + (k + 1 : ℕ)) ^ 2) ((x + α + (k + 1 : ℕ)) ^ 2) (sq_nonneg _) (sq_nonneg _)
      have hp2 := hlog_pair (((k + 1 : ℕ) + 1 : ℝ) ^ 2) (((k + 1 : ℕ) : ℝ) ^ 2) (sq_nonneg _) (sq_nonneg _)
      have htot := hp1.add (hp2.const_mul α)
      rw [mul_zero, add_zero] at htot
      simpa [gamma_w, Nat.cast_add, Nat.cast_one] using htot
    · rw [Filter.eventually_atTop]
      refine ⟨0, fun u hu k => ?_⟩
      simpa [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using hCbd (k + 1) (by omega) u hu
  have htot := ((htsum_lim.add (hlog_pair (x ^ 2) ((x + α) ^ 2) (sq_nonneg _) (sq_nonneg _))).add
    ((hlog_pair 1 ((x + 1 / 2) ^ 2) zero_le_one (sq_nonneg _)).const_mul α))
  rw [add_zero, mul_zero, add_zero] at htot
  refine htot.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨1, fun u hu => ?_⟩
  exact (hg_rep u (by linarith only [hu])).symm

private noncomputable def gamma_f_der (x α : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  1 / ((x + k) ^ 2 + u) - 1 / ((x + α + k) ^ 2 + u)

private noncomputable def gamma_gN' (x α : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), gamma_f_der x α k u) - α / ((x + 1 / 2) ^ 2 + u)

private noncomputable def gamma_D (x α u : ℝ) : ℝ :=
  (∑' k : ℕ, gamma_f_der x α k u) - α / ((x + 1 / 2) ^ 2 + u)

private lemma gamma_f_der_summable {x α u : ℝ} (_hx : -(1 / 4 : ℝ) < x) (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 < u) :
    Summable (fun k : ℕ => gamma_f_der x α k u) := by
  set K₀ : ℕ := Nat.ceil (2 * |x| + 2) + 1
  have hK₀_ge : (2 * |x| + 2 : ℝ) ≤ K₀ := by
    have := Nat.le_ceil (2 * |x| + 2); dsimp [K₀]; push_cast; linarith only [this]
  set M : ℝ := max (2 / u * (K₀ : ℝ) ^ 2) 768
  have hsum_inv : Summable (fun k : ℕ => M / ((k + 1 : ℝ) ^ 2)) := by
    have hs := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hs.mul_left M
  refine Summable.of_norm_bounded hsum_inv fun k => ?_
  rw [Real.norm_eq_abs]
  by_cases hkK : k < K₀
  · have h1 : |gamma_f_der x α k u| ≤ 2 / u := by
      dsimp [gamma_f_der]
      have h1a : 0 ≤ 1 / ((x + k) ^ 2 + u) := by positivity
      have h1b : 1 / ((x + k) ^ 2 + u) ≤ 1 / u :=
        one_div_le_one_div_of_le hu (by linarith only [sq_nonneg (x + k)])
      have h2a : 0 ≤ 1 / ((x + α + k) ^ 2 + u) := by positivity
      have h2b : 1 / ((x + α + k) ^ 2 + u) ≤ 1 / u :=
        one_div_le_one_div_of_le hu (by linarith only [sq_nonneg (x + α + k)])
      have h12 : (1 : ℝ) / u ≤ 2 / u := div_le_div_of_nonneg_right (by norm_num) hu.le
      rw [abs_le]
      constructor <;> linarith only [h1a, h1b, h2a, h2b, h12]
    have h2 : 2 / u ≤ 2 / u * (K₀ : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : ((k + 1 : ℝ) ^ 2) ≤ (K₀ : ℝ) ^ 2 := by
        have hk1 : (k + 1 : ℝ) ≤ K₀ := by exact_mod_cast hkK
        nlinarith only [hk1]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    exact le_trans h1 (le_trans h2 (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  · have hk_ge : (K₀ : ℝ) ≤ k := by exact_mod_cast (le_of_not_gt hkK)
    have hk_pos : (0 : ℝ) < k := by linarith only [hk_ge, hK₀_ge, abs_nonneg x]
    have hxk_half : (k : ℝ) / 2 ≤ x + k := by
      have : -|x| ≤ x := neg_abs_le x; linarith only [this, hK₀_ge, hk_ge]
    have hxk_4 : (k + 1 : ℝ) / 4 ≤ x + k := by
      have : (1 : ℝ) ≤ k := by linarith only [hk_ge, hK₀_ge, abs_nonneg x]
      linarith only [hxk_half, this]
    have hnn_k : 0 ≤ gamma_f_der x α k u := by
      dsimp [gamma_f_der]
      have hsq : (x + k) ^ 2 ≤ (x + α + k) ^ 2 := by
        have : (0 : ℝ) ≤ x + k := by linarith only [hxk_half, hk_pos]
        nlinarith only [this, hα0]
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith only [hsq]))
    rw [abs_of_nonneg hnn_k]
    have hden1 : ((k + 1 : ℝ) ^ 2 / 16) ≤ (x + k) ^ 2 + u := by
      have : (k + 1 : ℝ) ^ 2 / 16 ≤ (x + k) ^ 2 := by nlinarith only [hxk_4]
      linarith only [this, hu]
    have hden2 : ((k + 1 : ℝ) ^ 2 / 16) ≤ (x + α + k) ^ 2 + u := by
      have : (k + 1 : ℝ) / 4 ≤ x + α + k := by linarith only [hxk_4, hα0]
      have h2 : (k + 1 : ℝ) ^ 2 / 16 ≤ (x + α + k) ^ 2 := by nlinarith only [this]
      linarith only [h2, hu]
    have hxk_ub : x + k ≤ 3 / 2 * k := by
      have : x ≤ |x| := le_abs_self x; linarith only [this, hK₀_ge, hk_ge]
    have hnum : α * (2 * x + 2 * k + α) ≤ 3 * (k + 1 : ℝ) := by
      have h1 : 2 * x + 2 * k + α ≤ 3 * (k : ℝ) + 1 := by linarith only [hxk_ub, hα1]
      have hnn : 0 ≤ 2 * x + 2 * k + α := by linarith only [hxk_4, hα0]
      nlinarith only [hα0, hα1, h1, hnn]
    have heq : gamma_f_der x α k u =
        α * (2 * x + 2 * k + α) / (((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u)) := by
      dsimp [gamma_f_der]
      field_simp [(by positivity : (x + k) ^ 2 + u ≠ 0), (by positivity : (x + α + k) ^ 2 + u ≠ 0)]
      ring
    rw [heq]
    have hden_prod : ((k + 1 : ℝ) ^ 4 / 256) ≤ ((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u) := by
      have hm := mul_le_mul hden1 hden2 (by positivity) (by positivity)
      linarith only [hm, show ((k + 1 : ℝ) ^ 2 / 16) * ((k + 1 : ℝ) ^ 2 / 16) = (k + 1 : ℝ) ^ 4 / 256 by ring]
    have h1 : α * (2 * x + 2 * k + α) / (((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u)) ≤
        3 * (k + 1 : ℝ) / ((k + 1 : ℝ) ^ 4 / 256) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden_prod
    have h2 : 3 * (k + 1 : ℝ) / ((k + 1 : ℝ) ^ 4 / 256) = 768 / ((k + 1 : ℝ) ^ 3) := by
      field_simp; ring
    have h3 : 768 / ((k + 1 : ℝ) ^ 3) ≤ 768 / ((k + 1 : ℝ) ^ 2) := by
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      have hk1 : (1 : ℝ) ≤ k + 1 := by linarith only [hk_pos]
      nlinarith only [hk1]
    exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))))

private lemma gamma_log_ratio_hasDerivAt {x α u₀ : ℝ} (_hx : -(1 / 4 : ℝ) < x) (hα0 : 0 < α)
    (hα1 : α < 1) (hu₀ : 0 < u₀) :
    HasDerivAt (gamma_g x α) (gamma_D x α u₀) u₀ := by
  let s : Set ℝ := Set.Ioo (u₀ / 2) (u₀ + 1)
  have hs_open : IsOpen s := isOpen_Ioo
  have hu₀_mem : u₀ ∈ s := ⟨by linarith only [hu₀], by linarith only [hu₀]⟩
  have hderiv_N : ∀ n : ℕ, ∀ u ∈ s, HasDerivAt (gamma_gN x α n) (gamma_gN' x α n u) u := by
    intro n u hu
    have hu_pos : 0 < u := lt_trans (by linarith only [hu₀]) hu.1
    have hsum_der : HasDerivAt
        (fun v : ℝ => ∑ k ∈ Finset.range (n + 1), (Real.log ((x + k) ^ 2 + v) - Real.log ((x + α + k) ^ 2 + v)))
        (∑ k ∈ Finset.range (n + 1), gamma_f_der x α k u) u := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have h1 : HasDerivAt (fun v : ℝ => (x + k) ^ 2 + v) 1 u :=
        ((hasDerivAt_id' u).const_add ((x + k) ^ 2)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun v : ℝ => (x + α + k) ^ 2 + v) 1 u :=
        ((hasDerivAt_id' u).const_add ((x + α + k) ^ 2)).congr_deriv (by ring)
      have hl1 := h1.log (by positivity : (x + k) ^ 2 + u ≠ 0)
      have hl2 := h2.log (by positivity : (x + α + k) ^ 2 + u ≠ 0)
      exact (hl1.fun_sub hl2).congr_deriv (by simp [gamma_f_der])
    have htail_der : HasDerivAt (fun v : ℝ => α * Real.log ((x + 1 / 2) ^ 2 + v))
        (α / ((x + 1 / 2) ^ 2 + u)) u := by
      have h1 : HasDerivAt (fun v : ℝ => (x + 1 / 2) ^ 2 + v) 1 u :=
        ((hasDerivAt_id' u).const_add ((x + 1 / 2) ^ 2)).congr_deriv (by ring)
      exact ((h1.log (by positivity : (x + 1 / 2) ^ 2 + u ≠ 0)).const_mul α).congr_deriv (by ring)
    exact ((hsum_der.const_add (2 * α * Real.log n)).fun_sub htail_der).congr_deriv (by simp [gamma_gN'])
  have hunif : TendstoLocallyUniformlyOn (gamma_gN' x α) (gamma_D x α) Filter.atTop s := by
    set K₀ : ℕ := Nat.ceil (2 * |x| + 2) + 1
    have hK₀_ge : (2 * |x| + 2 : ℝ) ≤ K₀ := by
      have := Nat.le_ceil (2 * |x| + 2); dsimp [K₀]; push_cast; linarith only [this]
    set M : ℝ := max (4 / u₀ * (K₀ : ℝ) ^ 2) 768
    have hsum_bd : Summable (fun k : ℕ => M / ((k + 1 : ℝ) ^ 2)) := by
      have hs := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
      simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hs.mul_left M
    have hnorm_bd : ∀ k : ℕ, ∀ u ∈ s, ‖gamma_f_der x α k u‖ ≤ M / ((k + 1 : ℝ) ^ 2) := by
      intro k u hu
      have hu_lb : u₀ / 2 < u := hu.1
      have hu_pos : 0 < u := lt_trans (by linarith only [hu₀]) hu_lb
      rw [Real.norm_eq_abs]
      by_cases hkK : k < K₀
      · have h1 : |gamma_f_der x α k u| ≤ 4 / u₀ := by
          dsimp [gamma_f_der]
          have h1a : 0 ≤ 1 / ((x + k) ^ 2 + u) := by positivity
          have h1b : 1 / ((x + k) ^ 2 + u) ≤ 1 / (u₀ / 2) :=
            one_div_le_one_div_of_le (by linarith only [hu₀]) (by linarith only [sq_nonneg (x + k), hu_lb])
          have h2a : 0 ≤ 1 / ((x + α + k) ^ 2 + u) := by positivity
          have h2b : 1 / ((x + α + k) ^ 2 + u) ≤ 1 / (u₀ / 2) :=
            one_div_le_one_div_of_le (by linarith only [hu₀]) (by linarith only [sq_nonneg (x + α + k), hu_lb])
          have h24 : (1 : ℝ) / (u₀ / 2) ≤ 4 / u₀ := by
            have : (1 : ℝ) / (u₀ / 2) = 2 / u₀ := by ring
            rw [this]
            exact div_le_div_of_nonneg_right (by norm_num) hu₀.le
          rw [abs_le]
          constructor <;> linarith only [h1a, h1b, h2a, h2b, h24]
        have h2 : 4 / u₀ ≤ 4 / u₀ * (K₀ : ℝ) ^ 2 / ((k + 1 : ℝ) ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          have hsq : (k + 1 : ℝ) ^ 2 ≤ (K₀ : ℝ) ^ 2 := by
            have hk1 : (k + 1 : ℝ) ≤ K₀ := by exact_mod_cast hkK
            nlinarith only [hk1]
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
        exact le_trans h1 (le_trans h2 (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
      · have hk_ge : (K₀ : ℝ) ≤ k := by exact_mod_cast (le_of_not_gt hkK)
        have hk_pos : (0 : ℝ) < k := by linarith only [hk_ge, hK₀_ge, abs_nonneg x]
        have hxk_half : (k : ℝ) / 2 ≤ x + k := by
          have : -|x| ≤ x := neg_abs_le x; linarith only [this, hK₀_ge, hk_ge]
        have hxk_4 : (k + 1 : ℝ) / 4 ≤ x + k := by
          have : (1 : ℝ) ≤ k := by linarith only [hk_ge, hK₀_ge, abs_nonneg x]
          linarith only [hxk_half, this]
        have hnn_k : 0 ≤ gamma_f_der x α k u := by
          dsimp [gamma_f_der]
          have hsq : (x + k) ^ 2 ≤ (x + α + k) ^ 2 := by
            have : (0 : ℝ) ≤ x + k := by linarith only [hxk_half, hk_pos]
            nlinarith only [this, hα0]
          exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith only [hsq]))
        rw [abs_of_nonneg hnn_k]
        have hden1 : ((k + 1 : ℝ) ^ 2 / 16) ≤ (x + k) ^ 2 + u := by
          have : (k + 1 : ℝ) ^ 2 / 16 ≤ (x + k) ^ 2 := by nlinarith only [hxk_4]
          linarith only [this, hu_pos]
        have hden2 : ((k + 1 : ℝ) ^ 2 / 16) ≤ (x + α + k) ^ 2 + u := by
          have : (k + 1 : ℝ) / 4 ≤ x + α + k := by linarith only [hxk_4, hα0]
          have h2 : (k + 1 : ℝ) ^ 2 / 16 ≤ (x + α + k) ^ 2 := by nlinarith only [this]
          linarith only [h2, hu_pos]
        have hxk_ub : x + k ≤ 3 / 2 * k := by
          have : x ≤ |x| := le_abs_self x; linarith only [this, hK₀_ge, hk_ge]
        have hnum : α * (2 * x + 2 * k + α) ≤ 3 * (k + 1 : ℝ) := by
          have h1 : 2 * x + 2 * k + α ≤ 3 * (k : ℝ) + 1 := by linarith only [hxk_ub, hα1]
          have hnn : 0 ≤ 2 * x + 2 * k + α := by linarith only [hxk_4, hα0]
          nlinarith only [hα0, hα1, h1, hnn]
        have heq : gamma_f_der x α k u =
            α * (2 * x + 2 * k + α) / (((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u)) := by
          dsimp [gamma_f_der]
          field_simp [(by positivity : (x + k) ^ 2 + u ≠ 0), (by positivity : (x + α + k) ^ 2 + u ≠ 0)]
          ring
        rw [heq]
        have hden_prod : ((k + 1 : ℝ) ^ 4 / 256) ≤ ((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u) := by
          have hm := mul_le_mul hden1 hden2 (by positivity) (by positivity)
          linarith only [hm, show ((k + 1 : ℝ) ^ 2 / 16) * ((k + 1 : ℝ) ^ 2 / 16) = (k + 1 : ℝ) ^ 4 / 256 by ring]
        have h1 : α * (2 * x + 2 * k + α) / (((x + k) ^ 2 + u) * ((x + α + k) ^ 2 + u)) ≤
            3 * (k + 1 : ℝ) / ((k + 1 : ℝ) ^ 4 / 256) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden_prod
        have h2 : 3 * (k + 1 : ℝ) / ((k + 1 : ℝ) ^ 4 / 256) = 768 / ((k + 1 : ℝ) ^ 3) := by
          field_simp; ring
        have h3 : 768 / ((k + 1 : ℝ) ^ 3) ≤ 768 / ((k + 1 : ℝ) ^ 2) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          have hk1 : (1 : ℝ) ≤ k + 1 := by linarith only [hk_pos]
          nlinarith only [hk1]
        exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3
          (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))))
    have ht_fin := tendstoUniformlyOn_tsum hsum_bd hnorm_bd
    have ht_nat : TendstoUniformlyOn (fun n : ℕ => fun u => ∑ k ∈ Finset.range (n + 1), gamma_f_der x α k u)
        (fun u => ∑' k : ℕ, gamma_f_der x α k u) Filter.atTop s := by
      rw [Metric.tendstoUniformlyOn_iff] at ht_fin ⊢
      intro ε hε
      exact (Filter.tendsto_finset_range.comp (Filter.tendsto_add_atTop_nat 1)).eventually (ht_fin ε hε)
    have ht_sub : TendstoUniformlyOn (gamma_gN' x α) (gamma_D x α) Filter.atTop s := by
      rw [Metric.tendstoUniformlyOn_iff] at ht_nat ⊢
      intro ε hε
      filter_upwards [ht_nat ε hε] with n hn u hu
      simpa [gamma_gN', gamma_D, Real.dist_eq, sub_sub_sub_cancel_right] using hn u hu
    exact ht_sub.tendstoLocallyUniformlyOn
  exact hasDerivAt_of_tendstoLocallyUniformlyOn hs_open hunif
    (Filter.Eventually.of_forall hderiv_N)
    (fun u hu => gamma_log_ratio_seq_tendsto (lt_trans (by linarith only [hu₀]) hu.1))
    hu₀_mem

private lemma gamma_D_nonneg {x α u : ℝ} (hy : 1 / 4 ≤ x + α / 2) (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 < u) :
    0 ≤ gamma_D x α u := by
  set y := x + α / 2
  set δ := α / 2
  have hx : -(1 / 4 : ℝ) < x := by dsimp [y] at hy; linarith only [hy, hα1]
  have hδ0 : 0 < δ := by dsimp [δ]; linarith only [hα0]
  have hδ1 : δ < 1 / 2 := by dsimp [δ]; linarith only [hα1]
  have hnn_der : ∀ k : ℕ, 0 ≤ gamma_f_der x α k u := fun k => by
    dsimp [gamma_f_der]
    have hsq : (x + k) ^ 2 ≤ (x + α + k) ^ 2 := by
      have hy_k : (0 : ℝ) ≤ x + α / 2 + k := by
        dsimp [y] at hy
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith only [hy, hk0]
      nlinarith only [hy_k, hα0]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith only [hsq]))
  let φ : ℕ → ℝ → ℝ := fun k t =>
    Real.exp (-u * t) * (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t))
  let ψ : ℝ → ℝ := fun t => 2 * δ * Real.exp (-((y + 1 / 2 - δ) ^ 2 + u) * t)
  have hφ_nn : ∀ k : ℕ, ∀ t > 0, 0 ≤ φ k t := fun k t ht => by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hwy : 0 ≤ y + (k : ℝ) := by dsimp [y] at hy ⊢; linarith only [hy, hk0]
    have hsq : (y + k - δ) ^ 2 ≤ (y + k + δ) ^ 2 := by nlinarith only [hwy, hδ0]
    have hexp : Real.exp (-(y + k + δ) ^ 2 * t) ≤ Real.exp (-(y + k - δ) ^ 2 * t) :=
      Real.exp_le_exp.mpr (by nlinarith only [hsq, ht])
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hexp)
  have hφ_int : ∀ k : ℕ, ∫ t in Set.Ioi (0 : ℝ), φ k t = gamma_f_der x α k u := by
    intro k
    have h1 : ∀ t : ℝ, φ k t =
        Real.exp (-((x + k) ^ 2 + u) * t) - Real.exp (-((x + α + k) ^ 2 + u) * t) := fun t => by
      have e1 : -u * t + -(y + k - δ) ^ 2 * t = -((x + k) ^ 2 + u) * t := by dsimp [y, δ]; ring
      have e2 : -u * t + -(y + k + δ) ^ 2 * t = -((x + α + k) ^ 2 + u) * t := by dsimp [y, δ]; ring
      dsimp [φ]; rw [mul_sub, ← Real.exp_add, ← Real.exp_add, e1, e2]
    simp_rw [h1]
    have hi1 := integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity) : -((x + k) ^ 2 + u) < 0) 0
    have hi2 := integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity) : -((x + α + k) ^ 2 + u) < 0) 0
    rw [MeasureTheory.integral_sub hi1 hi2,
      integral_Ioi_exp_neg (by positivity : 0 < (x + k) ^ 2 + u),
      integral_Ioi_exp_neg (by positivity : 0 < (x + α + k) ^ 2 + u)]
    simp [gamma_f_der, one_div]
  have hψ_int : ∫ t in Set.Ioi (0 : ℝ), ψ t = α / ((x + 1 / 2) ^ 2 + u) := by
    have heq : (fun t : ℝ => ψ t) = (fun t : ℝ => (2 * δ) * Real.exp (-((x + 1 / 2) ^ 2 + u) * t)) := by
      ext t; dsimp [ψ, y, δ]; congr 2; ring
    rw [heq, MeasureTheory.integral_const_mul,
      integral_Ioi_exp_neg (by positivity : 0 < (x + 1 / 2) ^ 2 + u)]
    dsimp [δ]; ring
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal (ψ t) ≤ ∑' k : ℕ, ENNReal.ofReal (φ k t) := by
    intro t ht
    have hsum_pt : Summable (fun k : ℕ => φ k t) := by
      have hp5 := (P5_gauss_bounds (y - 1 / 2) δ t hδ0 ht).1
      have hcon : Summable (fun k : ℕ => Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) :=
        hp5.congr fun k => by ring_nf
      exact hcon.mul_left (Real.exp (-u * t))
    have hgauss := gaussian_sum_ge hy hδ0 hδ1 ht
    have hexp_cmp : Real.exp (-(y + 1 / 2 - δ) ^ 2 * t) ≤ Real.exp (-y ^ 2 * t) := by
      apply Real.exp_le_exp.mpr
      have ht_pos : 0 < t := ht
      have h1 : y ≤ y + 1 / 2 - δ := by linarith only [hδ1]
      have h2 : y ^ 2 ≤ (y + 1 / 2 - δ) ^ 2 := by nlinarith only [hy, h1]
      nlinarith only [h2, ht_pos]
    have hmul1 : ψ t ≤ Real.exp (-u * t) * (2 * δ * Real.exp (-y ^ 2 * t)) := by
      have hψ_eq : ψ t = Real.exp (-u * t) * (2 * δ * Real.exp (-(y + 1 / 2 - δ) ^ 2 * t)) := by
        dsimp [ψ]
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [hψ_eq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_cmp (by positivity)) (Real.exp_pos _).le
    have hmul2 : Real.exp (-u * t) * (2 * δ * Real.exp (-y ^ 2 * t)) ≤ ∑' k : ℕ, φ k t := by
      have h1 := mul_le_mul_of_nonneg_left hgauss (Real.exp_pos (-u * t)).le
      have h2 : Real.exp (-u * t) * ∑' k : ℕ,
            (Real.exp (-(y + k - δ) ^ 2 * t) - Real.exp (-(y + k + δ) ^ 2 * t)) =
          ∑' k : ℕ, φ k t := by
        simpa [φ] using tsum_mul_left.symm
      linarith only [h1, h2]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hφ_nn k t ht) hsum_pt]
    exact ENNReal.ofReal_le_ofReal (le_trans hmul1 hmul2)
  have hlint := MeasureTheory.lintegral_mono_ae (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hlint_lhs : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (ψ t) = ENNReal.ofReal (α / ((x + 1 / 2) ^ 2 + u)) := by
    rw [← hψ_int, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity) : -((y + 1 / 2 - δ) ^ 2 + u) < 0) 0).const_mul (2 * δ)
    · exact Filter.Eventually.of_forall fun t => by dsimp [ψ]; positivity
  have hlint_rhs : ∫⁻ t in Set.Ioi (0 : ℝ), ∑' k : ℕ, ENNReal.ofReal (φ k t) =
      ENNReal.ofReal (∑' k : ℕ, gamma_f_der x α k u) := by
    rw [MeasureTheory.lintegral_tsum]
    · have hterm : ∀ k : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (φ k t) =
          ENNReal.ofReal (gamma_f_der x α k u) := by
        intro k
        rw [← hφ_int k, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
        · have hi1 := integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity) : -((x + k) ^ 2 + u) < 0) 0
          have hi2 := integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity) : -((x + α + k) ^ 2 + u) < 0) 0
          have heq : (fun t : ℝ => φ k t) = (fun t : ℝ =>
              Real.exp (-((x + k) ^ 2 + u) * t) - Real.exp (-((x + α + k) ^ 2 + u) * t)) := by
            ext t
            have e1 : -u * t + -(y + k - δ) ^ 2 * t = -((x + k) ^ 2 + u) * t := by dsimp [y, δ]; ring
            have e2 : -u * t + -(y + k + δ) ^ 2 * t = -((x + α + k) ^ 2 + u) * t := by dsimp [y, δ]; ring
            dsimp [φ]; rw [mul_sub, ← Real.exp_add, ← Real.exp_add, e1, e2]
          change Integrable (fun t : ℝ => φ k t) (volume.restrict (Set.Ioi 0))
          rw [heq]; exact hi1.sub hi2
        · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hφ_nn k t ht
      simp_rw [hterm]
      exact (ENNReal.ofReal_tsum_of_nonneg hnn_der (gamma_f_der_summable hx hα0 hα1 hu)).symm
    · intro k
      exact (Measurable.ennreal_ofReal (by dsimp [φ]; fun_prop)).aemeasurable
  rw [hlint_lhs, hlint_rhs] at hlint
  have hsum_nn : 0 ≤ ∑' k : ℕ, gamma_f_der x α k u := tsum_nonneg hnn_der
  have hle := (ENNReal.ofReal_le_ofReal_iff hsum_nn).mp hlint
  dsimp [gamma_D]
  linarith only [hle]

private lemma gamma_log_ratio_nonpos {x α u : ℝ} (hy : 1 / 4 ≤ x + α / 2) (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 < u) :
    gamma_g x α u ≤ 0 := by
  have hx : -(1 / 4 : ℝ) < x := by linarith only [hy, hα1]
  have hmono : MonotoneOn (gamma_g x α) (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · exact fun v hv => (gamma_log_ratio_hasDerivAt hx hα0 hα1 hv).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ioi] at hv
      exact (gamma_log_ratio_hasDerivAt hx hα0 hα1 hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ioi] at hv
      rw [(gamma_log_ratio_hasDerivAt hx hα0 hα1 hv).deriv]
      exact gamma_D_nonneg hy hα0 hα1 hv
  have htend := gamma_log_ratio_tendsto_zero hx hα0 hα1
  have hev : ∀ᶠ v in Filter.atTop, gamma_g x α u ≤ gamma_g x α v := by
    rw [Filter.eventually_atTop]
    exact ⟨u, fun v huv => hmono hu (lt_of_lt_of_le hu huv) huv⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev

private lemma gamma_ratio_le_of_im_ne_zero {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ}
    (hs_lo : -(1 / 2 : ℝ) < s.re) (hs_hi : s.re < 1 / 2) (him : s.im ≠ 0) :
    ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) / Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
      (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re) := by
  set x := Q / 2 + s.re / 2
  set τ := s.im / 2
  set α := 1 / 2 - s.re
  have hα0 : 0 < α := by dsimp [α]; linarith only [hs_hi]
  have hα1 : α < 1 := by dsimp [α]; linarith only [hs_lo]
  have hy : 1 / 4 ≤ x + α / 2 := by dsimp [x, α]; linarith only [hQ]
  have hτ_ne : τ ≠ 0 := by dsimp [τ]; exact div_ne_zero him two_ne_zero
  have hu : 0 < τ ^ 2 := sq_pos_of_ne_zero hτ_ne
  have hg_le := gamma_log_ratio_nonpos hy hα0 hα1 hu
  set b : ℂ := (Q : ℂ) / 2 + s / 2
  set a : ℂ := (Q : ℂ) / 2 + (1 - s) / 2
  have hb_eq : b = (x : ℂ) + (τ : ℂ) * Complex.I := by
    apply Complex.ext <;> (simp [b, x, τ]; try ring)
  have ha_conj_eq : starRingEnd ℂ a = ((x + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [a, Complex.conj_re, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re,
        Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        mul_one]
      dsimp [x, α]; ring
    · simp only [a, Complex.conj_im, Complex.add_im, Complex.div_ofNat_im, Complex.ofReal_im,
        Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, add_zero, zero_add]
      dsimp [τ]; ring
  have hnorm_rat : ‖Complex.Gamma a / Complex.Gamma b‖ =
      ‖Complex.Gamma (((x + α : ℝ) : ℂ) + (Real.sqrt (τ ^ 2) : ℂ) * Complex.I) /
        Complex.Gamma ((x : ℂ) + (Real.sqrt (τ ^ 2) : ℂ) * Complex.I)‖ := by
    have ha_n : ‖Complex.Gamma a‖ = ‖Complex.Gamma (starRingEnd ℂ a)‖ := by
      rw [Complex.Gamma_conj, Complex.norm_conj]
    rw [norm_div, norm_div, ha_n, ha_conj_eq, hb_eq]
    by_cases hτ0 : 0 ≤ τ
    · rw [Real.sqrt_sq hτ0]
    · have hτ_neg : τ < 0 := lt_of_not_ge hτ0
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hτ_neg]
      have hc1 : (((x + α : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) =
          starRingEnd ℂ (((x + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      have hc0 : ((x : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) = starRingEnd ℂ ((x : ℂ) + (τ : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [hc1, hc0, Complex.Gamma_conj, Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj]
  have hnorm_c : ‖(Q : ℂ) + 1 + s‖ / 2 = Real.sqrt ((x + 1 / 2) ^ 2 + τ ^ 2) := by
    have hc_eq : ((Q : ℂ) + 1 + s) / (2 : ℂ) = ((x + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
      apply Complex.ext <;> (simp [x, τ]; try ring)
    have hdiv : ‖(Q : ℂ) + 1 + s‖ / 2 = ‖((Q : ℂ) + 1 + s) / (2 : ℂ)‖ := by
      rw [norm_div]; norm_num
    rw [hdiv, hc_eq, ← Real.sqrt_sq (norm_nonneg _), c_re_add_im_normSq]
  have hsqrt_pos : 0 < Real.sqrt ((x + 1 / 2) ^ 2 + τ ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hlog_cmp : Real.log ‖Complex.Gamma a / Complex.Gamma b‖ ≤
      Real.log ((Real.sqrt ((x + 1 / 2) ^ 2 + τ ^ 2)) ^ α) := by
    rw [hnorm_rat, Real.log_rpow hsqrt_pos, Real.log_sqrt (by positivity)]
    have hg' : gamma_g x α (τ ^ 2) ≤ 0 := hg_le
    dsimp [gamma_g] at hg'
    linarith only [hg']
  have hrhs_pos : 0 < (Real.sqrt ((x + 1 / 2) ^ 2 + τ ^ 2)) ^ α :=
    Real.rpow_pos_of_pos hsqrt_pos α
  have hγb_ne : Complex.Gamma b ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him' := congrArg Complex.im hm
    simp only [hb_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.neg_im,
      Complex.natCast_im, neg_zero] at him'
    exact hτ_ne him'
  have hγa_ne : Complex.Gamma a ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre' := congrArg Complex.re hm
    have ha_re : a.re = x + α := by simp [a, x, α]; ring
    have ha_pos : 0 < a.re := by rw [ha_re]; linarith only [hy, hα0]
    simp only [Complex.neg_re, Complex.natCast_re] at hre'
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith only [ha_pos, hre', hm0]
  have hlhs_pos : 0 < ‖Complex.Gamma a / Complex.Gamma b‖ :=
    norm_pos_iff.mpr (div_ne_zero hγa_ne hγb_ne)
  rw [hnorm_c]
  exact (Real.log_le_log_iff hlhs_pos hrhs_pos).mp hlog_cmp

end SolGammaHelpers

theorem solution :
    ∀ Q : ℝ, 0 ≤ Q → ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re) := by
  intro Q hQ s hs_lo hs_hi
  set a : ℂ := (Q : ℂ) / 2 + (1 - s) / 2
  set b : ℂ := (Q : ℂ) / 2 + s / 2
  by_cases hs_eq_hi : s.re = 1 / 2
  · have ha_eq : starRingEnd ℂ a = b := by
      apply Complex.ext
      · simp only [a, b, Complex.conj_re, Complex.add_re, Complex.div_ofNat_re,
          Complex.ofReal_re, Complex.sub_re, Complex.one_re]
        linarith only [hs_eq_hi]
      · simp only [a, b, Complex.conj_im, Complex.add_im, Complex.div_ofNat_im,
          Complex.ofReal_im, Complex.sub_im, Complex.one_im]
        ring
    have ha_n : ‖Complex.Gamma a‖ = ‖Complex.Gamma b‖ := by
      calc ‖Complex.Gamma a‖ = ‖(starRingEnd ℂ) (Complex.Gamma a)‖ := (Complex.norm_conj _).symm
        _ = ‖Complex.Gamma (starRingEnd ℂ a)‖ := by rw [Complex.Gamma_conj]
        _ = ‖Complex.Gamma b‖ := by rw [ha_eq]
    rw [hs_eq_hi, sub_self, Real.rpow_zero, norm_div, ha_n]
    exact div_self_le_one ‖Complex.Gamma b‖
  · have hs_lt_hi : s.re < 1 / 2 := lt_of_le_of_ne hs_hi hs_eq_hi
    by_cases hs_eq_lo : s.re = -(1 / 2 : ℝ)
    · have ha_eq : starRingEnd ℂ a = b + 1 := by
        apply Complex.ext
        · simp only [a, b, Complex.conj_re, Complex.add_re, Complex.div_ofNat_re,
            Complex.ofReal_re, Complex.sub_re, Complex.one_re]
          linarith only [hs_eq_lo]
        · simp only [a, b, Complex.conj_im, Complex.add_im, Complex.div_ofNat_im,
            Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.one_im]
          ring
      have ha_n : ‖Complex.Gamma a‖ = ‖Complex.Gamma (b + 1)‖ := by
        calc ‖Complex.Gamma a‖ = ‖(starRingEnd ℂ) (Complex.Gamma a)‖ := (Complex.norm_conj _).symm
          _ = ‖Complex.Gamma (starRingEnd ℂ a)‖ := by rw [Complex.Gamma_conj]
          _ = ‖Complex.Gamma (b + 1)‖ := by rw [ha_eq]
      rw [hs_eq_lo, show (1 / 2 - -(1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one]
      by_cases hb0 : b = 0
      · simp [hb0, Complex.Gamma_zero]; positivity
      · have hγ1 : Complex.Gamma (b + 1) = b * Complex.Gamma b := Complex.Gamma_add_one b hb0
        rw [norm_div, ha_n, hγ1, norm_mul]
        have hle1 : ‖b‖ * ‖Complex.Gamma b‖ / ‖Complex.Gamma b‖ ≤ ‖b‖ := by
          by_cases hgb : ‖Complex.Gamma b‖ = 0
          · simp [hgb]
          · rw [mul_div_cancel_right₀ _ hgb]
        have hb_le : ‖b‖ ≤ ‖(Q : ℂ) + 1 + s‖ / 2 := by
          have hc_eq : ((Q : ℂ) + 1 + s) / (2 : ℂ) = b + (1 / 2 : ℂ) := by
            apply Complex.ext <;> (simp [b]; try ring)
          have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [← hn2, ← norm_div, hc_eq]
          have hsq : ‖b‖ ^ 2 ≤ ‖b + (1 / 2 : ℂ)‖ ^ 2 := by
            have h1 : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
              rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
            have h2 : ‖b + (1 / 2 : ℂ)‖ ^ 2 = (b.re + 1 / 2) ^ 2 + b.im ^ 2 := by
              rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
              simp only [Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.one_re,
                Complex.div_ofNat_im, Complex.one_im, zero_div, add_zero, sq]
            have hbre : -(1 / 4 : ℝ) ≤ b.re := by simp [b, hs_eq_lo]; linarith only [hQ]
            linarith only [h1, h2, show (b.re + 1 / 2) ^ 2 - b.re ^ 2 = b.re + 1 / 4 by ring, hbre]
          nlinarith only [hsq, norm_nonneg b, norm_nonneg (b + (1 / 2 : ℂ))]
        exact le_trans hle1 hb_le
    · have hs_gt_lo : -(1 / 2 : ℝ) < s.re := lt_of_le_of_ne hs_lo (Ne.symm hs_eq_lo)
      by_cases him : s.im ≠ 0
      · exact SolGammaHelpers.gamma_ratio_le_of_im_ne_zero hQ hs_gt_lo hs_lt_hi him
      · have him0 : s.im = 0 := not_ne_iff.mp him
        by_cases hb0 : b = 0
        · simp [hb0, Complex.Gamma_zero]; positivity
        · have hb_re : -(1 / 4 : ℝ) < b.re := by simp [b]; linarith only [hQ, hs_gt_lo]
          have hb_pole : ∀ m : ℕ, b ≠ -(m : ℂ) := by
            intro m hm
            rcases m with _ | m
            · simp only [Nat.cast_zero, neg_zero] at hm; exact hb0 hm
            · have hre := congrArg Complex.re hm
              simp only [Complex.neg_re, Complex.natCast_re] at hre
              have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
              linarith only [hb_re, hre, hm1]
          have ha_pole : ∀ m : ℕ, a ≠ -(m : ℂ) := by
            intro m hm
            have hre := congrArg Complex.re hm
            have hare : 0 < a.re := by simp [a]; linarith only [hQ, hs_lt_hi]
            simp only [Complex.neg_re, Complex.natCast_re] at hre
            have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            linarith only [hare, hre, hm0]
          let s_seq : ℕ → ℂ := fun n => ⟨s.re, 1 / ((n : ℝ) + 1)⟩
          have heq_s_seq : s_seq = fun n : ℕ => (s.re : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
            ext n; apply Complex.ext <;> simp only [s_seq, Complex.add_re, Complex.add_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
              Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
          have hs_eq : s = (s.re : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
            apply Complex.ext <;> simp [him0]
          have hinv : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have hs_seq_lim : Filter.Tendsto s_seq Filter.atTop (nhds s) := by
            rw [heq_s_seq]
            conv_rhs => rw [hs_eq]
            exact (tendsto_const_nhds (x := (s.re : ℂ))).add
              (((Complex.continuous_ofReal.tendsto 0).comp hinv).mul_const Complex.I)
          have ha_seq_lim : Filter.Tendsto (fun n : ℕ => (Q : ℂ) / 2 + (1 - s_seq n) / 2)
              Filter.atTop (nhds a) := by
            exact tendsto_const_nhds.add ((tendsto_const_nhds.sub hs_seq_lim).div_const 2)
          have hb_seq_lim : Filter.Tendsto (fun n : ℕ => (Q : ℂ) / 2 + s_seq n / 2)
              Filter.atTop (nhds b) := by
            exact tendsto_const_nhds.add (hs_seq_lim.div_const 2)
          have hlhs_lim : Filter.Tendsto
              (fun n : ℕ => ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s_seq n) / 2) /
                Complex.Gamma ((Q : ℂ) / 2 + s_seq n / 2)‖)
              Filter.atTop (nhds ‖Complex.Gamma a / Complex.Gamma b‖) := by
            have hga := (Complex.continuousAt_Gamma a ha_pole).tendsto.comp ha_seq_lim
            have hgb := (Complex.continuousAt_Gamma b hb_pole).tendsto.comp hb_seq_lim
            exact (hga.div hgb (Complex.Gamma_ne_zero hb_pole)).norm
          have hrhs_lim : Filter.Tendsto
              (fun n : ℕ => (‖(Q : ℂ) + 1 + s_seq n‖ / 2) ^ (1 / 2 - s.re))
              Filter.atTop (nhds ((‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re))) := by
            have hc : Filter.Tendsto (fun n : ℕ => ‖(Q : ℂ) + 1 + s_seq n‖ / 2)
                Filter.atTop (nhds (‖(Q : ℂ) + 1 + s‖ / 2)) :=
              (((tendsto_const_nhds (x := (Q : ℂ) + 1)).add hs_seq_lim).norm).div_const 2
            exact hc.rpow tendsto_const_nhds (Or.inr (by linarith only [hs_lt_hi]))
          have hpt : ∀ n : ℕ,
              ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s_seq n) / 2) /
                Complex.Gamma ((Q : ℂ) / 2 + s_seq n / 2)‖ ≤
                (‖(Q : ℂ) + 1 + s_seq n‖ / 2) ^ (1 / 2 - s.re) := by
            intro n
            have him_ne : (s_seq n).im ≠ 0 := by
              simp only [s_seq]
              exact one_div_ne_zero (by positivity)
            simpa [s_seq] using SolGammaHelpers.gamma_ratio_le_of_im_ne_zero hQ (s := s_seq n)
              (by simpa [s_seq] using hs_gt_lo) (by simpa [s_seq] using hs_lt_hi) him_ne
          exact le_of_tendsto_of_tendsto hlhs_lim hrhs_lim (Filter.Eventually.of_forall hpt)
