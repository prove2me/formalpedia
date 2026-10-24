-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_collision_determinant_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:49:06.918007+00:00
-- url     : https://prove2.me/submissions/bc9e1b2f-b526-43bd-bb0c-2c1232fb2bcb

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_translated_cauchy_determinant_bound
import Theorems.Thm_OAI_PiExponent_MinorTranslationData_periodMonomial_coeff_eq_cauchy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

-- Only the two general analytic/algebraic interfaces above are child obligations.
-- All quantitative specialization, including the logarithmic remainder, is proved here.

private lemma tc_exp_norm (b h : ℂ) (q : ℕ) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖b * Complex.exp (h * z) * z ^ q‖ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ q := by
  simp only [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
    exact (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by
        simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg h)))
  · exact pow_le_pow_left₀ (norm_nonneg z) hz q
  · positivity
  · exact pow_nonneg hR q

private lemma tc_exp_budget (b h : ℂ) (q N : ℕ)
    {z : ℂ} {R H w0 wstar : ℝ} (hR : 1 ≤ R) (hH : 0 ≤ H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hz : ‖z‖ ≤ R)
    (hb : ‖b‖ ≤ (2 : ℝ) ^ N) (hh : ‖h‖ ≤ H / w0)
    (hq : q ≤ N) (hN : (N : ℝ) ≤ H / wstar) :
    ‖b * Complex.exp (h * z) * z ^ q‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have h2R : 0 < 2 * R := by positivity
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ q := tc_exp_norm b h q hR0 hz
    _ ≤ (2 : ℝ) ^ N * Real.exp ((H / w0) * R) * R ^ N := by
      apply mul_le_mul
      · exact mul_le_mul hb
          (Real.exp_le_exp.mpr (mul_le_mul hh le_rfl hR0 (div_nonneg hH hw0.le)))
          (Real.exp_pos _).le (by positivity)
      · exact pow_le_pow_right₀ hR hq
      · positivity
      · positivity
    _ = Real.exp ((H / w0) * R + (N : ℝ) * Real.log (2 * R)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h2R, mul_pow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn := mul_le_mul_of_nonneg_right hN hlog
      calc
        _ ≤ (H / w0) * R + (H / wstar) * Real.log (2 * R) := add_le_add le_rfl hn
        _ = _ := by ring

private lemma tc_column_norm {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * h + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        Complex.exp ((h : ℂ) * z) * z ^ (∑ i, (a i - A i))‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hwpos (i : Fin m) : 0 ≤ w i := hws.le.trans (hw i)
  have hs0 : 0 ≤ ∑ i, w i * (a i : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hh : ‖(h : ℂ)‖ ≤ H / w0 := by
    rw [Complex.norm_natCast, le_div_iff₀ hw0]
    nlinarith
  have htot : ((∑ i, a i : ℕ) : ℝ) ≤ H / wstar := by
    rw [le_div_iff₀ hws]
    have hs : wstar * ∑ i, (a i : ℝ) ≤ ∑ i, w i * (a i : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hcast : ((∑ i, a i : ℕ) : ℝ) = ∑ i, (a i : ℝ) := by
      simp only [Nat.cast_sum]
    rw [hcast]
    have hh0 : 0 ≤ w0 * (h : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
    nlinarith
  have hb : ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤
      (2 : ℝ) ^ (∑ i, a i) := by
    rw [Complex.norm_natCast]
    have hn : (∏ i, (a i).choose (A i) : ℕ) ≤ 2 ^ (∑ i, a i) := by
      calc
        _ ≤ ∏ i, 2 ^ a i := Finset.prod_le_prod
          (fun i _ => Nat.zero_le _) (fun i _ => Nat.choose_le_two_pow _ _)
        _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    exact_mod_cast hn
  exact tc_exp_budget _ _ _ _ hR hH hw0 hws hz hb hh
    (Finset.sum_le_sum fun i _ => Nat.sub_le _ _) htot

private noncomputable def tc_ratio : ℝ := Real.exp (-Real.log 2 / 2)

private lemma tc_ratio_pos : 0 < tc_ratio := Real.exp_pos _

private lemma tc_ratio_lt_one : tc_ratio < 1 := by
  unfold tc_ratio
  apply Real.exp_lt_one_iff.mpr
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

private lemma tc_ratio_square : tc_ratio * tc_ratio = 1 / 2 := by
  unfold tc_ratio
  rw [← Real.exp_add]
  have he : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
  rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
  simp only [one_div]

private lemma tc_factorial (M : ℕ) :
    (M.factorial : ℝ) ≤ Real.exp ((M : ℝ) * Real.log M) := by
  by_cases hM : M = 0
  · subst M
    norm_num
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hM)]
    exact_mod_cast Nat.factorial_le_pow M

private lemma tc_pair_count {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) :
    2 * ((∑ a, (multiplicity group a).choose 2 : ℕ) : ℝ) =
      (∑ a, (multiplicity group a : ℝ) ^ 2) - Fintype.card ι := by
  classical
  have hnat : (∑ a, multiplicity group a) = Fintype.card ι := by
    simpa only [OAI.PiExponent.MinorTranslationData.multiplicity, Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset κ))
        (f := group) (by intro i _; exact Finset.mem_univ (group i))).symm
  have hsum : (∑ a, (multiplicity group a : ℝ)) = Fintype.card ι := by
    exact_mod_cast hnat
  push_cast
  rw [Finset.mul_sum]
  calc
    _ = ∑ a, ((multiplicity group a : ℝ) ^ 2 - (multiplicity group a : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Nat.cast_choose_two]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, hsum]

private lemma tc_normalize (M C ell : ℕ) {H A v S : ℝ} (hH : 0 < H)
    (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    (((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
        tc_ratio ^ C * ((1 - tc_ratio)⁻¹) ^ M) ≤
      Real.exp (-(Real.log 2 / 4) * S +
        (M : ℝ) * H * (A + Real.log 2 / v + remainder M H)) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hr : 0 < 1 - tc_ratio := sub_pos.mpr tc_ratio_lt_one
  have ht : (2 : ℝ) ^ ell ≤ Real.exp ((M : ℝ) * H / v * Real.log 2) := by
    calc
      _ = Real.exp ((ell : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hell hlog2)
  have hraw :
      (((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
        tc_ratio ^ C * ((1 - tc_ratio)⁻¹) ^ M) ≤
      Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
        (M : ℝ) * (Real.log M + Real.log 2 / 4 - Real.log (1 - tc_ratio))) := by
    calc
      _ ≤ (Real.exp ((M : ℝ) * Real.log M) * (Real.exp (H * A)) ^ M *
            Real.exp ((M : ℝ) * H / v * Real.log 2)) *
            tc_ratio ^ C * ((1 - tc_ratio)⁻¹) ^ M := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hr.le) M)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg tc_ratio_pos.le C)
        apply mul_le_mul _ ht (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (tc_factorial M) (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, tc_ratio, ← Real.exp_nat_mul]
        have hi : (1 - Real.exp (-Real.log 2 / 2))⁻¹ =
            Real.exp (-Real.log (1 - tc_ratio)) := by
          rw [Real.exp_neg, Real.exp_log hr]
          rfl
        rw [hi, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        congr 1
        have hc : (C : ℝ) = (S - M) / 2 := by linarith
        rw [hc]
        unfold tc_ratio
        ring
  have he :
      -(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v + remainder M H) =
      -(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
        (M : ℝ) * (Real.log M + Real.log 2 / 4 - Real.log (1 - tc_ratio)) := by
    unfold remainder
    change _ = _ + (M : ℝ) *
      (Real.log M + Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)))
    have hcancel : H * ((Real.log M + Real.log 2 / 4 -
        Real.log (1 - Real.exp (-Real.log 2 / 2))) / H) =
        Real.log M + Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)) :=
      mul_div_cancel₀ _ hH.ne'
    calc
      _ = -(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
          (M : ℝ) * (H * ((Real.log M + Real.log 2 / 4 -
            Real.log (1 - Real.exp (-Real.log 2 / 2))) / H)) := by ring
      _ = _ := by rw [hcancel]
  rw [he]
  exact hraw

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (multiplicity (fun r : Row d H => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + remainder (actualRowCount d H) H)) := by
  classical
  have hwEq (i : Fin d.m) : fixedWeights d i = d.x (i.val + 1) := by
    change (Nat.ceil (Real.log (d.q i.val)) : ℝ) = d.x (i.val + 1)
    exact (d.x_log i.val).symm
  have hwp (i : Fin d.m) : 0 < fixedWeights d i := by
    rw [hwEq]
    exact zero_lt_one.trans_le (d.x_one_le _)
  have hwl (i : Fin d.m) : d.wstar ≤ fixedWeights d i := by
    rw [hwEq]
    exact d.wstar_lower i
  have horder (r : Row d H) : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    have hr := (Finset.mem_filter.mp r.2.2).2
    change (∑ i : Fin (d.m + 1),
      InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i *
        (r.2.1 i : ℝ)) < H at hr
    rw [Fin.sum_univ_succ] at hr
    simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ] at hr
    have hs : 0 ≤ ∑ i : Fin d.m,
        (fixedWeights d i / (d.base.theta : ℝ)) * (r.2.1 i.succ : ℝ) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (div_nonneg (hwp i).le d.base.theta_pos.le) (Nat.cast_nonneg _)
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith
  have hcol (c : Row d H) :
      (d.w0 : ℝ) * ((selection c).1 0 : ℝ) +
        ∑ i, fixedWeights d i * ((selection c).1 i.succ : ℝ) ≤ H := by
    have hc := (Finset.mem_filter.mp (selection c).2).2
    change (∑ i : Fin (d.m + 1),
      InterpolationMatrix.columnWeights d.w0 (fixedWeights d) i *
        ((selection c).1 i : ℝ)) ≤ H at hc
    simpa only [Fin.sum_univ_succ, InterpolationMatrix.columnWeights,
      Fin.cases_zero, Fin.cases_succ] using hc
  let ell : Row d H → ℕ := fun r => r.2.1 0 - ((f r).2.2 : ℕ)
  have hell : ((∑ r, ell r : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ))
          (horder r)
      _ = _ := by simp; ring
  let R : NNReal := ⟨100 * (d.K : ℝ), by positivity⟩
  have hK : 0 < d.K := Nat.zero_lt_one.trans_le d.K_pos
  have hK1 : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hR : 0 < R := by change (0 : ℝ) < 100 * d.K; positivity
  have hR1 : (1 : ℝ) ≤ R := by change (1 : ℝ) ≤ 100 * d.K; linarith
  let AA : ℝ := (R : ℝ) / (d.w0 : ℝ) + Real.log (2 * (R : ℝ)) / d.wstar
  let F : Transverse d H → Row d H → ℂ → ℂ := fun A c z =>
    ((∏ i, ((selection c).1 i.succ).choose (A.1 i) : ℕ) : ℂ) *
      Complex.exp (((selection c).1 0 : ℂ) * z) *
      z ^ (∑ i : Fin d.m, ((selection c).1 i.succ - A.1 i))
  have hF : ∀ A c, Differentiable ℂ (F A c) := by
    intro A c
    dsimp [F]
    exact ((Complex.differentiable_exp.comp
      (differentiable_id.const_mul _)).const_mul _).mul (differentiable_id.pow _)
  have hFD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖F A c z‖ ≤ Real.exp (H * AA) := by
    intro A c z hz
    exact tc_column_norm ((selection c).1 0) (fun i => (selection c).1 i.succ)
      A.1 (fixedWeights d) hR1 hH.le d.w0_pos d.wstar_pos hwl (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le)
  have hcenter (r : Row d H) :
      ‖(r.1.val : ℂ) * period‖ + 3 / 4 ≤ (R : ℝ) / 2 := by
    have hjK : (r.1.val : ℝ) ≤ d.K := by exact_mod_cast r.1.isLt.le
    have hn : ‖(r.1.val : ℂ) * period‖ = (r.1.val : ℝ) * (2 * Real.pi) := by
      simp [period, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hn]
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
    have hp : (r.1.val : ℝ) * (2 * Real.pi) ≤ (d.K : ℝ) * 8 :=
      mul_le_mul hjK hpi (by positivity) (by positivity)
    change (r.1.val : ℝ) * (2 * Real.pi) + 3 / 4 ≤ (100 * (d.K : ℝ)) / 2
    linarith
  have hb := OAI.PiExponent.AnalyticCollision.translated_cauchy_determinant_bound
    (fun r : Row d H => (f r).1) F (fun r => (r.1.val : ℂ) * period) ell
    R hR (Real.exp (H * AA)) tc_ratio (Real.exp_pos _).le
    tc_ratio_pos.le tc_ratio_lt_one tc_ratio_square hF hFD hcenter
  have hm :
      choiceMatrix d selection f =
        (fun r c => cauchyPowerSeries
          (fun t : ℂ => F (f r).1 c ((r.1.val : ℂ) * period + Complex.log (1 + t)))
          0 (1 / 2) (ell r) (fun _ => (1 : ℂ))) := by
    funext r c
    exact periodMonomial_coeff_eq_cauchy r.1.val ((selection c).1 0) (ell r)
      (fun i => (selection c).1 i.succ) (f r).1.1
  rw [← hm] at hb
  have hb' := hb.trans (tc_normalize (Fintype.card (Row d H))
    (∑ A : Transverse d H, (multiplicity (fun r : Row d H => (f r).1) A).choose 2)
    (∑ r, ell r) hH hell (tc_pair_count (fun r : Row d H => (f r).1)))
  have hAA : AA + Real.log 2 / (d.v0 : ℝ) = d.holomorphicError := by
    change 100 * (d.K : ℝ) / (d.w0 : ℝ) +
        Real.log (2 * (100 * (d.K : ℝ))) / d.wstar + Real.log 2 / (d.v0 : ℝ) =
      100 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
        Real.log (200 * (d.K : ℝ)) / d.wstar
    have he : (2 : ℝ) * (100 * d.K) = 200 * d.K := by ring
    rw [he]
    ring
  rw [hAA] at hb'
  simpa only [actualRowCount] using hb'
