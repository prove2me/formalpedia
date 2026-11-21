-- Prove2me | solution 1 for NymanBeurling.fixed_damping_shifted_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:46:33.396112+00:00
-- url     : https://prove2.me/submissions/5946d753-3b5d-4b21-9914-0d79f2131ff9

import Mathlib
import Definitions.Def_NymanBeurling_DampedResidualLimits
import Theorems.Thm_NymanBeurling_fixed_damping_bounded_energy_implies_shifted_zero_free

/-
The discrete Mellin transform and its Cauchy–Schwarz bounds follow the
Prove2Me proof of NymanBeurling.finite_remainder_zero_obstruction
(submission 657705dd, Codex-kr). The Abel continuation and fixed-damping
converse are separate arguments below.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped BigOperators

namespace NymanBeurling.FixedDampingBoundary

noncomputable section

-- Evaluate the discrete Mellin transform on the nth interval, indexed from one.
private def pval (s : ℂ) (m : ℕ) : ℂ := (m : ℂ) ^ (-s)
private def jump (s : ℂ) (n : ℕ) : ℂ := pval s (n+1) - pval s (n+2)
private def remainder (k m : ℕ) : ℂ := ((m % k : ℕ) : ℂ) / k

private theorem jump_estimate {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖jump s n‖ ≤ ‖s‖ * (n+1 : ℝ)^(-s.re-1) := by
  let a := (n+1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs' : -s ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hs)
  have hd (x : ℝ) (hx : x ∈ Icc a (a+1)) :=
    (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha hx.1).ne' hs').hasDerivWithinAt (s := Icc a (a+1))
  have hb (x : ℝ) (hx : x ∈ Ico a (a+1)) :
      ‖(-s) * (x:ℂ)^(-s-1)‖ ≤ ‖s‖ * a^(-s.re-1) := by
    rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hx.1)]
    simp only [sub_re,neg_re,one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (a+1) (show a+1 ∈ Icc a (a+1) by constructor <;> linarith)
  rw [norm_sub_rev] at h
  norm_num [jump,pval,a,Nat.cast_add,add_assoc] at h ⊢
  exact h

private theorem sum_rpow (a : ℝ) (ha : a < -1) :
    Summable (fun n : ℕ => (n+1 : ℝ)^a) := by
  simpa using (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr ha)

private theorem remainder_bound {k : ℕ} (hk : 0 < k) (m : ℕ) : ‖remainder k m‖ ≤ 1 := by
  have h := Nat.mod_lt m hk
  simp only [remainder,norm_div,Complex.norm_natCast]
  exact (div_le_one (by positivity)).mpr (by exact_mod_cast h.le)

private theorem bounded_jump_summable {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => g n * jump s n) := by
  apply Summable.of_norm_bounded ((sum_rpow _ (by linarith : -s.re-1 < -1)).mul_left (B*‖s‖))
  intro n
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (hg n) (jump_estimate hs n) (norm_nonneg _) ((norm_nonneg _).trans (hg n))

private theorem jump_series_analytic {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B) :
    AnalyticOnNhd ℂ (fun s => ∑' n, g n * jump s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let U := {w : ℂ | s.re / 2 < w.re ∧ ‖w‖ < ‖s‖ + 1}
  have hopen : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := ⟨by linarith,by linarith⟩
  have hdb (n : ℕ) : DifferentiableOn ℂ (fun w => g n * jump w n) U := by
    unfold jump pval
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.sub
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+1 ≠ 0)))
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+2 ≠ 0)))
  apply (Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => g n * jump w n)
    ((sum_rpow _ (by linarith : -(s.re / 2)-1 < -1)).mul_left (B*(‖s‖+1))) hdb hopen _).analyticOnNhd hopen s hsU
  intro n w hw
  have hw' : s.re/2 < w.re ∧ ‖w‖ < ‖s‖+1 := hw
  rw [norm_mul,mul_assoc]
  apply mul_le_mul (hg n) _ (norm_nonneg _) ((norm_nonneg _).trans (hg n))
  apply (jump_estimate (by linarith : 0 < w.re) n).trans
  exact mul_le_mul hw'.2.le (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith))
    (by positivity) (by positivity)

private theorem remainder_step {k : ℕ} (hk : 0 < k) (m : ℕ) :
    remainder k (m+1) - remainder k m = (k : ℂ)⁻¹ - (if k ∣ m+1 then 1 else 0) := by
  have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hr (j : ℕ) : remainder k j = (j:ℂ)/k - ((j/k:ℕ):ℂ) := by
    have h : ((j % k : ℕ):ℂ) + (k:ℂ) * ((j/k:ℕ):ℂ) = (j:ℂ) := by exact_mod_cast Nat.mod_add_div j k
    unfold remainder
    field_simp
    linear_combination h
  rw [hr,hr,Nat.succ_div]
  split_ifs <;> push_cast <;> ring

private theorem pval_hasSum {s : ℂ} (hs : 1 < s.re) : HasSum (pval s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  apply ((Complex.summable_one_div_nat_cpow.mpr hs).hasSum).congr_fun
  intro n
  simp [pval,Complex.cpow_neg,one_div]

private theorem multiple_hasSum {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => if k ∣ m then pval s m else 0) (pval s k * riemannZeta s) := by
  have hi : Injective (fun n : ℕ => k*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hk h
  apply (hi.hasSum_iff (fun x hx => by
    have h : ¬ k ∣ x := fun ⟨y,hy⟩ => hx ⟨y,hy.symm⟩
    simp [h])).mp
  apply ((pval_hasSum hs).mul_left (pval s k)).congr_fun
  intro n
  simp only [Function.comp_apply,dvd_mul_right,if_true,pval,Nat.cast_mul]
  exact (Complex.mul_cpow_ofReal_nonneg (a := k) (b := n) (by positivity) (by positivity) (-s))

private theorem remainder_dirichlet {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (remainder k (n+1) - remainder k n) * pval s (n+1))
      (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
  let f (m : ℕ) := (k:ℂ)⁻¹ * pval s m - (if k ∣ m then pval s m else 0)
  have hs' : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h : HasSum f (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    rw [sub_mul]
    exact ((pval_hasSum hs).mul_left (k:ℂ)⁻¹).sub (multiple_hasSum hk hs)
  have h0 : f 0 = 0 := by simp [f,pval,Complex.zero_cpow (neg_ne_zero.mpr hs')]
  have h' : HasSum (fun n => f (n+1)) (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    simpa [h0] using (hasSum_nat_add_iff' 1).mpr h
  apply h'.congr_fun
  intro n
  rw [remainder_step hk, sub_mul]
  dsimp [f]; split_ifs <;> simp

private theorem initial_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  have hq := (summable_nat_add_iff 1).mpr (pval_hasSum hs).summable
  have hb (d : ℕ) : Summable (fun n : ℕ => remainder k (n+d) * pval s (n+1)) := by
    apply Summable.of_norm_bounded hq.norm
    intro n
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (remainder_bound hk (n+d)) (norm_nonneg (pval s (n+1)))
  have h0 : Summable (fun n : ℕ => remainder k n * pval s (n+1)) := by simpa using hb 0
  have h1 := hb 1
  have hshift := h0.tsum_eq_zero_add
  simp only [remainder, Nat.zero_mod,Nat.cast_zero,zero_div,zero_mul,zero_add] at hshift
  rw [← (remainder_dirichlet hk hs).tsum_eq]
  simp only [jump,mul_sub,sub_mul]
  rw [h1.tsum_sub ((summable_nat_add_iff 1).mpr h0), h1.tsum_sub h0]
  exact congrArg _ hshift.symm

-- Remove the pole of zeta at one before applying uniqueness on the connected half-plane.
private theorem remainder_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  let U := {z : ℂ | 0 < z.re}
  let G (z : ℂ) := ∑' n, remainder k (n+1) * jump z n
  let C (z : ℂ) := (k:ℂ)⁻¹ - pval z k
  have hG : AnalyticOnNhd ℂ G U := jump_series_analytic (fun n => remainder_bound hk (n+1))
  have hC : Differentiable ℂ C := by
    intro z
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast hk.ne')))
  have ha : AnalyticOnNhd ℂ (fun z => (z-1) * G z) U := (analyticOnNhd_id.sub analyticOnNhd_const).mul hG
  have hb : AnalyticOnNhd ℂ (fun z => C z * riemannZeta₁ z) U :=
    (hC.mul differentiable_riemannZeta₁).differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re)
  have he (z : ℂ) (hz : 1 < z.re) : (z-1) * G z = C z * riemannZeta₁ z := by
    have hz' : z ≠ 1 := by intro h; simp [h] at hz
    dsimp [G,C]
    rw [initial_transform hk hz,riemannZeta_eq_inv_sub_mul hz']
    field_simp
  have htwo : (2:ℂ) ∈ U := by change 0 < (2:ℂ).re; norm_num
  have h := ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_halfSpace_re_gt 0).isPreconnected htwo
    (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ) < (2:ℂ).re by norm_num)) he)
    (show s ∈ U from hs)
  change G s = C s * riemannZeta s
  rw [riemannZeta_eq_inv_sub_mul h1]
  have hne := sub_ne_zero.mpr h1
  field_simp
  linear_combination h

private theorem pval_zero {s : ℂ} (hs : 0 < s.re) : Tendsto (fun n => pval s (n+1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  apply h'.congr
  intro n
  simp only [Function.comp_apply,pval]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (x := (n+1:ℕ)) (by positivity) (-s)).symm

private theorem jump_one {s : ℂ} (hs : 0 < s.re) : HasSum (jump s) 1 := by
  have hsum : Summable (jump s) := by simpa using (bounded_jump_summable (g := fun _ => 1) (B := 1) (by simp) hs)
  apply hsum.hasSum_iff_tendsto_nat.mpr
  have htel (N : ℕ) : ∑ n ∈ Finset.range N, jump s n = 1 - pval s (N+1) := by
    induction N with
    | zero => simp [pval]
    | succ N ih => rw [Finset.sum_range_succ,ih]; dsimp [jump]; ring
  simp_rw [htel]
  simpa using (tendsto_const_nhds (x := (1:ℂ))).sub (pval_zero hs)

private def wt (n : ℕ) : ℝ := (n+1 : ℝ)*(n+2 : ℝ)

private theorem weight_pos (n : ℕ) : 0 < wt n := by unfold wt; positivity


private theorem integral_rpow_product_sq {a b p q : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hp : p ≤ 0) (hq : q ≤ 0) :
    (∫ x : ℝ in a..b, x^(p+q))^2 ≤ (∫ x : ℝ in a..b, x^(p+p)) * ∫ x : ℝ in a..b, x^(q+q) := by
  let μ := volume.restrict (Ioc a b)
  have hnon (r : ℝ) : 0 ≤ᵐ[μ] (fun x : ℝ => x^r) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc a b))] with x hx
    exact Real.rpow_nonneg (ha.trans hx.1).le _
  have hmem (r : ℝ) (hr : r ≤ 0) : MemLp (fun x : ℝ => x^r) (ENNReal.ofReal 2) μ := by
    apply MemLp.mono_measure (volume.restrict_mono_set Ioc_subset_Icc_self)
    apply AntitoneOn.memLp_isCompact isCompact_Icc
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (ha.trans_le hx.1) hxy hr
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (hnon p) (hnon q) (hmem p hp) (hmem q hq)
  have hsum (r t : ℝ) : (∫ x : ℝ, x ^ r * x ^ t ∂μ) = ∫ x in a..b, x^(r+t) := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc a b))] with x hx
    exact (Real.rpow_add (ha.trans hx.1) r t).symm
  simp only [Real.rpow_two,sq,hsum,←Real.sqrt_eq_rpow] at h
  have hn (r : ℝ) : 0 ≤ ∫ x : ℝ in a..b, x^r :=
    intervalIntegral.integral_nonneg hab fun x hx => Real.rpow_nonneg (ha.trans_le hx.1).le _
  simpa only [mul_pow,Real.sq_sqrt (hn _)] using pow_le_pow_left₀ (hn _) h 2

private theorem sharp_interval {a b : ℝ} (ha : 0 < a) (hab : a < b) {s : ℂ} (hs : 1/2 < s.re) :
    (2*s.re-1) * (a*b/(b-a)) * ‖(a:ℂ)^(-s) - (b:ℂ)^(-s)‖^2 ≤
      ‖s‖^2 * (a^(1-2*s.re) - b^(1-2*s.re)) := by
  have hb : 0 < b := ha.trans hab
  have haway : (0:ℝ) ∉ uIcc a b := by rw [uIcc_of_le hab.le]; exact fun h => (not_le.mpr ha) h.1
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hz : (a:ℂ)^(-s) - (b:ℂ)^(-s) = s * ∫ x : ℝ in a..b, (x:ℂ)^(-s-1) := by
    rw [integral_cpow (Or.inr ⟨by intro h; apply hs0; linear_combination -h,haway⟩)]
    simp only [sub_add_cancel]
    field_simp
    ring
  let I (r : ℝ) := ∫ x : ℝ in a..b, x^r
  have hn (r : ℝ) : 0 ≤ I r :=
    intervalIntegral.integral_nonneg hab.le fun x hx => Real.rpow_nonneg (ha.trans_le hx.1).le _
  have he : (∫ x : ℝ in a..b, ‖(x:ℂ)^(-s-1)‖) = I (-1 + -s.re) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    dsimp only
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    simp [sub_eq_add_neg,add_comm]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x : ℝ => (x:ℂ)^(-s-1)) hab.le
  rw [he] at hnorm
  have hc : I (-1 + -s.re)^2 ≤ I (-2) * I (-2*s.re) := by
    dsimp [I]
    convert integral_rpow_product_sq (p := -1) (q := -s.re) ha hab.le (by norm_num) (by linarith) using 1; ring_nf
  have hA : I (-2) = (b-a)/(a*b) := by
    dsimp [I]
    rw [integral_rpow (Or.inr ⟨by norm_num,haway⟩)]
    norm_num [Real.rpow_neg_one]
    field_simp
    ring
  have hB : I (-2*s.re) = (a^(1-2*s.re) - b^(1-2*s.re))/(2*s.re-1) := by
    dsimp [I]
    rw [integral_rpow (Or.inr ⟨by linarith,haway⟩)]
    rw [show -2*s.re+1 = 1-2*s.re by ring]
    rw [show 1-2*s.re = -(2*s.re-1) by ring, div_neg, ← neg_div, neg_sub]
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hc
  rw [hA,hB] at hsq
  rw [hz,norm_mul,mul_pow]
  have hpos : 0 < 2*s.re-1 := by linarith
  have hba : 0 < b-a := by linarith
  rw [show ∀ v : ℝ, (2*s.re-1)*(a*b/(b-a))*(‖s‖^2*v) = ‖s‖^2*((2*s.re-1)*(a*b/(b-a))*v) from fun _ => by ring]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ (2*s.re-1)*(a*b/(b-a))*(((b-a)/(a*b))*((a^(1-2*s.re)-b^(1-2*s.re))/(2*s.re-1))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by field_simp [hpos.ne',hba.ne',ha.ne',hb.ne']

private theorem dual_energy {s : ℂ} (hs : 1/2 < s.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, wt n * ‖jump s n‖^2 ≤ ‖s‖^2 / (2*s.re-1) := by
  let u (n : ℕ) := (n+1:ℝ)^(1-2*s.re)
  have hpos : 0 < 2*s.re-1 := by linarith
  have hx (n : ℕ) : (2*s.re-1) * (wt n * ‖jump s n‖^2) ≤ ‖s‖^2*(u n-u (n+1)) := by
    have h := sharp_interval (a := (n+1:ℝ)) (b := (n+2:ℝ)) (by positivity) (by linarith) hs
    have hd : (n+2:ℝ) - (n+1:ℝ) = 1 := by ring
    simpa only [jump,pval,wt,u,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Complex.ofReal_add,Complex.ofReal_one,
      Complex.ofReal_natCast,Complex.ofReal_ofNat,hd,div_one,mul_assoc,add_assoc,one_add_one_eq_two] using h
  have htel : ∑ n ∈ Finset.range N, (u n-u (n+1)) = u 0 - u N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih]; ring
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hx n)
  rw [←Finset.mul_sum,←Finset.mul_sum,htel] at h
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm]
  apply h.trans
  have h0 : 0 ≤ u N := by dsimp [u]; positivity
  simp only [u,Nat.cast_zero,zero_add,Real.one_rpow] at h0 ⊢
  nlinarith [mul_nonneg (sq_nonneg ‖s‖) h0]

private theorem energy_inequality (g h : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, g n * h n‖^2 ≤
      (∑ n ∈ Finset.range N, ‖g n‖^2/wt n) * ∑ n ∈ Finset.range N, wt n * ‖h n‖^2 := by
  let a (n : ℕ) := ‖g n‖ / Real.sqrt (wt n)
  let b (n : ℕ) := Real.sqrt (wt n) * ‖h n‖
  have hw (n : ℕ) : Real.sqrt (wt n) ≠ 0 := (Real.sqrt_pos.mpr (weight_pos n)).ne'
  have hab (n : ℕ) : ‖g n * h n‖ = a n * b n := by rw [norm_mul]; dsimp [a,b]; field_simp [hw n]
  have ha (n : ℕ) : a n ^ 2 = ‖g n‖^2/wt n := by dsimp [a]; rw [div_pow,Real.sq_sqrt (weight_pos _).le]
  have hb (n : ℕ) : b n ^ 2 = wt n * ‖h n‖^2 := by dsimp [b]; rw [mul_pow,Real.sq_sqrt (weight_pos _).le]
  have hnorm := norm_sum_le (Finset.range N) (fun n => g n * h n)
  simp_rw [hab] at hnorm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) a b
  simp_rw [ha,hb] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs


private def dampedCoeff (ε : ℝ) (k : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (k + 2) : ℝ) / ((k + 2 : ℕ) : ℝ) ^ ε

private def partialMobius (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (ArithmeticFunction.moebius (n + 1) : ℂ) * pval s (n + 1)

private lemma residual_ofReal (N : ℕ) (ε : ℝ) (n : ℕ) :
    (NymanBeurling.dampedResidualFinite N ε (n+1) : ℂ) =
      1 - ∑ k ∈ Finset.range N, (-(dampedCoeff ε k : ℂ)) * remainder (k+2) (n+1) := by
  let f (k : ℕ) : ℝ := ((ArithmeticFunction.moebius (k+2) : ℝ) / (k+2 : ℝ)^ε) *
    (((n+1)%(k+2) : ℕ) : ℝ) / (k+2 : ℝ)
  have hf : dampedResidualFinite N ε (n+1) = 1 + ∑ k ∈ Finset.range N, f k := by
    unfold dampedResidualFinite
    exact congrArg (fun z : ℝ ↦ 1 + z) (Fin.sum_univ_eq_sum_range f N)
  rw [hf, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_one]
  simp only [neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold dampedCoeff remainder
  dsimp only [f]
  push_cast
  ring

private lemma coeff_pow (ε : ℝ) (k : ℕ) :
    (dampedCoeff ε k : ℂ) =
      (ArithmeticFunction.moebius (k+2) : ℂ) * pval (ε : ℂ) (k+2) := by
  unfold dampedCoeff pval
  rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity), Complex.cpow_neg, div_eq_mul_inv]
  push_cast
  rfl

private lemma damped_multiplier (N : ℕ) (ε : ℝ) (s : ℂ) :
    (∑ k ∈ Finset.range N,
       (-(dampedCoeff ε k : ℂ)) * ((((k+2:ℕ):ℂ))⁻¹ - pval s (k+2))) =
      partialMobius (N+1) (s+(ε:ℂ)) - partialMobius (N+1) (1+(ε:ℂ)) := by
  simp only [partialMobius, Finset.sum_range_succ']
  have hOne (w : ℂ) :
      (ArithmeticFunction.moebius (0 + 1) : ℂ) * pval w (0 + 1) = 1 := by
    simp [pval]
  simp only [hOne]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coeff_pow]
  have hkk : k + 1 + 1 = k + 2 := by omega
  simp only [hkk]
  let d : ℂ := ((k + 2 : ℕ) : ℂ)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (by omega : k + 2 ≠ 0)
  dsimp only [pval]
  change -((ArithmeticFunction.moebius (k+2) : ℂ) * d ^ (-(ε:ℂ))) *
       (d⁻¹ - d^(-s)) =
    (ArithmeticFunction.moebius (k+2) : ℂ) * d^(-(s+(ε:ℂ))) -
    (ArithmeticFunction.moebius (k+2) : ℂ) * d^(-(1+(ε:ℂ)))
  simp only [neg_add, Complex.cpow_add _ _ hd, Complex.cpow_neg_one]
  ring

private lemma finite_damped_moment_hasSum (N : ℕ) (ε : ℝ) {s : ℂ}
    (hs : 1/2 < s.re) (h1 : s ≠ 1) :
    HasSum (fun n : ℕ ↦ (dampedResidualFinite N ε (n+1) : ℂ) * jump s n)
      (1 - (partialMobius (N+1) (s+(ε:ℂ)) -
        partialMobius (N+1) (1+(ε:ℂ))) * riemannZeta s) := by
  have hσ : 0 < s.re := by linarith
  let c (k : ℕ) := -(dampedCoeff ε k : ℂ)
  have hkernel (k : ℕ) :
      HasSum (fun n : ℕ ↦ remainder (k+2) (n+1) * jump s n)
        (((((k+2 : ℕ) : ℂ))⁻¹ - pval s (k+2)) * riemannZeta s) := by
    have h := bounded_jump_summable (fun n ↦ remainder_bound (by omega : 0 < k+2) (n+1)) hσ
    simpa only [remainder_transform (by omega : 0 < k+2) hσ h1] using h.hasSum
  have hlin := hasSum_sum (s := Finset.range N) (fun k _ ↦ (hkernel k).mul_left (c k))
  have hsum := (jump_one hσ).sub hlin
  have hmult : (∑ k ∈ Finset.range N,
       c k * (((((k+2 : ℕ) : ℂ))⁻¹ - pval s (k+2)) * riemannZeta s)) =
       (partialMobius (N+1) (s+(ε:ℂ)) - partialMobius (N+1) (1+(ε:ℂ))) * riemannZeta s := by
    simp only [← mul_assoc, ← Finset.sum_mul, c, damped_multiplier]
  rw [hmult] at hsum
  have heq : (fun n : ℕ ↦ (dampedResidualFinite N ε (n+1) : ℂ) * jump s n) =
      fun n ↦ jump s n - ∑ k ∈ Finset.range N, c k * (remainder (k+2) (n+1) * jump s n) := by
    funext n
    rw [residual_ofReal N ε n, sub_mul, Finset.sum_mul]
    simp only [one_mul, mul_assoc, c]
  rw [heq]
  exact hsum

private lemma finite_damped_moment_sq_le (N : ℕ) (ε : ℝ) {s : ℂ}
    (hs : 1/2 < s.re) (h1 : s ≠ 1)
    {B : ℝ} (hB : ∀ H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B) :
    ‖1 - (partialMobius (N+1) (s+(ε:ℂ)) -
        partialMobius (N+1) (1+(ε:ℂ))) * riemannZeta s‖ ^ 2 ≤ B * (‖s‖ ^ 2 / (2*s.re-1)) := by
  let g (n : ℕ) := (dampedResidualFinite N ε (n+1) : ℂ)
  have hlim := (finite_damped_moment_hasSum N ε hs h1).tendsto_sum_nat.norm.pow 2
  have hB' : ∀ H, (∑ n ∈ Finset.range H, ‖g n‖^2 / wt n) ≤ B := by
    intro H
    simpa [wt, g, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hB H
  have hnon : 0 ≤ B := by simpa using hB 0
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro H
  exact (energy_inequality g (jump s) H).trans
    (mul_le_mul (hB' H) (dual_energy hs H)
      (Finset.sum_nonneg fun n _ ↦ mul_nonneg (weight_pos n).le (sq_nonneg _)) hnon)


private lemma partialMobius_tendsto {w : ℂ} (hw : 1 < w.re) :
    Tendsto (fun N ↦ partialMobius N w) atTop
      (𝓝 (LSeries (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) w)) := by
  let f : ℕ → ℂ := fun d ↦ (ArithmeticFunction.moebius d : ℂ)
  have hS : Summable (LSeries.term f w) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hw
  have hTail := (summable_nat_add_iff (f := LSeries.term f w) 1).mpr hS
  have hsum : (∑' n : ℕ, LSeries.term f w (n+1)) = LSeries f w := by
    change _ = ∑' n, LSeries.term f w n
    rw [hS.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hterm (n : ℕ) :
      LSeries.term f w (n+1) = (ArithmeticFunction.moebius (n+1) : ℂ) * pval w (n+1) := by
    rw [LSeries.term_of_ne_zero (by omega : n + 1 ≠ 0), pval, Complex.cpow_neg, div_eq_mul_inv]
  have h := hTail.hasSum.tendsto_sum_nat
  rw [hsum] at h
  simpa only [hterm, partialMobius] using h

private lemma shifted_partialMobius_bounded (ε : ℝ) (hε : 0 < ε) {s : ℂ}
    (hs : 1/2 < s.re) (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0)
    {B : ℝ} (hB : ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B) :
    ∃ M : ℝ, ∀ N : ℕ, ‖partialMobius N (s+(ε:ℂ))‖ ≤ M := by
  let w := (1 + (ε : ℂ))
  have hw : 1 < w.re := by simp [w, hε]
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ (partialMobius_tendsto hw)).exists_norm_le
  let C := Real.sqrt (B * (‖s‖ ^ 2 / (2*s.re-1)))
  let M := D + (1+C) / ‖riemannZeta s‖
  have hD' (N : ℕ) : ‖partialMobius N w‖ ≤ D := hD _ (mem_range_self N)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD' 0)
  have hM : 0 ≤ M := add_nonneg hD0 (div_nonneg (by positivity) (norm_nonneg _))
  refine ⟨M, fun N ↦ ?_⟩
  cases N with
  | zero => simpa [partialMobius] using hM
  | succ N =>
    let S := partialMobius (N+1) (s+(ε:ℂ))
    let L := partialMobius (N+1) w
    let z := riemannZeta s
    have he : ‖1 - (S-L)*z‖ ≤ C :=
      Real.le_sqrt_of_sq_le (finite_damped_moment_sq_le N ε hs h1 (hB N))
    have hmul : ‖(S-L)*z‖ ≤ 1+C := by
      calc
        _ = ‖1 - (1 - (S-L)*z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖(1:ℂ)‖+‖1 - (S-L)*z‖ := norm_sub_le _ _
        _ ≤ 1+C := by simpa using add_le_add_left he 1
    rw [norm_mul] at hmul
    have hSL : ‖S-L‖ ≤ (1+C)/‖z‖ := (le_div_iff₀ (norm_pos_iff.mpr hz)).mpr hmul
    calc
      ‖S‖ = ‖(S-L)+L‖ := by rw [sub_add_cancel]
      _ ≤ ‖S-L‖+‖L‖ := norm_add_le _ _
      _ ≤ M := by
        dsimp only [M, z] at *
        linarith [hD' (N+1)]

private def abelMobius (w₀ w : ℂ) : ℂ :=
  ∑' n : ℕ, partialMobius (n+1) w₀ * jump (w-w₀) n

private lemma abelMobius_analytic {w₀ : ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialMobius n w₀‖ ≤ M) :
    AnalyticOnNhd ℂ (abelMobius w₀) {w : ℂ | w₀.re < w.re} := by
  intro w hw
  have hRe : w-w₀ ∈ {z : ℂ | 0 < z.re} := by
    change w₀.re < w.re at hw
    simpa [sub_re, sub_pos] using hw
  let F (r : ℂ) := ∑' n : ℕ, partialMobius (n+1) w₀ * jump r n
  have hF : AnalyticAt ℂ F (w-w₀) :=
    jump_series_analytic (fun n ↦ hM (n+1)) _ hRe
  have hShift : AnalyticAt ℂ (fun z : ℂ ↦ z - w₀) w := analyticAt_id.sub analyticAt_const
  exact AnalyticAt.comp (f := fun z : ℂ ↦ z - w₀) (g := F) (x := w) hF hShift

private lemma partialMobius_tendsto_abelMobius {w₀ w : ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialMobius n w₀‖ ≤ M)
    (hw₀ : w₀.re < w.re) :
    Tendsto (fun N ↦ partialMobius N w) atTop (𝓝 (abelMobius w₀ w)) := by
  let r := w-w₀
  have hr : 0 < r.re := by change 0 < w.re - w₀.re; exact sub_pos.mpr hw₀
  have hb : Summable (fun n : ℕ ↦ partialMobius (n+1) w₀ * jump r n) :=
    bounded_jump_summable (fun n ↦ hM (n+1)) hr
  have htel (N : ℕ) :
      (∑ n ∈ Finset.range N, partialMobius (n+1) w₀ * jump r n) =
        partialMobius N w - partialMobius N w₀ * pval r (N+1) := by
    induction N with
    | zero => simp [partialMobius]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hm (x : ℂ) : partialMobius (N+1) x = partialMobius N x +
          (ArithmeticFunction.moebius (N+1) : ℂ) * pval x (N+1) := by
        unfold partialMobius
        rw [Finset.sum_range_succ]
      have hp : pval w₀ (N+1) * pval r (N+1) = pval w (N+1) := by
        unfold pval
        have hd : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N + 1 ≠ 0)
        rw [← Complex.cpow_add _ _ hd, show -w₀ + -r = -w by dsimp [r]; ring]
      simp only [jump, hm]
      calc
        _ = (partialMobius N w - (partialMobius N w₀ +
            (ArithmeticFunction.moebius (N+1) : ℂ)*pval w₀ (N+1))*pval r (N+2)) +
              (ArithmeticFunction.moebius (N+1) : ℂ) *
                (pval w₀ (N+1) * pval r (N+1)) := by ring
        _ = _ := by rw [hp]; ring
  have htail : Tendsto (fun N ↦ partialMobius N w₀ * pval r (N+1)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := ((pval_zero hr).norm.const_mul M)
    simp only [norm_zero, mul_zero] at h
    apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) _ h
    exact Eventually.of_forall (fun N ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM N) (norm_nonneg _))
  have hlim := hb.hasSum.tendsto_sum_nat
  simp_rw [htel] at hlim
  simpa only [sub_add_cancel, add_zero, abelMobius] using hlim.add htail

private lemma abelMobius_eq_LSeries {w₀ w : ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialMobius n w₀‖ ≤ M) (hw : 1 < w.re) (hw₀ : w₀.re < w.re) :
    abelMobius w₀ w = LSeries (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) w :=
  tendsto_nhds_unique (partialMobius_tendsto_abelMobius hM hw₀) (partialMobius_tendsto hw)

private lemma abelMobius_mul_regularizedZeta {w₀ : ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialMobius n w₀‖ ≤ M) {w : ℂ} (hw : w₀.re < w.re) :
    abelMobius w₀ w * riemannZeta₁ w = w - 1 := by
  let U := {z : ℂ | w₀.re < z.re}
  let D := {z : ℂ | max w₀.re 1 < z.re}
  let G := abelMobius w₀
  have hG : AnalyticOnNhd ℂ G U := abelMobius_analytic hM
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ U :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re)
  have ha : AnalyticOnNhd ℂ (fun z => G z * riemannZeta₁ z) U := hG.mul hZ
  have hc : AnalyticOnNhd ℂ (fun z : ℂ => z-1) U := analyticOnNhd_id.sub analyticOnNhd_const
  have hEq (z : ℂ) (hz : z ∈ D) : G z * riemannZeta₁ z = z-1 := by
    have hz' : max w₀.re 1 < z.re := hz
    have hz₀ : w₀.re < z.re := (le_max_left _ _).trans_lt hz'
    have hz₁ : 1 < z.re := (le_max_right _ _).trans_lt hz'
    have hne : z ≠ 1 := by intro he; simp [he] at hz₁
    have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz₁
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz₁, ← abelMobius_eq_LSeries hM hz₁ hz₀] at hprod
    change riemannZeta z * G z = 1 at hprod
    rw [riemannZeta_eq_inv_sub_mul hne] at hprod
    field_simp at hprod
    simpa only [mul_comm] using hprod
  let b : ℂ := (max w₀.re 1 + 1 : ℝ)
  have hbD : b ∈ D := by change max w₀.re 1 < ((max w₀.re 1 + 1 : ℝ) : ℂ).re; simp
  have hbU : b ∈ U := by
    change w₀.re < b.re
    exact (le_max_left _ _).trans_lt (show max w₀.re 1 < b.re from hbD)
  have hOpen : IsOpen D := isOpen_lt continuous_const continuous_re
  have h := ha.eqOn_of_preconnected_of_eventuallyEq hc (convex_halfSpace_re_gt w₀.re).isPreconnected hbU
    (eventuallyEq_of_mem (hOpen.mem_nhds hbD) hEq) (show w ∈ U from hw)
  exact h

private lemma abelMobius_eq_inv_zeta {w₀ w : ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialMobius n w₀‖ ≤ M) (hw : w₀.re < w.re) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) :
    abelMobius w₀ w = (riemannZeta w)⁻¹ := by
  have h := abelMobius_mul_regularizedZeta hM hw
  have hζ : riemannZeta₁ w = (w - 1) * riemannZeta w := by
    rw [riemannZeta_eq_inv_sub_mul h1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h1), one_mul]
  rw [hζ, ← mul_assoc, mul_right_comm] at h
  have h := (mul_right_cancel₀ (sub_ne_zero.mpr h1)) (h.trans (one_mul _).symm)
  calc
    abelMobius w₀ w = abelMobius w₀ w * 1 := (mul_one _).symm
    _ = abelMobius w₀ w * (riemannZeta w * (riemannZeta w)⁻¹) := by rw [mul_inv_cancel₀ hz]
    _ = (riemannZeta w)⁻¹ := by rw [← mul_assoc, h, one_mul]

private lemma exists_zeta_nonzero_in_re_interval {a b : ℝ} (hab : a < b) (hb : b ≤ 1) :
    ∃ s : ℂ, a < s.re ∧ s.re < b ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  by_contra! hNo
  let U := {z : ℂ | a < z.re ∧ z.re < b}
  let c : ℂ := ((a+b)/2 : ℝ)
  have hOpen : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hc : c ∈ U := by
    change a < (((a+b)/2 : ℝ):ℂ).re ∧ (((a+b)/2 : ℝ):ℂ).re < b
    simp only [Complex.ofReal_re]
    constructor <;> linarith
  have hNear : riemannZeta₁ =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hOpen.mem_nhds hc] with s hs
    have hs' : a < s.re ∧ s.re < b := hs
    have h1 : s ≠ 1 := by
      intro h
      have hl := hs'.2.trans_le hb
      simp [h] at hl
    have hz := hNo s hs'.1 hs'.2 h1
    rw [riemannZeta_eq_inv_sub_mul h1, mul_eq_zero] at hz
    exact hz.resolve_left (inv_ne_zero (sub_ne_zero.mpr h1))
  have hA : AnalyticOnNhd ℂ riemannZeta₁ univ :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ
  have hEq := hA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_univ (mem_univ c) hNear (mem_univ (1 : ℂ))
  simp [riemannZeta₁_one] at hEq

open Asymptotics

private def referenceMobius (ε : ℝ) : ℂ :=
  LSeries (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) (1 + (ε : ℂ))

private lemma limiting_mellin_sq_le (ε : ℝ) (hε : 0 < ε)
    {B : ℝ} (hB : ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B)
    {s : ℂ} (hs : 1/2 < s.re) (h1 : s ≠ 1) (hw1 : s+(ε:ℂ) ≠ 1) :
    ‖1 - ((riemannZeta (s+(ε:ℂ)))⁻¹ - referenceMobius ε) * riemannZeta s‖ ^ 2 ≤
      B * (‖s‖ ^ 2 / (2*s.re-1)) := by
  let b := min 1 s.re
  have hb : (1/2 : ℝ) < b := lt_min (by norm_num) hs
  obtain ⟨r, hr, hrb, hr1, hζr⟩ := exists_zeta_nonzero_in_re_interval hb (min_le_left _ _)
  obtain ⟨M, hM⟩ := shifted_partialMobius_bounded ε hε hr hr1 hζr hB
  have hw : (r+(ε:ℂ)).re < (s+(ε:ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, add_lt_add_iff_right]
    exact hrb.trans_le (min_le_right _ _)
  have hζw := NymanBeurling.fixed_damping_bounded_energy_implies_shifted_zero_free
    ε hε ⟨B, hB⟩ (s+(ε:ℂ))
      (by simpa only [Complex.add_re, Complex.ofReal_re, add_lt_add_iff_right] using hs) hw1
  have hlim := partialMobius_tendsto_abelMobius hM hw
  rw [abelMobius_eq_inv_zeta hM hw hw1 hζw] at hlim
  have h₁ := hlim.comp (tendsto_add_atTop_nat 1)
  have h₂ := (partialMobius_tendsto (w := 1+(ε:ℂ)) (by simp [hε])).comp (tendsto_add_atTop_nat 1)
  have hpair : Tendsto (fun N : ℕ ↦ ‖1 - (partialMobius (N+1) (s+(ε:ℂ)) -
      partialMobius (N+1) (1+(ε:ℂ))) * riemannZeta s‖^2) atTop
      (𝓝 (‖1 - ((riemannZeta (s+(ε:ℂ)))⁻¹ - referenceMobius ε) * riemannZeta s‖^2)) :=
    ((tendsto_const_nhds (x := (1:ℂ))).sub ((h₁.sub h₂).mul_const (riemannZeta s))).norm.pow 2
  apply le_of_tendsto hpair
  exact Eventually.of_forall (fun N ↦ finite_damped_moment_sq_le N ε hs h1 (hB N))


private lemma translated_real_tendsto_right (z : ℂ) :
    Tendsto (fun t : ℝ ↦ z+(t:ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa only [add_zero] using (tendsto_const_nhds (x := z)).add ht

private lemma norm_zeta_at_translate_le_linear {z : ℂ} (hz : z ≠ 1) (h0 : riemannZeta z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖riemannZeta (z+(t:ℂ))‖ ≤ C*t := by
  obtain ⟨C, hC, hBound⟩ := (differentiableAt_riemannZeta hz).isBigO_sub.exists_nonneg
  refine ⟨C, hC, ?_⟩
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  filter_upwards [translated_real_tendsto_right z hBound.bound, hpos] with t ht htpos
  change ‖riemannZeta (z+(t:ℂ)) - riemannZeta z‖ ≤ C * ‖(z+(t:ℂ))-z‖ at ht
  simpa only [h0, sub_zero, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg htpos.le] using ht

/-- With bounded residual energies at damping `ε`, a zero on the
shifted boundary must have a critical-line zero at the same ordinate.
The strict half-plane case is the previously proved zero-free criterion. -/
theorem fixed_damping_shifted_boundary_zero
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2)
    (hB : ∃ B : ℝ, ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B)
    (ρ : ℂ) (hρ : ρ.re = 1/2 + ε) (hzρ : riemannZeta ρ = 0) :
    riemannZeta (ρ-(ε:ℂ)) = 0 := by
  obtain ⟨B, hB⟩ := hB
  have hB0 : 0 ≤ B := by simpa using hB 0 0
  let s₀ := ρ-(ε:ℂ)
  let S (t : ℝ) := s₀+(t:ℂ)
  let W (t : ℝ) := ρ+(t:ℂ)
  let X (t : ℝ) := riemannZeta (S t)
  let Z (t : ℝ) := riemannZeta (W t)
  let D := referenceMobius ε
  let M (t : ℝ) := 1 - ((Z t)⁻¹-D)*X t
  let U := ‖s₀‖+1
  let V := ‖riemannZeta s₀‖+1
  have hσ₀ : s₀.re = 1/2 := by dsimp [s₀]; rw [hρ]; ring
  have hρ1 : ρ ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hρ
    linarith
  have hs₀1 : s₀ ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hσ₀
    norm_num at hσ₀
  have hte : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have htsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < min 1 (1/2-ε) :=
    hte (gt_mem_nhds (lt_min zero_lt_one (by linarith)))
  have hX : Tendsto X (𝓝[>] (0:ℝ)) (𝓝 (riemannZeta s₀)) :=
    (differentiableAt_riemannZeta hs₀1).continuousAt.tendsto.comp (translated_real_tendsto_right s₀)
  have hV : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖X t‖ < V := hX.norm (gt_mem_nhds (by
    change ‖riemannZeta s₀‖ < ‖riemannZeta s₀‖+1
    linarith))
  obtain ⟨C, hC, hZbound⟩ := norm_zeta_at_translate_le_linear hρ1 hzρ
  let P (t : ℝ) := 3*C^2*(t^2*(1+(V*‖D‖)^2) + t*(B*U^2/2))
  have hEvent : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖X t‖^2 ≤ P t := by
    filter_upwards [htpos, htsmall, hV, hZbound] with t ht ht' hXV hZT
    have ht₁ : t < 1 := ht'.trans_le (min_le_left _ _)
    have htε : t < 1/2-ε := ht'.trans_le (min_le_right _ _)
    have hSr : (S t).re = 1/2 + t := by simp [S, hσ₀]
    have hWr : (W t).re = 1/2 + ε + t := by simp [W, hρ]
    have hSW : S t+(ε:ℂ) = W t := by dsimp [S,W,s₀]; ring
    have hS1 : S t ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hSr
      linarith
    have hW1 : W t ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hWr
      linarith
    have hSR : (1/2 : ℝ) < (S t).re := by rw [hSr]; linarith
    have hWR : (1/2 : ℝ) + ε < (W t).re := by rw [hWr]; linarith
    have hZ : Z t ≠ 0 := NymanBeurling.fixed_damping_bounded_energy_implies_shifted_zero_free
      ε hε ⟨B, hB⟩ (W t) hWR hW1
    have hU : ‖S t‖ ≤ U := by
      calc
        _ ≤ ‖s₀‖+‖(t:ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
          exact add_le_add_right ht₁.le _
    have hM : ‖M t‖^2 ≤ B*U^2/(2*t) := by
      have h := limiting_mellin_sq_le ε hε hB hSR hS1 (hSW ▸ hW1)
      rw [hSW, hSr, show 2*((1/2 : ℝ)+t)-1 = 2*t by ring, ← mul_div_assoc] at h
      exact h.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hU 2) hB0) (by positivity))
    have hMt : t*‖M t‖^2 ≤ B*U^2/2 := by
      have hh := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hM
      nlinarith only [hh]
    let Y := 1-M t+D*X t
    have hXY : X t = Z t * Y := by
      dsimp only [Y,M]
      field_simp [hZ]
      ring
    have hY : ‖Y‖ ≤ 1+‖M t‖+V*‖D‖ := by
      calc
        _ ≤ ‖1-M t‖+‖D*X t‖ := norm_add_le _ _
        _ ≤ 1+‖M t‖+V*‖D‖ := by
          rw [norm_mul, mul_comm ‖D‖ ‖X t‖, ← norm_one (α := ℂ)]
          exact add_le_add (norm_sub_le _ _) (mul_le_mul_of_nonneg_right hXV.le (norm_nonneg _))
    have hYsq : ‖Y‖^2 ≤ 3*(1+‖M t‖^2+(V*‖D‖)^2) := by
      apply (pow_le_pow_left₀ (norm_nonneg _) hY 2).trans
      nlinarith only [sq_nonneg (1-‖M t‖), sq_nonneg (1-V*‖D‖), sq_nonneg (‖M t‖-V*‖D‖)]
    have hZsq : ‖Z t‖^2 ≤ C^2*t^2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hZT 2
    calc
      ‖X t‖^2 = ‖Z t‖^2 * ‖Y‖^2 := by rw [hXY, norm_mul, mul_pow]
      _ ≤ (C^2*t^2) * (3*(1+‖M t‖^2+(V*‖D‖)^2)) :=
        mul_le_mul hZsq hYsq (sq_nonneg _) (by positivity)
      _ = 3*C^2*(t^2*(1+(V*‖D‖)^2)+t*(t*‖M t‖^2)) := by ring
      _ ≤ P t := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hMt ht.le) _) (by positivity)
  have hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [P] using
      ((((hte.pow 2).mul_const (1+(V*‖D‖)^2)).add (hte.mul_const (B*U^2/2))).const_mul (3*C^2))
  have hzero : Tendsto (fun t ↦ ‖X t‖^2) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun t ↦ sq_nonneg ‖X t‖)) hEvent hP
  have hLim := tendsto_nhds_unique (hX.norm.pow 2) hzero
  have hz : ‖riemannZeta s₀‖ = 0 := by nlinarith only [hLim]
  exact norm_eq_zero.mp hz

end

end NymanBeurling.FixedDampingBoundary

open NymanBeurling

theorem solution
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2)
    (hB : ∃ B : ℝ, ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B)
    (ρ : ℂ) (hρ : ρ.re = 1/2 + ε) (hzρ : riemannZeta ρ = 0) :
    riemannZeta (ρ-(ε:ℂ)) = 0 :=
  NymanBeurling.FixedDampingBoundary.fixed_damping_shifted_boundary_zero ε hε hεhalf hB ρ hρ hzρ
