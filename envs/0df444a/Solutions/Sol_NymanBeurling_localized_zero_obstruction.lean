-- Prove2me | solution 1 for NymanBeurling.localized_zero_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:56:50.702208+00:00
-- url     : https://prove2.me/submissions/464b8718-6c93-4049-829a-800a7b2fc808

import Mathlib

open Complex Filter Function Set Topology MeasureTheory
open scoped BigOperators

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

private theorem dual_shift {s : ℂ} (hs : 1/2 < s.re) (H N : ℕ) :
    ∑ n ∈ Finset.range N, wt (H+n) * ‖jump s (H+n)‖^2 ≤ ‖s‖^2 * (H+1:ℝ)^(1-2*s.re) / (2*s.re-1) := by
  let u (n : ℕ) := (n+1:ℝ)^(1-2*s.re)
  have hpos : 0 < 2*s.re-1 := by linarith
  have hx (n : ℕ) : (2*s.re-1) * (wt n * ‖jump s n‖^2) ≤ ‖s‖^2*(u n-u (n+1)) := by
    have h := sharp_interval (a := (n+1:ℝ)) (b := (n+2:ℝ)) (by positivity) (by linarith) hs
    have hd : (n+2:ℝ) - (n+1:ℝ) = 1 := by ring
    simpa only [jump,pval,wt,u,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Complex.ofReal_add,Complex.ofReal_one,
      Complex.ofReal_natCast,Complex.ofReal_ofNat,hd,div_one,mul_assoc,add_assoc,one_add_one_eq_two] using h
  have htel : ∑ n ∈ Finset.range N, (u (H+n)-u (H+n+1))=u H-u (H+N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih];simp only [Nat.add_succ];ring
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hx (H+n))
  rw [←Finset.mul_sum,←Finset.mul_sum,htel] at h
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm];apply h.trans
  change ‖s‖^2*(u H-u (H+N))≤‖s‖^2*u H
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hu : 0≤u (H+N) := by dsimp [u];positivity
  linarith

private theorem energy_shift (g h : ℕ → ℂ) (H N : ℕ) :
    ‖∑ n ∈ Finset.range N, g n * h n‖^2 ≤
      (∑ n ∈ Finset.range N, ‖g n‖^2/wt (H+n)) * ∑ n ∈ Finset.range N, wt (H+n) * ‖h n‖^2 := by
  let a (n : ℕ) := ‖g n‖ / Real.sqrt (wt (H+n))
  let b (n : ℕ) := Real.sqrt (wt (H+n)) * ‖h n‖
  have hw (n : ℕ) : Real.sqrt (wt (H+n)) ≠ 0 := (Real.sqrt_pos.mpr (weight_pos (H+n))).ne'
  have hab (n : ℕ) : ‖g n * h n‖ = a n * b n := by rw [norm_mul]; dsimp [a,b]; field_simp [hw n]
  have ha (n : ℕ) : a n ^ 2 = ‖g n‖^2/wt (H+n) := by dsimp [a]; rw [div_pow,Real.sq_sqrt (weight_pos _).le]
  have hb (n : ℕ) : b n ^ 2 = wt (H+n) * ‖h n‖^2 := by dsimp [b]; rw [mul_pow,Real.sq_sqrt (weight_pos _).le]
  have hnorm := norm_sum_le (Finset.range N) (fun n => g n * h n)
  simp_rw [hab] at hnorm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) a b
  simp_rw [ha,hb] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

private theorem residual_hasSum {s : ℂ} (hs : 1/2 < s.re) (h1 : s ≠ 1) (hz : riemannZeta s = 0)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    HasSum (fun n => (1 - ∑ k ∈ S, c k * remainder (k+2) (n+1)) * jump s n) 1 := by
  have hkernel (k : ℕ) : HasSum (fun n => remainder (k+2) (n+1) * jump s n) 0 := by
    have h := bounded_jump_summable (fun n => remainder_bound (by omega : 0 < k+2) (n+1)) (by linarith : 0 < s.re)
    simpa [remainder_transform (by omega : 0 < k+2) (by linarith : 0 < s.re) h1,hz] using h.hasSum
  have hlin := hasSum_sum (s := S) (fun k _ => (hkernel k).mul_left (c k))
  have h := (jump_one (by linarith : 0 < s.re)).sub hlin
  simpa [sub_mul,Finset.sum_mul,mul_assoc] using h

-- All entries in a finite certificate are rational.
private def qrem (k m : ℕ) : ℚ := (m % k : ℕ) / (k:ℚ)
private def resid (c : ℕ →₀ ℚ) (n : ℕ) : ℚ :=
  1 - ∑ k ∈ c.support, c k * qrem (k+2) (n+1)
private def qweight (n : ℕ) : ℚ := (n+1:ℚ)*(n+2:ℚ)
private def part (c : ℕ →₀ ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (resid c n)^2 / qweight n
private def major (c : ℕ →₀ ℚ) : ℚ := 1 + ∑ k ∈ c.support, |c k|
private def certificate (c : ℕ →₀ ℚ) (H : ℕ) : ℚ := part c H + (major c)^2/(H+1)

private theorem resid_bound (c : ℕ →₀ ℚ) (n : ℕ) : |resid c n| ≤ major c := by
  unfold resid major
  refine (abs_sub _ _).trans ?_
  simp only [abs_one,add_le_add_iff_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [abs_mul]
  have hb : 0 ≤ qrem (k+2) (n+1) := by unfold qrem; positivity
  have h1 : qrem (k+2) (n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (Nat.mod_lt (n+1) (by omega : 0 < k+2)).le)
  rw [abs_of_nonneg hb]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

private theorem part_le_certificate (c : ℕ →₀ ℚ) (N H : ℕ) : part c N ≤ certificate c H := by
  have hpos (n : ℕ) : 0 < qweight n := by dsimp [qweight]; positivity
  have hm : Monotone (part c) := monotone_nat_of_le_succ fun n => by
    simp only [part, Finset.sum_range_succ,le_add_iff_nonneg_right]
    exact div_nonneg (sq_nonneg _) (hpos n).le
  by_cases h : N ≤ H
  · exact (hm h).trans (le_add_of_nonneg_right (by positivity))
  have hstep (n : ℕ) : certificate c (n+1) ≤ certificate c n := by
    unfold certificate part
    rw [Finset.sum_range_succ,add_assoc]
    rw [add_le_add_iff_left]
    have hR : (resid c n)^2 ≤ (major c)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (resid_bound c n) 2
    calc
      _ ≤ (major c)^2 / qweight n + (major c)^2/((n+1 : ℕ)+1 : ℚ) :=
        add_le_add (div_le_div_of_nonneg_right hR (hpos n).le) le_rfl
      _ = _ := by unfold qweight; push_cast; field_simp; ring
  have hc := (antitone_nat_of_succ_le hstep) (Nat.le_of_lt (Nat.lt_of_not_ge h))
  exact (le_add_of_nonneg_right (show 0 ≤ (major c)^2/(N+1) by positivity)).trans hc


private def etile (c : ℕ→₀ℚ) (n : ℕ) : ℝ := (((resid c n)^2/qweight n:ℚ):ℝ)

private theorem local_bound {s : ℂ} (hs : 1/2<s.re) (h1 : s≠1) (hz : riemannZeta s=0)
    (c : ℕ→₀ℚ) (H K : ℕ) :
    let g := fun n : ℕ => (resid c n : ℂ)*jump s n
    let T := ∑' j : ℕ,etile c (H+j)
    (2*s.re-1)*(H+1:ℝ)^(2*s.re-1)*‖1-∑ n∈Finset.range H,g n‖^2 ≤ T*‖s‖^2 ∧
      T ≤ (certificate c K:ℝ)-∑ n∈Finset.range H,etile c n := by
  dsimp only
  let E := etile c
  have hn (j : ℕ) : 0≤E j := by dsimp [E,etile,qweight];positivity
  have hpsum (M : ℕ) : (∑ j∈Finset.range M,E j) ≤ (certificate c K:ℝ) := by
    simpa only [E,etile,part,Rat.cast_sum] using (Rat.cast_le (K:=ℝ)).mpr (part_le_certificate c M K)
  have he : Summable E := summable_of_sum_range_le hn hpsum
  have htail : Summable (fun j => E (H+j)) := by simpa only [Nat.add_comm H] using (summable_nat_add_iff H).mpr he
  have htot := he.sum_add_tsum_nat_add H
  have hc := he.tsum_le_of_sum_range_le hpsum
  have hcast (n : ℕ) : (resid c n:ℂ)=1-∑ k∈c.support,(c k:ℂ)*remainder (k+2) (n+1) := by simp [resid,qrem,remainder]
  have hsum : HasSum (fun n => (resid c n:ℂ)*jump s n) 1 := by
    simpa only [hcast] using residual_hasSum hs h1 hz c.support (fun k => (c k:ℂ))
  have hshift := (hasSum_nat_add_iff' H).mpr hsum
  let T := ∑' j : ℕ, E (H+j)
  have hT : 0≤T := tsum_nonneg (fun n => hn _)
  constructor
  · let v := (H+1:ℝ)^(2*s.re-1)
    have hv : 0<v := Real.rpow_pos_of_pos (by positivity) _
    have hpos : 0<2*s.re-1 := by linarith
    have hi : (H+1:ℝ)^(1-2*s.re)=v⁻¹ := by rw [show 1-2*s.re=-(2*s.re-1) by ring,Real.rpow_neg (by positivity)]
    have hb : ‖1-∑ n∈Finset.range H,(resid c n:ℂ)*jump s n‖^2≤
        T*(‖s‖^2*v⁻¹/(2*s.re-1)) := by
      apply le_of_tendsto (hshift.tendsto_sum_nat.norm.pow 2)
      apply Eventually.of_forall;intro N
      simp only [Nat.add_comm _ H]
      apply (energy_shift (fun j => (resid c (H+j):ℂ)) (fun j => jump s (H+j)) H N).trans
      apply mul_le_mul _ _ (Finset.sum_nonneg fun j _ => mul_nonneg (weight_pos _).le (sq_nonneg _)) hT
      · have heq (j : ℕ) : ‖(resid c (H+j):ℂ)‖^2/wt (H+j) = E (H+j) := by simp [E,etile,wt,qweight,Complex.norm_ratCast,sq_abs]
        simpa only [heq] using htail.sum_le_tsum (Finset.range N) (fun i _ => hn _)
      · simpa only [hi] using dual_shift hs H N
    rw [←mul_div_assoc,le_div_iff₀ hpos] at hb
    have hbb := mul_le_mul_of_nonneg_right hb hv.le
    field_simp [hv.ne'] at hbb
    change (2*s.re-1)*v*_≤T*‖s‖^2
    linarith only [hbb]
  · change (∑' j : ℕ,E (H+j))≤_-(∑ j∈Finset.range H,E j)
    simpa only [Nat.add_comm H] using (le_sub_iff_add_le'.mpr (htot.trans_le hc))

private theorem two_scales {s : ℂ} (hs : 1/2<s.re) (h1 : s≠1) (hz : riemannZeta s=0)
    (c : ℕ→₀ℚ) (H K : ℕ) :
    let P := ∑ n∈Finset.range H,etile c n
    let a := (H+1:ℝ)^(1-2*s.re)
    2*s.re-1 ≤ 2*‖s‖^2*(P+a*((certificate c K:ℝ)-P)) := by
  dsimp only
  let P := ∑ n∈Finset.range H,etile c n
  let J := ∑ n∈Finset.range H,(resid c n:ℂ)*jump s n
  let T := ∑' j : ℕ,etile c (H+j)
  let b := 2*s.re-1
  let v := (H+1:ℝ)^b
  have hb : 0<b := by dsimp [b];linarith
  have hv : 0<v := Real.rpow_pos_of_pos (by positivity) _
  have hP : 0≤P := Finset.sum_nonneg fun n _ => by dsimp [etile,qweight];positivity
  have hpre : b*‖J‖^2≤P*‖s‖^2 := by
    have h := energy_shift (fun n => (resid c n:ℂ)) (jump s) 0 H
    simp only [Nat.zero_add] at h
    have heq (n : ℕ) : ‖(resid c n:ℂ)‖^2/wt n=etile c n := by simp [etile,wt,qweight,Complex.norm_ratCast,sq_abs]
    simp_rw [heq] at h
    have ht := dual_shift hs 0 H
    simp only [Nat.zero_add,Nat.cast_zero,zero_add,Real.one_rpow,mul_one] at ht
    have hh : ‖J‖^2≤P*(‖s‖^2/b) := h.trans (mul_le_mul_of_nonneg_left ht hP)
    rwa [←mul_div_assoc,le_div_iff₀ hb,mul_comm] at hh
  obtain ⟨hrem,hC⟩ := local_bound hs h1 hz c H K
  change b*v*‖1-J‖^2≤T*‖s‖^2 at hrem
  change T≤(certificate c K:ℝ)-P at hC
  have htail : b*‖1-J‖^2≤((certificate c K:ℝ)-P)*‖s‖^2/v := by
    apply (le_div_iff₀ hv).mpr
    rw [mul_right_comm b]
    exact hrem.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  have htriangle : (1:ℝ)≤‖J‖+‖1-J‖ := by
    simpa only [add_sub_cancel,norm_one] using norm_add_le J (1-J)
  have hsq : (1:ℝ)≤2*(‖J‖^2+‖1-J‖^2) := by
    have h0 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) htriangle 2
    nlinarith only [h0,sq_nonneg (‖J‖-‖1-J‖)]
  have hh := mul_le_mul_of_nonneg_left hsq hb.le
  have ha : (H+1:ℝ)^(1-2*s.re)=v⁻¹ := by rw [show 1-2*s.re=-(2*s.re-1) by ring,Real.rpow_neg (by positivity)]
  rw [ha];change b≤2*‖s‖^2*(P+v⁻¹*((certificate c K:ℝ)-P))
  rw [div_eq_mul_inv] at htail
  linarith only [hpre,htail,hh]

theorem solution (s : ℂ) (hs : 1/2<s.re) (h1 : s≠1) (hz : riemannZeta s=0)
    (c : ℕ→₀ℚ) (H K : ℕ) :
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let T := ∑' j : ℕ,(E (H+j):ℝ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    let D := 1-∑ n∈Finset.range H,(R n:ℂ)*((n+1:ℂ)^(-s)-(n+2:ℂ)^(-s))
    let P := ∑ n∈Finset.range H,(E n:ℝ)
    (2*s.re-1)*(H+1:ℝ)^(2*s.re-1)*‖D‖^2 ≤ T*‖s‖^2 ∧ T ≤ (C:ℝ)-P ∧
      2*s.re-1 ≤ 2*‖s‖^2*(P+(H+1:ℝ)^(1-2*s.re)*((C:ℝ)-P)) := by
  dsimp only
  have h := local_bound hs h1 hz c H K
  simpa only [resid,qrem,jump,pval,etile,certificate,part,qweight,major,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using And.intro h.1 (And.intro h.2 (two_scales hs h1 hz c H K))
