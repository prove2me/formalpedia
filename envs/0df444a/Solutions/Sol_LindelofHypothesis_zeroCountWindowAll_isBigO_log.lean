-- Prove2me | solution 1 for LindelofHypothesis.zeroCountWindowAll_isBigO_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:53:00.137378+00:00
-- url     : https://prove2.me/submissions/dd1940f7-a7c7-4bec-8213-282f23b09e2f

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts


open Complex Filter Asymptotics Topology Set

namespace LHBound

/-- `F y = y^(1-s)/(1-s)`, an antiderivative of `y^(-s)`. -/
noncomputable def F (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (-s + 1) / (-s + 1)

lemma step1 (s : ℂ) (hs : s ≠ 0) (hσ : 0 ≤ s.re) (n : ℝ) (hn : 1 ≤ n) :
    ∀ x ∈ Icc n (n + 1), ‖(x : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ * n ^ (-s.re - 1) * (x - n) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun y => (-s) * (y : ℂ) ^ (-s - 1))
  · intro x hx
    have hx0 : x ≠ 0 := by have := hx.1; linarith
    exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := by have := hx.1; linarith
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
    gcongr
    simp only [sub_re, neg_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)

lemma step2 (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) (hσ : 0 ≤ s.re) (n : ℝ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - (F s (n + 1) - F s n)‖ ≤ ‖s‖ * n ^ (-s.re - 1) := by
  set g : ℝ → ℂ := fun y => F s y - (y : ℂ) * (n : ℂ) ^ (-s) with hg
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (f' := fun y => (y : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) (a := n) (b := n + 1)
    (C := ‖s‖ * n ^ (-s.re - 1)) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · have : g (n + 1) - g n = -((n : ℂ) ^ (-s) - (F s (n + 1) - F s n)) := by
      simp only [hg]; push_cast; ring
    rw [this, norm_neg] at key
    simpa using key
  · intro x hx
    have hx0 : x ≠ 0 := by have := hx.1; linarith
    have h1 := hasDerivAt_ofReal_cpow_const' hx0 (r := -s) (by
      intro h; apply hs1; linear_combination -h)
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (n : ℂ) ^ (-s)) (1 * (n : ℂ) ^ (-s)) x :=
      (hasDerivAt_id x).ofReal_comp.mul_const _
    simp only [one_mul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  · intro x hx
    have := step1 s hs hσ n hn x (Ico_subset_Icc_self hx)
    calc _ ≤ ‖s‖ * n ^ (-s.re - 1) * (x - n) := this
      _ ≤ ‖s‖ * n ^ (-s.re - 1) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by positivity)
      _ = _ := mul_one _

lemma norm_F_le (s : ℂ) (hσ : 1 ≤ s.re) (him : s.im ≠ 0) (y : ℝ) (hy : 1 ≤ y) :
    ‖F s y‖ ≤ 1 / |s.im| := by
  unfold F
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  have h1 : y ^ (-s + 1).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hy
    simp; linarith
  have h2 : |s.im| ≤ ‖-s + 1‖ := by
    have := abs_im_le_norm (-s + 1)
    simpa using this
  have h : 0 < |s.im| := abs_pos.mpr him
  · calc y ^ (-s + 1).re / ‖-s + 1‖ ≤ 1 / ‖-s + 1‖ := by gcongr
      _ ≤ 1 / |s.im| := by gcongr

lemma telescope (f e t : ℕ → ℂ) (he : ∀ n, e n = t n - (f (n + 1) - f n)) (N M : ℕ)
    (h : N ≤ M) : ∑ n ∈ Finset.Ico N M, t n = f M - f N + ∑ n ∈ Finset.Ico N M, e n := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, Finset.sum_Ico_succ_top hM, ih, he]; ring

lemma inv_sq_sum (N M : ℕ) (hN : 1 ≤ N) (h : N ≤ M) :
    ∑ n ∈ Finset.Ico N M, (1 / (n : ℝ) ^ 2) ≤ (2 : ℝ) / N - (2 : ℝ) / M := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hN.trans hM
    have : 1 / (M : ℝ) ^ 2 ≤ 2 / M - 2 / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma harm (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico 1 (N + 1), (1 / (n : ℝ)) ≤ 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : 1 / ((N + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log N := by
      push_cast
      have := Real.log_le_sub_one_of_pos (x := (N : ℝ) / (N + 1)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at this
      have e : (N : ℝ) / (N + 1) - 1 = -(1 / (N + 1)) := by field_simp; ring
      linarith
    linarith

/-- Main bound for `1 < σ ≤ 2`, `T ≥ 1`. -/
lemma zeta_bound_gt (σ T : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) :
    ‖riemannZeta (σ + T * I)‖ ≤ 9 + Real.log (T + 1) := by
  set s : ℂ := σ + T * I with hsdef
  have hre : s.re = σ := by simp [hsdef]
  have him : s.im = T := by simp [hsdef]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hre] at this; linarith
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.im h; simp [him] at this; linarith
  have hnorm : ‖s‖ ≤ 2 + T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ = σ + T := by rw [hre, him, abs_of_pos (by linarith), abs_of_pos (by linarith)]
      _ ≤ 2 + T := by linarith
  set N : ℕ := ⌈T⌉₊ with hN
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by linarith) (Nat.le_ceil T)
    exact_mod_cast this
  have hTN : T ≤ N := Nat.le_ceil T
  have hNT : (N : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  -- the terms
  set t : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-s) with ht
  set f : ℕ → ℂ := fun n => F s n with hf
  set e : ℕ → ℂ := fun n => t n - (f (n + 1) - f n) with he
  have he_bd : ∀ n, 1 ≤ n → ‖e n‖ ≤ ‖s‖ * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := step2 s hs0 hs1 (by rw [hre]; linarith) n hn'
    simp only [he, ht, hf]
    push_cast at this ⊢
    refine this.trans ?_
    gcongr
    rw [hre, one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le hn'
    push_cast; linarith
  have ht_bd : ∀ n, 1 ≤ n → ‖t n‖ ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [ht]
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, hre, Real.rpow_neg (by positivity),
      one_div]
    gcongr
    calc (n : ℝ) = n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ n ^ σ := Real.rpow_le_rpow_of_exponent_le hn' hσ.le
  have hfb : ∀ n, 1 ≤ n → ‖f n‖ ≤ 1 / T := by
    intro n hn
    have := norm_F_le s (by rw [hre]; linarith) (by rw [him]; linarith) n (by exact_mod_cast hn)
    rwa [him, abs_of_pos (by linarith)] at this
  -- partial sums
  have hpart : ∀ M, N ≤ M → ‖∑ n ∈ Finset.Ico 1 M, t n‖ ≤ 9 + Real.log (T + 1) := by
    intro M hM
    rw [← Finset.sum_Ico_consecutive _ hN1 hM, telescope f e t (fun n => rfl) N M hM]
    have A : ‖∑ n ∈ Finset.Ico 1 N, t n‖ ≤ 1 + Real.log N := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn => ht_bd n (Finset.mem_Ico.1 hn).1).trans ?_
      have h1 := harm N hN1
      rw [Finset.sum_Ico_succ_top hN1] at h1
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
    have B : ‖∑ n ∈ Finset.Ico N M, e n‖ ≤ 6 := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn =>
        he_bd n (hN1.trans (Finset.mem_Ico.1 hn).1)).trans ?_
      rw [← Finset.mul_sum]
      have h1 := inv_sq_sum N M hN1 hM
      have hM0 : (0 : ℝ) ≤ 2 / M := by positivity
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      calc ‖s‖ * ∑ n ∈ Finset.Ico N M, 1 / (n : ℝ) ^ 2 ≤ (2 + T) * (2 / N) := by
            apply mul_le_mul hnorm (by linarith) (Finset.sum_nonneg fun _ _ => by positivity)
              (by linarith)
        _ ≤ (2 + T) * (2 / T) := by gcongr
        _ ≤ 6 := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    have C : ‖f M - f N‖ ≤ 2 / T := by
      refine (norm_sub_le _ _).trans ?_
      have := hfb M (hN1.trans hM); have := hfb N hN1
      rw [show 2 / T = 1 / T + 1 / T by ring]; linarith
    have D : 2 / T ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have E : Real.log N ≤ Real.log (T + 1) :=
      Real.log_le_log (by exact_mod_cast hN1) hNT
    calc ‖∑ n ∈ Finset.Ico 1 N, t n + (f M - f N + ∑ n ∈ Finset.Ico N M, e n)‖
        ≤ ‖∑ n ∈ Finset.Ico 1 N, t n‖ + (‖f M - f N‖ + ‖∑ n ∈ Finset.Ico N M, e n‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 9 + Real.log (T + 1) := by linarith
  -- limit
  have hsre : 1 < s.re := by rw [hre]; exact hσ
  have hsum : HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsre]
    apply Summable.hasSum
    have := (Complex.summable_one_div_nat_cpow (p := s)).mpr hsre
    exact (summable_nat_add_iff 1).mpr this |>.congr fun k => by push_cast; rfl
  have htend := hsum.tendsto_sum_nat
  have hk : ∀ M : ℕ, ∑ k ∈ Finset.range M, 1 / ((k : ℂ) + 1) ^ s =
      ∑ n ∈ Finset.Ico 1 (M + 1), t n := by
    intro M
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [ht, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.cpow_neg, one_div]; push_cast; ring_nf
  refine le_of_tendsto htend.norm (eventually_atTop.2 ⟨N, fun M hM => ?_⟩)
  rw [hk]
  exact hpart (M + 1) (by omega)

lemma zeta_bound_one (T : ℝ) (hT : 1 ≤ T) :
    ‖riemannZeta (1 + T * I)‖ ≤ 9 + Real.log (T + 1) := by
  have hc : ContinuousAt (fun σ : ℝ => riemannZeta (σ + T * I)) 1 := by
    have h1 : (((1 : ℝ) : ℂ) + T * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    exact ((differentiableAt_riemannZeta h1).continuousAt).comp
      (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)
  have ht := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))).norm
  have := le_of_tendsto ht (by
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ
    exact zeta_bound_gt σ T hσ.1 hσ.2.le hT)
  simpa using this

lemma zeta_one_isBigO (a : ℝ) (ha : 0 < a) :
    (fun T : ℝ => riemannZeta (1 + T * I)) =O[atTop] (fun T : ℝ => T ^ a) := by
  refine IsBigO.of_bound (9 + 2 ^ a / a) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := zeta_bound_one T hT
  have h2 : Real.log (T + 1) ≤ (T + 1) ^ a / a := Real.log_le_rpow_div (by linarith) ha
  have h3 : (T + 1) ^ a ≤ (2 * T) ^ a := Real.rpow_le_rpow (by linarith) (by linarith) ha.le
  have h4 : (2 * T) ^ a = 2 ^ a * T ^ a := Real.mul_rpow (by norm_num) (by linarith)
  have h5 : 1 ≤ T ^ a := Real.one_le_rpow hT ha.le
  have h6 : (T + 1) ^ a / a ≤ 2 ^ a / a * T ^ a := by
    calc (T + 1) ^ a / a ≤ (2 * T) ^ a / a := by gcongr
      _ = 2 ^ a / a * T ^ a := by rw [h4]; ring
  have : (1 + T * I) = (((1 : ℝ) : ℂ) + T * I) := by simp
  nlinarith

end LHBound


open Complex Filter Topology Set ComplexConjugate

namespace LHGV

noncomputable def h (T x : ℝ) : ℝ := Real.log (1 + T ^ 2 / x ^ 2)

lemma h_convex (T : ℝ) : ConvexOn ℝ (Ioi 0) (h T) := by
  have heq : EqOn (fun x : ℝ => Real.log (x ^ 2 + T ^ 2) - 2 * Real.log x) (h T) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    simp only [h]
    rw [show 1 + T ^ 2 / x ^ 2 = (x ^ 2 + T ^ 2) / x ^ 2 by field_simp,
      Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  refine ConvexOn.congr ?_ heq
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + T ^ 2) - 2 * Real.log x)
      (-(2 * T ^ 2) / (x * (x ^ 2 + T ^ 2))) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + T ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (T ^ 2)
    have h2 := h1.log (by positivity)
    have h3 := (Real.hasDerivAt_log hx.ne').const_mul 2
    have : x ^ 2 + T ^ 2 ≠ 0 := by positivity
    refine (h2.sub h3).congr_deriv ?_
    field_simp
    ring
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    rw [(hd x hx0).deriv, (hd y hy0).deriv, neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_le_mul hxy this (by positivity) hy0.le]

/-- partial sums -/
noncomputable def Φ (T σ : ℝ) (n : ℕ) : ℝ := (1 / 2) * ∑ j ∈ Finset.range (n + 1), h T (σ + j)

lemma norm_add_j (σ T : ℝ) (j : ℕ) :
    ‖((σ : ℂ) + T * I) + j‖ = Real.sqrt ((σ + j) ^ 2 + T ^ 2) := by
  have : ((σ : ℂ) + T * I) + j = ((σ + j : ℝ) : ℂ) + T * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]

lemma log_ratio (σ T : ℝ) (hσ : 0 < σ) (j : ℕ) :
    Real.log ‖((σ : ℂ) + T * I) + j‖ - Real.log (σ + j) = (1 / 2) * h T (σ + j) := by
  rw [norm_add_j]
  have hp : 0 < σ + j := by positivity
  rw [Real.log_sqrt (by positivity)]
  simp only [h]
  rw [show 1 + T ^ 2 / (σ + j) ^ 2 = ((σ + j) ^ 2 + T ^ 2) / (σ + j) ^ 2 by field_simp,
    Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast; ring

lemma GammaSeq_identity (σ T : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : n ≠ 0) :
    Real.log (Real.GammaSeq σ n) - Real.log ‖Complex.GammaSeq ((σ : ℂ) + T * I) n‖ = Φ T σ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hprodR : 0 < ∏ j ∈ Finset.range (n + 1), (σ + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hprodC : ∀ j ∈ Finset.range (n + 1), 0 < ‖((σ : ℂ) + T * I) + j‖ := by
    intro j _; rw [norm_add_j]; apply Real.sqrt_pos.mpr; positivity
  have hnorm : ‖Complex.GammaSeq ((σ : ℂ) + T * I) n‖ =
      (n : ℝ) ^ σ * (Nat.factorial n) / ∏ j ∈ Finset.range (n + 1), ‖((σ : ℂ) + T * I) + j‖ := by
    rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod]
    congr 2
    · rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
        norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    · simp
  rw [hnorm, Real.GammaSeq]
  have hP : 0 < ∏ j ∈ Finset.range (n + 1), ‖((σ : ℂ) + T * I) + j‖ := Finset.prod_pos hprodC
  rw [Real.log_div (by positivity) hprodR.ne', Real.log_div (by positivity) hP.ne',
    Real.log_prod (fun j _ => by positivity), Real.log_prod (fun j hj => (hprodC j hj).ne')]
  have : ∑ i ∈ Finset.range (n + 1), Real.log ‖((σ : ℂ) + T * I) + i‖ -
      ∑ i ∈ Finset.range (n + 1), Real.log (σ + i) = Φ T σ n := by
    rw [← Finset.sum_sub_distrib, Φ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => log_ratio σ T hσ j
  linarith

/-- `Ψ T σ = log Γ(σ) - log ‖Γ(σ + iT)‖`. -/
noncomputable def Ψ (T σ : ℝ) : ℝ := Real.log (Real.Gamma σ) - Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖

lemma Gamma_ne (σ T : ℝ) (hσ : 0 < σ) : Complex.Gamma ((σ : ℂ) + T * I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have := congrArg Complex.re hm
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

lemma tendsto_Φ (σ T : ℝ) (hσ : 0 < σ) : Tendsto (Φ T σ) atTop (𝓝 (Ψ T σ)) := by
  have h1 := (Real.GammaSeq_tendsto_Gamma σ).log (Real.Gamma_pos_of_pos hσ).ne'
  have h2 := ((Complex.GammaSeq_tendsto_Gamma ((σ : ℂ) + T * I)).norm).log
    (norm_ne_zero_iff.mpr (Gamma_ne σ T hσ))
  refine (h1.sub h2).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact GammaSeq_identity σ T hσ n hn

lemma Ψ_convex_aux (T x y a b : ℝ) (hx0 : 0 < x) (hy0 : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (j : ℕ) : h T (a * x + b * y + j) ≤ a * h T (x + j) + b * h T (y + j) := by
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  have := (h_convex T).2 (show x + j ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; positivity)
    (show y + j ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; positivity) ha hb hab
  simp only [smul_eq_mul] at this
  have e : a * (x + j) + b * (y + j) = a * x + b * y + j := by
    have : a * j + b * j = j := by rw [← add_mul, hab, one_mul]
    linarith
  rw [e] at this
  exact this


lemma Ψ_convex (T : ℝ) : ConvexOn ℝ (Ioi 0) (Ψ T) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hz : 0 < a • x + b • y := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using hy0
    · simp only [smul_eq_mul]; positivity
  have hlim := tendsto_Φ (a • x + b • y) T hz
  have hlim2 := ((tendsto_Φ x T hx0).const_smul a).add ((tendsto_Φ y T hy0).const_smul b)
  refine le_of_tendsto_of_tendsto' hlim hlim2 fun n => ?_
  simp only [Φ, smul_eq_mul]
  have key : ∑ j ∈ Finset.range (n + 1), h T (a * x + b * y + j) ≤
      ∑ j ∈ Finset.range (n + 1), (a * h T (x + j) + b * h T (y + j)) := by
    apply Finset.sum_le_sum
    intro j _
    exact Ψ_convex_aux T x y a b hx0 hy0 ha hb hab j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at key
  linear_combination (1 / 2 : ℝ) * key

end LHGV


open Complex Filter Asymptotics Topology Set ComplexConjugate

namespace LHFE0

lemma gamma_norm_sq (T : ℝ) (hT : T ≠ 0) :
    ‖Gamma (1 - T * I)‖ ^ 2 = Real.pi * T / Real.sinh (Real.pi * T) := by
  have hz : (T : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hT) I_ne_zero
  have h1 := Gamma_mul_Gamma_one_sub ((T : ℂ) * I)
  have h2 := Gamma_add_one ((T : ℂ) * I) hz
  have h3 : conj (Gamma (1 - T * I)) = Gamma ((T : ℂ) * I + 1) := by
    rw [← Gamma_conj]; congr 1; simp [conj_ofReal]; ring
  have h4 : Complex.sin (Real.pi * (T * I)) = Complex.sinh (Real.pi * T) * I := by
    rw [← sin_mul_I]; ring_nf
  have hs : Real.sinh (Real.pi * T) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hT
  apply Complex.ofReal_injective
  rw [ofReal_pow, ← Complex.mul_conj', h3, h2]
  calc Gamma (1 - ↑T * I) * (↑T * I * Gamma (↑T * I))
      = ↑T * I * (Gamma (↑T * I) * Gamma (1 - ↑T * I)) := by ring
    _ = ↑T * I * (↑Real.pi / (Complex.sinh (↑Real.pi * ↑T) * I)) := by rw [h1, h4]
    _ = _ := by
      rw [ofReal_div, ofReal_mul, ofReal_sinh, ofReal_mul]
      have : Complex.sinh (↑Real.pi * ↑T) ≠ 0 := by rw [← ofReal_mul, ← ofReal_sinh]; exact_mod_cast hs
      field_simp

lemma cos_norm (T : ℝ) :
    ‖Complex.cos (Real.pi * (1 - T * I) / 2)‖ = |Real.sinh (Real.pi * T / 2)| := by
  have : (Real.pi : ℂ) * (1 - T * I) / 2 = Real.pi / 2 - (((Real.pi * T / 2 : ℝ)) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.cos_sub, cos_mul_I, sin_mul_I]
  have e1 : Complex.cos (↑Real.pi / 2) = 0 := by
    rw [← ofReal_ofNat, ← ofReal_div, ← ofReal_cos]; simp
  have e2 : Complex.sin (↑Real.pi / 2) = 1 := by
    rw [← ofReal_ofNat, ← ofReal_div, ← ofReal_sin]; simp
  rw [e1, e2]
  have e3 : (↑Real.pi * ↑T / 2 : ℂ) = ((Real.pi * T / 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [zero_mul, one_mul]
  rw [← ofReal_sinh, zero_add, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `‖ζ(iT)‖ = c(T) ‖ζ(1+iT)‖` with `c(T) = (1/π) ‖Γ(1-iT)‖ |sinh(πT/2)|`. -/
lemma zeta_iT (T : ℝ) (hT : T ≠ 0) :
    ‖riemannZeta (T * I)‖ =
      (1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)| *
        ‖riemannZeta (1 + T * I)‖ := by
  set s : ℂ := 1 - T * I with hsdef
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [hsdef] at this; exact hT this
  have hsn : ∀ n : ℕ, s ≠ -n := by
    intro n h; have := congrArg Complex.re h; simp [hsdef] at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hfe := riemannZeta_one_sub hsn hs1
  have e1 : 1 - s = T * I := by simp [hsdef]
  have e2 : riemannZeta s = conj (riemannZeta (1 + T * I)) := by
    rw [← riemannZeta_conj]; congr 1; simp [hsdef, conj_ofReal]; ring
  rw [e1] at hfe
  rw [hfe, e2, norm_mul, norm_mul, norm_mul, norm_mul, cos_norm, RCLike.norm_conj]
  have h2pi : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi)⁻¹ := by
    have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hsdef, Real.rpow_neg_one]
  rw [h2pi]
  simp only [norm_ofNat]
  have hpi := Real.pi_pos
  field_simp

lemma c_sq (T : ℝ) (hT : 0 < T) :
    ((1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)|) ^ 2 =
      T * Real.sinh (Real.pi * T / 2) / (2 * Real.pi * Real.cosh (Real.pi * T / 2)) := by
  rw [mul_pow, mul_pow, gamma_norm_sq T hT.ne', sq_abs]
  have : Real.pi * T = 2 * (Real.pi * T / 2) := by ring
  rw [this, Real.sinh_two_mul]
  have hsh : 0 < Real.sinh (Real.pi * T / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hch : 0 < Real.cosh (Real.pi * T / 2) := Real.cosh_pos _
  have hpi := Real.pi_pos
  field_simp

lemma c_bounds (T : ℝ) (hT : 1 ≤ T) :
    T / 16 ≤ ((1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)|) ^ 2 ∧
    ((1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)|) ^ 2 ≤ T := by
  rw [c_sq T (by linarith)]
  set x := Real.pi * T / 2 with hx
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith
  have hch : 0 < Real.cosh x := Real.cosh_pos _
  have hsc : Real.sinh x ≤ Real.cosh x := (Real.sinh_lt_cosh x).le
  have hsc2 : Real.cosh x ≤ 2 * Real.sinh x := by
    rw [Real.sinh_eq, Real.cosh_eq]
    have : 3 ≤ Real.exp x * Real.exp x := by
      rw [← Real.exp_add]
      have := Real.add_one_le_exp (x + x); linarith
    have hpos : 0 < Real.exp x := Real.exp_pos x
    have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
    rw [hneg]
    rw [show 2 * ((Real.exp x - (Real.exp x)⁻¹) / 2) = Real.exp x - (Real.exp x)⁻¹ by ring]
    have : (Real.exp x)⁻¹ * 3 ≤ Real.exp x := by
      rw [inv_mul_le_iff₀ hpos]; linarith
    linarith
  have hT0 : 0 ≤ T := by linarith
  have hTc : 0 < T * Real.cosh x := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hpi4 hTc, mul_le_mul_of_nonneg_left hsc2 hT0]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsc hT0, mul_lt_mul_of_pos_left hpi hTc]

end LHFE0


open Complex Filter Topology Set ComplexConjugate

namespace LHGV

lemma Ψ_shift (T σ : ℝ) (hσ : 0 < σ) (hT : T ≠ 0) :
    Ψ T (σ + 1) = Ψ T σ + Real.log σ - Real.log ‖(σ : ℂ) + T * I‖ := by
  have hs : (σ : ℂ) + T * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hT this
  have e : ((σ + 1 : ℝ) : ℂ) + T * I = ((σ : ℂ) + T * I) + 1 := by push_cast; ring
  simp only [Ψ]
  rw [e, Complex.Gamma_add_one _ hs, Real.Gamma_add_one hσ.ne', norm_mul,
    Real.log_mul hσ.ne' (Real.Gamma_pos_of_pos hσ).ne',
    Real.log_mul (norm_ne_zero_iff.mpr hs) (norm_ne_zero_iff.mpr (Gamma_ne σ T hσ))]
  ring

lemma Ψ_half (T : ℝ) : Ψ T (1 / 2) = (1 / 2) * Real.log (Real.cosh (Real.pi * T)) := by
  have hz := Gamma_ne (1 / 2) T (by norm_num)
  have h1 := Complex.Gamma_mul_Gamma_one_sub (((1 / 2 : ℝ) : ℂ) + T * I)
  have h2 : Complex.Gamma (1 - (((1 / 2 : ℝ) : ℂ) + T * I)) =
      conj (Complex.Gamma (((1 / 2 : ℝ) : ℂ) + T * I)) := by
    rw [← Complex.Gamma_conj]; congr 1; apply Complex.ext <;> simp; norm_num
  have h3 : Complex.sin (Real.pi * (((1 / 2 : ℝ) : ℂ) + T * I)) =
      ((Real.cosh (Real.pi * T) : ℝ) : ℂ) := by
    have : (Real.pi : ℂ) * (((1 / 2 : ℝ) : ℂ) + T * I) = Real.pi / 2 + ((Real.pi * T : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.sin_add, cos_mul_I, sin_mul_I]
    have e1 : Complex.cos (↑Real.pi / 2) = 0 := by
      rw [← ofReal_ofNat, ← ofReal_div, ← ofReal_cos]; simp
    have e2 : Complex.sin (↑Real.pi / 2) = 1 := by
      rw [← ofReal_ofNat, ← ofReal_div, ← ofReal_sin]; simp
    rw [e1, e2, ofReal_cosh]; ring
  rw [h2, Complex.mul_conj', h3] at h1
  have hc : 0 < Real.cosh (Real.pi * T) := Real.cosh_pos _
  have h4 : ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + T * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * T) := by
    apply Complex.ofReal_injective; rw [ofReal_pow, h1]; exact (ofReal_div _ _).symm
  have h5 : Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + T * I)‖ =
      (1 / 2) * (Real.log Real.pi - Real.log (Real.cosh (Real.pi * T))) := by
    rw [← Real.log_div Real.pi_ne_zero hc.ne', ← h4, Real.log_pow]; push_cast; ring
  simp only [Ψ]
  rw [h5, Real.Gamma_one_half_eq, Real.log_sqrt Real.pi_pos.le]
  ring

lemma Ψ_one (T : ℝ) (hT : 0 < T) :
    Ψ T 1 = (1 / 2) * (Real.log (Real.sinh (Real.pi * T)) - Real.log (Real.pi * T)) := by
  have h1 := LHFE0.gamma_norm_sq T hT.ne'
  have h2 : ‖Complex.Gamma (((1 : ℝ) : ℂ) + T * I)‖ = ‖Complex.Gamma (1 - T * I)‖ := by
    rw [← RCLike.norm_conj, ← Complex.Gamma_conj]; congr 2; simp [conj_ofReal]; ring
  have hs : 0 < Real.sinh (Real.pi * T) := Real.sinh_pos_iff.mpr (by positivity)
  have h5 : Real.log ‖Complex.Gamma (((1 : ℝ) : ℂ) + T * I)‖ =
      (1 / 2) * (Real.log (Real.pi * T) - Real.log (Real.sinh (Real.pi * T))) := by
    rw [h2, ← Real.log_div (by positivity) hs.ne', ← h1, Real.log_pow]; push_cast; ring
  simp only [Ψ]
  rw [h5, Real.Gamma_one, Real.log_one]
  ring

/-- the main term -/
noncomputable def L (T σ : ℝ) : ℝ := Real.pi * T / 2 - (σ - 1 / 2) * Real.log T

lemma log_cosh_bounds (x : ℝ) (hx : 0 ≤ x) :
    x - Real.log 2 ≤ Real.log (Real.cosh x) ∧ Real.log (Real.cosh x) ≤ x := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have he : 0 < Real.exp x := Real.exp_pos x
  have hn : 0 < Real.exp (-x) := Real.exp_pos _
  have hn1 : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  constructor
  · rw [show x - Real.log 2 = Real.log (Real.exp x / 2) by
      rw [Real.log_div he.ne' (by norm_num), Real.log_exp]]
    apply Real.log_le_log (by positivity); linarith
  · calc Real.log ((Real.exp x + Real.exp (-x)) / 2) ≤ Real.log (Real.exp x) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = x := Real.log_exp x

lemma log_sinh_bounds (x : ℝ) (hx : 1 ≤ x) :
    x - 2 * Real.log 2 ≤ Real.log (Real.sinh x) ∧ Real.log (Real.sinh x) ≤ x - Real.log 2 := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have hn : 0 < Real.exp (-x) := Real.exp_pos _
  have hn1 : 2 * Real.exp (-x) ≤ Real.exp x := by
    have : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h2 : 2 ≤ Real.exp x := by
      have := Real.add_one_le_exp x; linarith
    nlinarith
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr (by linarith)
  rw [Real.sinh_eq] at hs ⊢
  constructor
  · rw [show x - 2 * Real.log 2 = Real.log (Real.exp x / 4) by
      rw [Real.log_div he.ne' (by norm_num), Real.log_exp,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by positivity); linarith
  · rw [show x - Real.log 2 = Real.log (Real.exp x / 2) by
      rw [Real.log_div he.ne' (by norm_num), Real.log_exp]]
    apply Real.log_le_log hs; linarith

lemma E_half (T : ℝ) (hT : 1 ≤ T) : |Ψ T (1 / 2) - L T (1 / 2)| ≤ 1 / 2 := by
  rw [Ψ_half, L]
  have := log_cosh_bounds (Real.pi * T) (by have := Real.pi_pos; positivity)
  have hl2 := Real.log_two_lt_d9
  rw [abs_le]; constructor <;> nlinarith

lemma E_one (T : ℝ) (hT : 1 ≤ T) : |Ψ T 1 - L T 1| ≤ 2 := by
  have hT0 : 0 < T := by linarith
  rw [Ψ_one T hT0, L, Real.log_mul Real.pi_ne_zero hT0.ne']
  have := log_sinh_bounds (Real.pi * T) (by nlinarith [Real.pi_gt_three])
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hlp : Real.log Real.pi ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log Real.pi_pos (by norm_num; linarith [Real.pi_lt_four])
  have hlp0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [abs_le]; constructor <;> nlinarith

lemma E_three_half (T : ℝ) (hT : 1 ≤ T) : |Ψ T (3 / 2) - L T (3 / 2)| ≤ 2 := by
  have hT0 : 0 < T := by linarith
  have e := Ψ_shift T (1 / 2) (by norm_num) hT0.ne'
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at e
  rw [e]
  have h1 := E_half T hT
  have hn : ‖(((1 / 2 : ℝ)) : ℂ) + T * I‖ = Real.sqrt (1 / 4 + T ^ 2) := by
    rw [Complex.norm_add_mul_I]; norm_num
  rw [hn, Real.log_sqrt (by positivity)]
  have hlT : 2 * Real.log T = Real.log (T ^ 2) := by rw [Real.log_pow]; push_cast; ring
  have hl1 : 2 * Real.log T ≤ Real.log (1 / 4 + T ^ 2) := by
    rw [hlT]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hl2 : Real.log (1 / 4 + T ^ 2) ≤ 2 * Real.log T + Real.log 2 := by
    rw [hlT, ← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hh : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hh]
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  simp only [L] at h1 ⊢
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith [h1.1, h1.2]

lemma E_bound (T σ : ℝ) (hT : 1 ≤ T) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    |Ψ T σ - L T σ| ≤ 10 := by
  have h12 := E_half T hT
  have h1 := E_one T hT
  have h32 := E_three_half T hT
  rw [abs_le] at h12 h1 h32 ⊢
  have hc := (Ψ_convex T).2
  have hL : ∀ a b x y : ℝ, a + b = 1 → L T (a * x + b * y) = a * L T x + b * L T y := by
    intro a b x y hab; simp only [L]
    have : b = 1 - a := by linarith
    subst this; ring
  have pos : ∀ x : ℝ, 1 / 2 ≤ x → x ∈ Ioi (0 : ℝ) := fun x hx => by
    simp only [mem_Ioi]; linarith
  rcases le_total σ 1 with hs | hs
  · -- σ ∈ [1/2, 1]
    -- upper: σ = (2 - 2σ) * (1/2) + (2σ - 1) * 1
    have hu := hc (pos _ le_rfl) (pos 1 (by norm_num)) (show 0 ≤ 2 - 2 * σ by linarith)
      (show 0 ≤ 2 * σ - 1 by linarith) (by ring)
    simp only [smul_eq_mul] at hu
    have e1 : (2 - 2 * σ) * (1 / 2) + (2 * σ - 1) * 1 = σ := by ring
    rw [e1] at hu
    have hLu := hL (2 - 2 * σ) (2 * σ - 1) (1 / 2) 1 (by ring)
    rw [e1] at hLu
    -- lower: 1 = u * σ + (1 - u) * (3/2), u = 1 / (3 - 2σ)
    have hd : 0 < 3 - 2 * σ := by linarith
    set u := 1 / (3 - 2 * σ) with hu_def
    have hu0 : 0 ≤ u := by positivity
    have hu1 : u ≤ 1 := by rw [hu_def, div_le_one hd]; linarith
    have hu2 : 1 / 2 ≤ u := by rw [hu_def, le_div_iff₀ hd]; linarith
    have hl := hc (pos σ hσ1) (pos (3 / 2) (by norm_num)) hu0 (show 0 ≤ 1 - u by linarith)
      (by ring)
    simp only [smul_eq_mul] at hl
    have e2 : u * σ + (1 - u) * (3 / 2) = 1 := by
      rw [hu_def]; field_simp; ring
    rw [e2] at hl
    have hLl := hL u (1 - u) σ (3 / 2) (by ring)
    rw [e2] at hLl
    constructor
    · nlinarith
    · nlinarith
  · -- σ ∈ [1, 3/2]
    have hu := hc (pos 1 (by norm_num)) (pos (3 / 2) (by norm_num)) (show 0 ≤ 3 - 2 * σ by linarith)
      (show 0 ≤ 2 * σ - 2 by linarith) (by ring)
    simp only [smul_eq_mul] at hu
    have e1 : (3 - 2 * σ) * 1 + (2 * σ - 2) * (3 / 2) = σ := by ring
    rw [e1] at hu
    have hLu := hL (3 - 2 * σ) (2 * σ - 2) 1 (3 / 2) (by ring)
    rw [e1] at hLu
    -- lower: 1 = (1 - u) * (1/2) + u * σ, u = 1 / (2σ - 1)
    have hd : 0 < 2 * σ - 1 := by linarith
    set u := 1 / (2 * σ - 1) with hu_def
    have hu0 : 0 ≤ u := by positivity
    have hu1 : u ≤ 1 := by rw [hu_def, div_le_one hd]; linarith
    have hu2 : 1 / 2 ≤ u := by rw [hu_def, le_div_iff₀ hd]; linarith
    have hl := hc (pos (1 / 2) le_rfl) (pos σ hσ1) (show 0 ≤ 1 - u by linarith) hu0 (by ring)
    simp only [smul_eq_mul] at hl
    have e2 : (1 - u) * (1 / 2) + u * σ = 1 := by
      rw [hu_def]; field_simp; ring
    rw [e2] at hl
    have hLl := hL (1 - u) u (1 / 2) σ (by ring)
    rw [e2] at hLl
    constructor
    · nlinarith
    · nlinarith

end LHGV


open Complex Filter Asymptotics Topology Set

namespace LZ1

open LHBound

/-- the correction terms `e_n(s) = n^{-s} - ∫_n^{n+1} x^{-s} dx`, indexed from `n+1`. -/
noncomputable def e (s : ℂ) (n : ℕ) : ℂ :=
  ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (F s ((n : ℝ) + 1 + 1) - F s ((n : ℝ) + 1))

lemma e_bound (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) (hσ : 0 ≤ s.re) (n : ℕ) :
    ‖e s n‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) :=
  step2 s hs hs1 hσ ((n : ℝ) + 1) (by have := n.cast_nonneg (α := ℝ); linarith)

lemma summable_shift (a : ℝ) (ha : 1 < a) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-a)) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -a < -1 by linarith))
  simpa using this

lemma rpow_mono (n : ℕ) {a b : ℝ} (hab : a ≤ b) : ((n : ℝ) + 1) ^ a ≤ ((n : ℝ) + 1) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by have := n.cast_nonneg (α := ℝ); linarith) hab

lemma F_tendsto (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => F s ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-s + 1).re) atTop (𝓝 0) := by
    have hneg : (-s + 1).re < 0 := by simp; linarith
    have := (tendsto_rpow_neg_atTop (y := -(-s + 1).re) (by linarith)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa [Function.comp_def] using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : (fun N : ℕ => ‖F s ((N : ℝ) + 1)‖) =
      fun N : ℕ => ((N : ℝ) + 1) ^ (-s + 1).re / ‖-s + 1‖ := by
    funext N
    unfold F
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rw [this]
  simpa using h1.div_const ‖-s + 1‖

lemma zeta_eq_gt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = 1 / (s - 1) + ∑' n, e s n := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) ^ s =
      e s n + (F s ((n : ℝ) + 1 + 1) - F s ((n : ℝ) + 1)) := by
    intro n
    simp only [e]
    rw [cpow_neg, one_div]; push_cast; ring
  simp_rw [hterm]
  have hsum_e : Summable (fun n => e s n) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1))
      ((summable_shift (s.re + 1) (by linarith)).mul_left ‖s‖ |>.congr (fun n => by ring_nf)) ?_
    intro n; exact e_bound s hs0 hs1 (by linarith) n
  have hsum_p : Summable (fun n : ℕ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re))
      (summable_shift s.re hs) ?_
    intro n
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
  have hsum_b : Summable (fun n : ℕ => F s ((n : ℝ) + 1 + 1) - F s ((n : ℝ) + 1)) := by
    refine (hsum_p.sub hsum_e).congr (fun n => ?_)
    simp only [e]; ring
  have htel : ∑' n : ℕ, (F s ((n : ℝ) + 1 + 1) - F s ((n : ℝ) + 1)) = -F s 1 := by
    have h1 := hsum_b.hasSum.tendsto_sum_nat
    have h2 : (fun N : ℕ => ∑ i ∈ Finset.range N, (F s ((i : ℝ) + 1 + 1) - F s ((i : ℝ) + 1)))
        = fun N : ℕ => F s ((N : ℝ) + 1) - F s 1 := by
      funext N
      have := Finset.sum_range_sub (fun i : ℕ => F s ((i : ℝ) + 1)) N
      simp only [Nat.cast_add, Nat.cast_one] at this
      rw [this]; simp
    rw [h2] at h1
    have h3 : Tendsto (fun N : ℕ => F s ((N : ℝ) + 1) - F s 1) atTop (𝓝 (0 - F s 1)) :=
      (F_tendsto s hs).sub tendsto_const_nhds
    rw [zero_sub] at h3
    exact tendsto_nhds_unique h1 h3
  rw [Summable.tsum_add hsum_e hsum_b, htel]
  have : F s 1 = 1 / (-s + 1) := by simp [F]
  rw [this]
  have hne : (-s + 1) ≠ 0 := by intro h; apply hs1; linear_combination -h
  have hne2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- bounded convex region -/
def Ω (K : ℝ) : Set ℂ := {s | 1 / 4 < s.re ∧ s.re < K ∧ 1 < s.im ∧ s.im < K}

lemma Ω_open (K : ℝ) : IsOpen (Ω K) := by
  unfold Ω
  refine (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)))

lemma Ω_convex (K : ℝ) : Convex ℝ (Ω K) := by
  unfold Ω
  have h1 : Convex ℝ {s : ℂ | 1 / 4 < s.re} := convex_halfSpace_gt reLm.isLinear _
  have h2 : Convex ℝ {s : ℂ | s.re < K} := convex_halfSpace_lt reLm.isLinear _
  have h3 : Convex ℝ {s : ℂ | 1 < s.im} := convex_halfSpace_gt imLm.isLinear _
  have h4 : Convex ℝ {s : ℂ | s.im < K} := convex_halfSpace_lt imLm.isLinear _
  exact h1.inter (h2.inter (h3.inter h4))

lemma e_diff (n : ℕ) (K : ℝ) : DifferentiableOn ℂ (fun s => e s n) (Ω K) := by
  intro s hs
  have hs1 : -s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [hs.2.2.1]
  apply DifferentiableAt.differentiableWithinAt
  unfold e F
  have hpos : ∀ x : ℝ, 0 < x → DifferentiableAt ℂ (fun s : ℂ => ((x : ℂ)) ^ (-s + 1)) s := by
    intro x hx
    exact (differentiableAt_id.neg.add_const 1).const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hpos' : ∀ x : ℝ, 0 < x → DifferentiableAt ℂ (fun s : ℂ => ((x : ℂ)) ^ (-s)) s := by
    intro x hx
    exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hd : DifferentiableAt ℂ (fun s : ℂ => -s + 1) s := differentiableAt_id.neg.add_const 1
  exact (hpos' _ (by positivity)).sub (((hpos _ (by positivity)).div hd hs1).sub
    ((hpos _ (by positivity)).div hd hs1))

lemma G_diff (K : ℝ) : DifferentiableOn ℂ (fun s => 1 / (s - 1) + ∑' n, e s n) (Ω K) := by
  have hsum : DifferentiableOn ℂ (fun s => ∑' n, e s n) (Ω K) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => (2 * |K|) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
      ((summable_shift (5 / 4) (by norm_num)).mul_left _) (fun n => e_diff n K) (Ω_open K) ?_
    intro n s hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at h3; simp at h3; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at h3; simp at h3; linarith
    refine (e_bound s hs0 hs1 (by linarith) n).trans ?_
    have hn : ‖s‖ ≤ 2 * |K| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
        _ ≤ 2 * |K| := by
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
          have := le_abs_self K; linarith
    exact mul_le_mul hn (rpow_mono n (by linarith)) (by positivity) (by positivity)
  refine DifferentiableOn.add ?_ hsum
  intro s hs
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [hs.2.2.1]
  have : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1
  exact this.differentiableWithinAt

lemma zeta_eq (s : ℂ) (hs : 1 / 4 < s.re) (hs' : 1 < s.im) :
    riemannZeta s = 1 / (s - 1) + ∑' n, e s n := by
  set K : ℝ := |s.re| + |s.im| + 3
  have hK : s ∈ Ω K := ⟨hs, by have := le_abs_self s.re; have := abs_nonneg s.im; linarith,
    hs', by have := le_abs_self s.im; have := abs_nonneg s.re; linarith⟩
  have hz : (2 + 2 * I : ℂ) ∈ Ω K := by
    refine ⟨by simp; norm_num, ?_, by simp, ?_⟩ <;> simp <;>
      linarith [abs_nonneg s.re, abs_nonneg s.im]
  have hζ : DifferentiableOn ℂ riemannZeta (Ω K) := by
    intro z hz
    have : z ≠ 1 := by intro h; rw [h] at hz; have := hz.2.2.1; simp at this; linarith
    exact (differentiableAt_riemannZeta this).differentiableWithinAt
  have hev : riemannZeta =ᶠ[𝓝 (2 + 2 * I)] fun s => 1 / (s - 1) + ∑' n, e s n := by
    have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 + 2 * I : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [this] with z hz
    exact zeta_eq_gt z hz
  exact (hζ.analyticOnNhd (Ω_open K)).eqOn_of_preconnected_of_eventuallyEq
    ((G_diff K).analyticOnNhd (Ω_open K)) (Ω_convex K).isPreconnected hz hev hK

end LZ1


open Complex Filter Asymptotics Topology Set ComplexConjugate

namespace LZ2

open LZ1 LHBound

noncomputable def S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))

lemma S_nonneg : 0 ≤ S := tsum_nonneg (fun n => by positivity)

lemma right_bound (s : ℂ) (h1 : 1 / 2 ≤ s.re) (h2 : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ 1 + S * ‖s‖ := by
  rw [zeta_eq s (by linarith) (by linarith)]
  have hs0 : s ≠ 0 := by intro h; rw [h] at h2; simp at h2; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at h2; simp at h2; linarith
  have hsumb : Summable (fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
    ((summable_shift (s.re + 1) (by linarith)).mul_left ‖s‖).congr (fun n => by ring_nf)
  have hb := fun n => e_bound s hs0 hs1 (by linarith) n
  have hnorm : Summable (fun n => ‖e s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsumb
  have h32 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) :=
    summable_shift (3 / 2) (by norm_num)
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have : 2 ≤ ‖s - 1‖ := by
      have := abs_im_le_norm (s - 1); simp at this
      have h' : |s.im| = s.im := abs_of_pos (by linarith)
      linarith
    rw [div_le_one (by linarith)]; linarith
  calc ‖1 / (s - 1) + ∑' n, e s n‖ ≤ ‖1 / (s - 1)‖ + ‖∑' n, e s n‖ := norm_add_le _ _
    _ ≤ 1 + ∑' n : ℕ, ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) :=
        add_le_add hinv ((norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hb hsumb))
    _ ≤ 1 + S * ‖s‖ := by
        rw [tsum_mul_left, mul_comm]
        gcongr
        exact Summable.tsum_le_tsum (fun n => rpow_mono n (by linarith))
          ((summable_shift (s.re + 1) (by linarith)).congr (fun n => by ring_nf)) h32

lemma gamma_le (σ : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) : Real.Gamma σ ≤ 2 := by
  have hc := Real.convexOn_Gamma.le_max_of_mem_Icc (x := 1 / 2) (y := 3 / 2)
    (by norm_num) (by norm_num) ⟨h1, h2⟩
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_lt_four]
  have e1 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have e2 : Real.Gamma (3 / 2) = 1 / 2 * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), e1]
  rw [e1, e2] at hc
  have : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  exact hc.trans (max_le hpi (by linarith))

lemma gamma_norm_le (σ T : ℝ) (hT : 1 ≤ T) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) :
    ‖Complex.Gamma ((σ : ℂ) + T * I)‖ ≤ 2 * Real.exp 10 * T * Real.exp (-(Real.pi * T / 2)) := by
  have hE := LHGV.E_bound T σ hT h1 h2
  unfold LHGV.Ψ LHGV.L at hE
  rw [abs_le] at hE
  have hpos : 0 < ‖Complex.Gamma ((σ : ℂ) + T * I)‖ :=
    norm_pos_iff.2 (LHGV.Gamma_ne σ T (by linarith))
  have hG : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have key : Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖ ≤
      Real.log (Real.Gamma σ) + 10 + (-(Real.pi * T / 2)) + Real.log T := by
    have : (σ - 1 / 2) * Real.log T ≤ Real.log T := by nlinarith
    linarith [hE.1]
  calc ‖Complex.Gamma ((σ : ℂ) + T * I)‖
      = Real.exp (Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log (Real.Gamma σ) + 10 + (-(Real.pi * T / 2)) + Real.log T) :=
        Real.exp_le_exp.2 key
    _ = Real.Gamma σ * Real.exp 10 * Real.exp (-(Real.pi * T / 2)) * T := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hG,
          Real.exp_log (by linarith)]
    _ ≤ 2 * Real.exp 10 * T * Real.exp (-(Real.pi * T / 2)) := by
        have := gamma_le σ h1 h2
        have h0 : 0 ≤ Real.exp 10 * Real.exp (-(Real.pi * T / 2)) * T := by positivity
        nlinarith

lemma cos_norm_sq (a b : ℝ) :
    ‖Complex.cos ((a : ℂ) - b * I)‖ = Real.sqrt (Real.cos a ^ 2 + Real.sinh b ^ 2) := by
  have e : Complex.cos ((a : ℂ) - b * I) =
      ((Real.cos a * Real.cosh b : ℝ) : ℂ) + ((Real.sin a * Real.sinh b : ℝ) : ℂ) * I := by
    rw [Complex.cos_sub, cos_mul_I, sin_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cosh,
      ← ofReal_sinh]
    push_cast; ring
  rw [e, Complex.norm_add_mul_I]
  congr 1
  have h1 := Real.cosh_sq b
  have h2 := Real.sin_sq_add_cos_sq a
  rw [mul_pow, mul_pow, h1]
  linear_combination (Real.sinh b ^ 2) * h2

lemma cos_le (a b : ℝ) (hb : 1 ≤ b) :
    ‖Complex.cos ((a : ℂ) - b * I)‖ ≤ Real.exp b := by
  rw [cos_norm_sq]
  have he : 0 < Real.exp b := Real.exp_pos b
  have hn : 0 < Real.exp (-b) := Real.exp_pos _
  have hprod : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add]; simp
  have h2 : 2 ≤ Real.exp b := by have := Real.add_one_le_exp b; linarith
  have hsh : Real.exp b / 4 ≤ Real.sinh b := by
    rw [Real.sinh_eq]; nlinarith
  have hsh0 : 0 ≤ Real.sinh b := by linarith [div_pos he (by norm_num : (0:ℝ) < 4)]
  have hsh1 : Real.sinh b ≤ Real.exp b / 2 := by rw [Real.sinh_eq]; linarith
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.cos_sq_le_one a]

/-- the functional equation in absolute values -/
lemma zeta_rel (σ T : ℝ) (hT : 1 ≤ T) :
    ‖riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)‖ =
      2 * (2 * Real.pi) ^ (-σ) * ‖Complex.Gamma ((σ : ℂ) + T * I)‖ *
        ‖Complex.cos ((((Real.pi * σ / 2 : ℝ)) : ℂ) - ((Real.pi * T / 2 : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta ((σ : ℂ) + T * I)‖ := by
  set s : ℂ := (σ : ℂ) - T * I with hsdef
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [hsdef] at this; linarith
  have hsn : ∀ n : ℕ, s ≠ -n := by
    intro n h; have := congrArg Complex.im h; simp [hsdef] at this; linarith
  have hfe := riemannZeta_one_sub hsn hs1
  have e1 : 1 - s = ((1 - σ : ℝ) : ℂ) + T * I := by simp [hsdef]; ring
  have e2 : riemannZeta s = conj (riemannZeta ((σ : ℂ) + T * I)) := by
    rw [← riemannZeta_conj]; congr 1; simp [hsdef, conj_ofReal]; ring
  have e3 : Complex.Gamma s = conj (Complex.Gamma ((σ : ℂ) + T * I)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [hsdef, conj_ofReal]; ring
  have e4 : (Real.pi : ℂ) * s / 2 = (((Real.pi * σ / 2 : ℝ)) : ℂ) - ((Real.pi * T / 2 : ℝ) : ℂ) * I := by
    simp [hsdef]; push_cast; ring
  rw [e1] at hfe
  rw [hfe, e2, e3, e4, norm_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h2pi : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-σ) := by
    have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hsdef]
  rw [h2pi]
  simp

lemma left_bound (σ T : ℝ) (h1 : -1 / 2 ≤ σ) (h2 : σ ≤ 1 / 2) (hT : 2 ≤ T) :
    ‖riemannZeta ((σ : ℂ) + T * I)‖ ≤
      4 * Real.exp 10 * T * (1 + S * ‖(((1 - σ : ℝ)) : ℂ) + T * I‖) := by
  have hr := zeta_rel (1 - σ) T (by linarith)
  rw [show (((1 - (1 - σ) : ℝ)) : ℂ) = σ by push_cast; ring] at hr
  rw [hr]
  have hpi1 : (2 * Real.pi) ^ (-(1 - σ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hg := gamma_norm_le (1 - σ) T (by linarith) (by linarith) (by linarith)
  have hc := cos_le (Real.pi * (1 - σ) / 2) (Real.pi * T / 2) (by nlinarith [Real.pi_gt_three])
  have hz := right_bound ((((1 - σ : ℝ)) : ℂ) + T * I) (by simp; linarith) (by simp; linarith)
  have hexp : Real.exp (-(Real.pi * T / 2)) * Real.exp (Real.pi * T / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h0 : 0 ≤ (2 * Real.pi) ^ (-(1 - σ)) := by positivity
  have hzn : 0 ≤ ‖riemannZeta ((((1 - σ : ℝ)) : ℂ) + T * I)‖ := norm_nonneg _
  have hgn : 0 ≤ ‖Complex.Gamma ((((1 - σ : ℝ)) : ℂ) + T * I)‖ := norm_nonneg _
  have hcn : 0 ≤ ‖Complex.cos ((((Real.pi * (1 - σ) / 2 : ℝ)) : ℂ) -
      ((Real.pi * T / 2 : ℝ) : ℂ) * I)‖ := norm_nonneg _
  calc 2 * (2 * Real.pi) ^ (-(1 - σ)) * ‖Complex.Gamma ((((1 - σ : ℝ)) : ℂ) + T * I)‖ *
        ‖Complex.cos ((((Real.pi * (1 - σ) / 2 : ℝ)) : ℂ) - ((Real.pi * T / 2 : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta ((((1 - σ : ℝ)) : ℂ) + T * I)‖
      ≤ 2 * 1 * (2 * Real.exp 10 * T * Real.exp (-(Real.pi * T / 2))) *
          Real.exp (Real.pi * T / 2) * (1 + S * ‖(((1 - σ : ℝ)) : ℂ) + T * I‖) := by
        gcongr
    _ = 4 * Real.exp 10 * T * (1 + S * ‖(((1 - σ : ℝ)) : ℂ) + T * I‖) := by
        rw [show 2 * 1 * (2 * Real.exp 10 * T * Real.exp (-(Real.pi * T / 2))) *
          Real.exp (Real.pi * T / 2) = 4 * Real.exp 10 * T *
          (Real.exp (-(Real.pi * T / 2)) * Real.exp (Real.pi * T / 2)) by ring, hexp, mul_one]

noncomputable def B : ℝ := 4 * Real.exp 10 * (1 + S)

lemma unified (z : ℂ) (h1 : -1 / 2 ≤ z.re) (h2 : z.re ≤ 9 / 2) (h3 : 2 ≤ z.im) :
    ‖riemannZeta z‖ ≤ B * (z.im + 5) ^ 2 := by
  have hS := S_nonneg
  have he : 1 ≤ Real.exp 10 := Real.one_le_exp (by norm_num)
  set t := z.im
  have ht5 : 1 ≤ t + 5 := by linarith
  have hsq : t + 5 ≤ (t + 5) ^ 2 := by nlinarith
  by_cases hr : 1 / 2 ≤ z.re
  · have hb := right_bound z hr h3
    have hn : ‖z‖ ≤ t + 5 := by
      have := norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith : 0 < t)] at this
      have : |z.re| ≤ 9 / 2 := abs_le.2 ⟨by linarith, h2⟩
      linarith
    calc ‖riemannZeta z‖ ≤ 1 + S * ‖z‖ := hb
      _ ≤ (1 + S) * (t + 5) := by nlinarith
      _ ≤ (1 + S) * (t + 5) ^ 2 := by nlinarith
      _ ≤ B * (t + 5) ^ 2 := by
          unfold B; have : 0 ≤ (1 + S) * (t + 5) ^ 2 := by positivity
          nlinarith
  · push Not at hr
    have hz : z = ((z.re : ℝ) : ℂ) + (t : ℂ) * I := (Complex.re_add_im z).symm
    have hb := left_bound z.re t h1 hr.le h3
    rw [← hz] at hb
    have hn : ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖ ≤ t + 5 := by
      have := norm_le_abs_re_add_abs_im ((((1 - z.re : ℝ)) : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at this
      rw [abs_of_pos (by linarith : 0 < t), abs_of_pos (by linarith : (0:ℝ) < 1 - z.re)] at this
      linarith
    calc ‖riemannZeta z‖ ≤ 4 * Real.exp 10 * t * (1 + S * ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖) := hb
      _ ≤ 4 * Real.exp 10 * (t + 5) * ((1 + S) * (t + 5)) := by
          have h0 : 0 ≤ 4 * Real.exp 10 := by positivity
          have hA : 1 + S * ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖ ≤ (1 + S) * (t + 5) := by nlinarith
          have hA0 : 0 ≤ 1 + S * ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖ := by positivity
          calc 4 * Real.exp 10 * t * (1 + S * ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖)
              ≤ 4 * Real.exp 10 * (t + 5) * (1 + S * ‖(((1 - z.re : ℝ)) : ℂ) + t * I‖) := by
                gcongr; linarith
            _ ≤ _ := by gcongr
      _ = B * (t + 5) ^ 2 := by unfold B; ring

end LZ2


open Complex Filter Asymptotics Topology Set ComplexConjugate

namespace LZ3

open LZ2

lemma zero_re (s : ℂ) (hz : riemannZeta s = 0) (him : 1 ≤ s.im) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    push Not at h
    have hr := zeta_rel (1 - s.re) s.im him
    have hs : (((1 - (1 - s.re) : ℝ)) : ℂ) + s.im * I = s := by
      rw [show (1 - (1 - s.re) : ℝ) = s.re by ring]; exact Complex.re_add_im s
    rw [hs, hz, norm_zero] at hr
    have h1 : 0 < (2 * Real.pi) ^ (-(1 - s.re)) := by positivity
    have h2 : 0 < ‖Complex.Gamma (((1 - s.re : ℝ) : ℂ) + s.im * I)‖ :=
      norm_pos_iff.2 (LHGV.Gamma_ne _ _ (by linarith))
    have h3 : 0 < ‖Complex.cos ((((Real.pi * (1 - s.re) / 2 : ℝ)) : ℂ) -
        ((Real.pi * s.im / 2 : ℝ) : ℂ) * I)‖ := by
      rw [cos_norm_sq]
      apply Real.sqrt_pos.2
      have : 0 < Real.sinh (Real.pi * s.im / 2) :=
        Real.sinh_pos_iff.2 (by have := Real.pi_pos; positivity)
      positivity
    have h4 : 0 < ‖riemannZeta (((1 - s.re : ℝ) : ℂ) + s.im * I)‖ :=
      norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
    have : 0 < 2 * (2 * Real.pi) ^ (-(1 - s.re)) *
        ‖Complex.Gamma (((1 - s.re : ℝ) : ℂ) + s.im * I)‖ *
        ‖Complex.cos ((((Real.pi * (1 - s.re) / 2 : ℝ)) : ℂ) -
          ((Real.pi * s.im / 2 : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta (((1 - s.re : ℝ) : ℂ) + s.im * I)‖ := by positivity
    linarith
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

lemma zeta_two_line (t : ℝ) : 1 / 3 ≤ ‖riemannZeta (2 + t * I)‖ := by
  set c : ℂ := 2 + t * I
  have hc : 1 < c.re := by simp [c]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hc]
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ c‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_div, norm_one, norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [c]
  have hsum2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1 + 1) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).2 hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    have e1 : (fun n : ℕ => 1 / ((n : ℝ) + 1 + 1) ^ 2) = fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
      funext n; push_cast; ring_nf
    rw [e1]
    have h0 : ((0 : ℝ) + 1 / ((0 : ℕ) : ℝ) ^ 2 + 1 / ((1 : ℕ) : ℝ) ^ 2) = 1 := by norm_num
    rw [h0] at this
    exact this
  have hsumN : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ c) := by
    refine Summable.of_norm ?_
    simp_rw [hnorm]
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using this
  rw [hsumN.tsum_eq_zero_add]
  have hfirst : 1 / (((0 : ℕ) : ℂ) + 1) ^ c = 1 := by simp
  rw [hfirst]
  have hs' : Summable (fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ c‖) := by
    have := (summable_nat_add_iff 1).2 hsumN.norm
    exact this
  have hb : ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ c‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq ?_)
    rw [← hsum2.tsum_eq]
    congr 1; funext n; rw [hnorm]; push_cast; ring_nf
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
    have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ c))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

end LZ3


open Complex Filter Asymptotics Topology Set Metric
open scoped ENNReal

namespace LZ3

open LZ2

lemma B_ge : 4 ≤ B := by
  unfold B
  have := S_nonneg
  have he : 1 ≤ Real.exp 10 := Real.one_le_exp (by norm_num)
  nlinarith

lemma key (T : ℝ) (hT : 4 ≤ T) :
    (LindelofHypothesis.zeroCountWindowAll T : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.log (B * (T + 8) ^ 2 / (1 / 3)) / Real.log ((5 / 2) / (21 / 10))) := by
  set c : ℂ := 2 + ((T + 1 / 2 : ℝ) : ℂ) * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = T + 1 / 2 := by simp [hc]
  set Z : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ T ≤ s.im ∧ s.im ≤ T + 1} with hZ
  have hZball : Z ⊆ closedBall c |21 / 10| := by
    intro s hs
    obtain ⟨h0, h1, h2⟩ := hs
    obtain ⟨hr0, hr1⟩ := zero_re s h0 (by linarith)
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖s - c‖ ^ 2 ≤ (21 / 10) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, sub_im, hcre, hcim]
      nlinarith
    rw [abs_of_pos (by norm_num)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by norm_num)).1 hsq
  have hfin : Z.Finite :=
    ((isCompact_closedBall c |21 / 10|).inter_riemannZetaZeros_finite).subset
      (fun s hs => ⟨hZball hs, hs.1⟩)
  have hne1 : ∀ z ∈ closedBall c |5 / 2|, z ≠ 1 := by
    intro z hz h
    rw [h, mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num)] at hz
    have := abs_im_le_norm (1 - c)
    simp only [sub_im, one_im, hcim] at this
    rw [abs_le] at this
    linarith [this.1, this.2]
  have hU : AnalyticOnNhd ℂ riemannZeta (closedBall c |5 / 2|) := by
    have hd : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact (hd.analyticOnNhd isOpen_compl_singleton).mono (fun z hz => hne1 z hz)
  have hc0 : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; norm_num)
  have hBp : 0 ≤ B := by linarith [B_ge]
  have hbound : ∀ z ∈ sphere c |5 / 2|, ‖riemannZeta z‖ ≤ B * (T + 8) ^ 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num)] at hz
    have hre := abs_re_le_norm (z - c)
    have him := abs_im_le_norm (z - c)
    simp only [sub_re, sub_im, hcre, hcim, hz] at hre him
    rw [abs_le] at hre him
    refine (unified z (by linarith) (by linarith) (by linarith)).trans ?_
    have h1 : z.im + 5 ≤ T + 8 := by linarith
    have h0 : 0 ≤ z.im + 5 := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hBp
  have hM : 1 ≤ B * (T + 8) ^ 2 := by
    have : 1 ≤ (T + 8) ^ 2 := by nlinarith
    nlinarith [B_ge]
  have J := hU.sum_divisor_le (r := 21 / 10) (by norm_num) (by norm_num) hM hc0 hbound
  have hlow := zeta_two_line (T + 1 / 2)
  have hcc : (2 : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I = c := rfl
  rw [hcc] at hlow
  have hlogR : 0 < Real.log ((5 / 2) / (21 / 10)) := Real.log_pos (by norm_num)
  have hJ2 : Real.log (B * (T + 8) ^ 2 / ‖riemannZeta c‖) / Real.log ((5 / 2) / (21 / 10)) ≤
      Real.log (B * (T + 8) ^ 2 / (1 / 3)) / Real.log ((5 / 2) / (21 / 10)) := by
    apply div_le_div_of_nonneg_right _ hlogR.le
    apply Real.log_le_log (div_pos (by linarith) (norm_pos_iff.2 hc0))
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hlow
  set D := MeromorphicOn.divisor riemannZeta (closedBall c |21 / 10|) with hDdef
  set F := hfin.toFinset with hF
  have hd1 : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := by
    have hd : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticOnNhd isOpen_compl_singleton
  have hord : ∀ s ∈ Z, analyticOrderAt riemannZeta s ≠ ⊤ := by
    intro s hs
    have hpre : IsPreconnected ({(1 : ℂ)}ᶜ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [(hd1 2 (by norm_num)).analyticOrderAt_eq_zero.2
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))]
      simp
    have hs1 : s ≠ 1 := by
      intro h; have := hs.2.1; rw [h] at this; simp at this; linarith
    exact hd1.analyticOrderAt_ne_top_of_isPreconnected hpre (by norm_num) hs1 h2
  have hU' : AnalyticOnNhd ℂ riemannZeta (closedBall c |21 / 10|) :=
    hU.mono (closedBall_subset_closedBall (by norm_num))
  have hD : ∀ s ∈ Z, D s = (analyticOrderNatAt riemannZeta s : ℤ) := by
    intro s hs
    rw [hDdef, MeromorphicOn.AnalyticOnNhd.divisor_apply hU' (hZball hs), ← Nat.cast_analyticOrderNatAt (hord s hs)]
    simp
  have hDnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hU' u
  have hsupp := D.finiteSupport (isCompact_closedBall c |21 / 10|)
  have hsum_le : (∑ s ∈ F, (analyticOrderNatAt riemannZeta s : ℤ)) ≤ ∑ᶠ u, D u := by
    rw [finsum_eq_sum_of_support_subset D (s := F ∪ hsupp.toFinset)
      (by intro u hu; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hu)]
    calc ∑ s ∈ F, (analyticOrderNatAt riemannZeta s : ℤ) = ∑ s ∈ F, D s :=
          Finset.sum_congr rfl (fun s hs => (hD s (hfin.mem_toFinset.1 hs)).symm)
      _ ≤ ∑ s ∈ F ∪ hsupp.toFinset, D s :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hDnn i)
  have hreal : (∑ s ∈ F, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
    exact_mod_cast hsum_le
  have hsetF : {s : ℂ | riemannZeta s = 0 ∧ T ≤ s.im ∧ s.im ≤ T + 1} = ((F : Finset ℂ) : Set ℂ) :=
    hfin.coe_toFinset.symm
  unfold LindelofHypothesis.zeroCountWindowAll
  rw [hsetF, Finset.tsum_subtype',
    Finset.sum_congr rfl (fun s hs => (Nat.cast_analyticOrderNatAt (hord s (hfin.mem_toFinset.1 hs))).symm),
    ← Nat.cast_sum, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  linarith

end LZ3

open LZ2 LZ3 in
theorem solution :
    ∃ C : ℝ, ∀ᶠ T in atTop, (LindelofHypothesis.zeroCountWindowAll T : ℝ≥0∞) ≤
      ENNReal.ofReal (C * Real.log T) := by
  set K : ℝ := Real.log (3 * B) + 2 * Real.log 2
  set ρ : ℝ := Real.log ((5 / 2) / (21 / 10))
  have hρ : 0 < ρ := Real.log_pos (by norm_num)
  refine ⟨(K + 2) / ρ, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
  refine (key T (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hB := B_ge
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ Real.log (3 * B) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have e1 : B * (T + 8) ^ 2 / (1 / 3) = (3 * B) * (T + 8) ^ 2 := by ring
  have hT8 : Real.log (T + 8) ≤ Real.log 2 + Real.log T := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog : Real.log (B * (T + 8) ^ 2 / (1 / 3)) ≤ (K + 2) * Real.log T := by
    rw [e1, Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast
    nlinarith
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hlog hρ.le
