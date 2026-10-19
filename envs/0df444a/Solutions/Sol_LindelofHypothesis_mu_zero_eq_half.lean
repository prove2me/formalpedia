-- Prove2me | solution 1 for LindelofHypothesis.mu_zero_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:54:24.704296+00:00
-- url     : https://prove2.me/submissions/85d3febb-1db9-428b-80a1-8133b1a4ee4a

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_one_eq_zero

open Complex Filter Asymptotics
open scoped ENNReal
open Topology Set ComplexConjugate
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

namespace LHMuZero

lemma upper (T : ℝ) (hT : 1 ≤ T) :
    ‖riemannZeta (T * I)‖ ≤ Real.sqrt T * ‖riemannZeta (1 + T * I)‖ := by
  rw [LHFE0.zeta_iT T (by linarith)]
  have hb := (LHFE0.c_bounds T hT).2
  have hc : 0 ≤ (1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)| := by
    have := Real.pi_pos; positivity
  have : (1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)| ≤ Real.sqrt T :=
    Real.le_sqrt_of_sq_le hb
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

lemma lower (T : ℝ) (hT : 1 ≤ T) :
    Real.sqrt T * ‖riemannZeta (1 + T * I)‖ ≤ 4 * ‖riemannZeta (T * I)‖ := by
  rw [LHFE0.zeta_iT T (by linarith)]
  have hb := (LHFE0.c_bounds T hT).1
  set c := (1 / Real.pi) * ‖Gamma (1 - T * I)‖ * |Real.sinh (Real.pi * T / 2)|
  have hc : 0 ≤ c := by have := Real.pi_pos; positivity
  have : Real.sqrt T ≤ 4 * c := by
    have h1 := Real.sqrt_le_sqrt hb
    rw [Real.sqrt_sq hc, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 16),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h1
    linarith
  calc Real.sqrt T * ‖riemannZeta (1 + T * I)‖ ≤ (4 * c) * ‖riemannZeta (1 + T * I)‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := by ring

end LHMuZero

open LindelofHypothesis in
theorem solution : mu 0 = ((1 / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · unfold mu
    refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
    obtain ⟨r, hr0, hrb⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hr : (1 / 2 : ℝ) < r := by exact_mod_cast hr0
    have hmem : r ∈ {a : ℝ | (fun T : ℝ => riemannZeta (((0 : ℝ) : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ a)} := by
      show (fun T : ℝ => riemannZeta (((0 : ℝ) : ℂ) + T * I)) =O[atTop] (fun T : ℝ => T ^ r)
      obtain ⟨C, hC⟩ := (LHBound.zeta_one_isBigO (r - 1 / 2) (by linarith)).bound
      refine IsBigO.of_bound C ?_
      filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with T h1 hT
      have hT0 : 0 < T := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0.le _)] at h1 ⊢
      have hu := LHMuZero.upper T hT
      have e : T ^ r = Real.sqrt T * T ^ (r - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT0]; congr 1; ring
      simp only [ofReal_zero, zero_add]
      rw [e]
      calc ‖riemannZeta (T * I)‖ ≤ Real.sqrt T * ‖riemannZeta (1 + T * I)‖ := hu
        _ ≤ Real.sqrt T * (C * T ^ (r - 1 / 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = C * (Real.sqrt T * T ^ (r - 1 / 2)) := by ring
    exact (sInf_le (Set.mem_image_of_mem _ hmem)).trans hrb.le
  · unfold mu
    apply le_sInf
    rintro _ ⟨a, ha, rfl⟩
    have ha' : (fun T : ℝ => riemannZeta (((0 : ℝ) : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ a) := ha
    obtain ⟨C, hC⟩ := ha'.bound
    have hb : (fun T : ℝ => riemannZeta (((1 : ℝ) : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ (a - 1 / 2)) := by
      refine IsBigO.of_bound (4 * C) ?_
      filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with T h1 hT
      have hT0 : 0 < T := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0.le _)] at h1 ⊢
      simp only [ofReal_zero, zero_add, ofReal_one] at h1 ⊢
      have hl := LHMuZero.lower T hT
      have e : T ^ a = Real.sqrt T * T ^ (a - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT0]; congr 1; ring
      have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
      rw [e] at h1
      have : Real.sqrt T * ‖riemannZeta (1 + T * I)‖ ≤
          Real.sqrt T * (4 * C * T ^ (a - 1 / 2)) := by nlinarith
      exact le_of_mul_le_mul_left this hs
    have h1 : mu 1 ≤ ((a - 1 / 2 : ℝ) : EReal) := by
      unfold mu; exact sInf_le ⟨a - 1 / 2, hb, rfl⟩
    rw [LindelofHypothesis.mu_one_eq_zero] at h1
    have : (0 : ℝ) ≤ a - 1 / 2 := by exact_mod_cast h1
    show ((1 / 2 : ℝ) : EReal) ≤ (a : EReal)
    exact_mod_cast (by linarith : (1 / 2 : ℝ) ≤ a)
