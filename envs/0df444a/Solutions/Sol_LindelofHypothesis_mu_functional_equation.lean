-- Prove2me | solution 1 for LindelofHypothesis.mu_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:07:39.9222+00:00
-- url     : https://prove2.me/submissions/e28b0701-afd4-4b47-9c80-532b412fe32f

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_mu_convex

open Complex Filter Asymptotics
open scoped ENNReal

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


open Complex Filter Topology Set ComplexConjugate

namespace LHGV

/-- two-sided vertical bound for `Γ` on the line `Re s = σ` -/
def Pb (σ : ℝ) : Prop := ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T →
  c * (T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2))) ≤ ‖Complex.Gamma ((σ : ℂ) + T * I)‖ ∧
  ‖Complex.Gamma ((σ : ℂ) + T * I)‖ ≤ C * (T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)))

lemma Pb_base (σ : ℝ) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) : Pb σ := by
  have hσ0 : 0 < σ := by linarith
  have hG := Real.Gamma_pos_of_pos hσ0
  refine ⟨Real.Gamma σ * Real.exp (-10), Real.Gamma σ * Real.exp 10, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hE := E_bound T σ hT hσ1 hσ2
  rw [abs_le] at hE
  have hn : 0 < ‖Complex.Gamma ((σ : ℂ) + T * I)‖ := norm_pos_iff.mpr (Gamma_ne σ T hσ0)
  have hform : ‖Complex.Gamma ((σ : ℂ) + T * I)‖ =
      Real.Gamma σ * Real.exp (-(Ψ T σ - L T σ)) *
        (T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2))) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    have : Ψ T σ = Real.log (Real.Gamma σ) - Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖ := rfl
    rw [this]
    simp only [L]
    have e : -(Real.log (Real.Gamma σ) - Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖ -
        (Real.pi * T / 2 - (σ - 1 / 2) * Real.log T)) +
        (Real.log T * (σ - 1 / 2) + -(Real.pi * T / 2)) =
        Real.log ‖Complex.Gamma ((σ : ℂ) + T * I)‖ - Real.log (Real.Gamma σ) := by ring
    rw [e, Real.exp_sub, Real.exp_log hn, Real.exp_log hG]
    field_simp
  have hpos : 0 < T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)) := by positivity
  rw [hform]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hpos.le
    apply mul_le_mul_of_nonneg_left _ hG.le
    exact Real.exp_le_exp.mpr (by linarith)
  · apply mul_le_mul_of_nonneg_right _ hpos.le
    apply mul_le_mul_of_nonneg_left _ hG.le
    exact Real.exp_le_exp.mpr (by linarith)

lemma norm_sT (σ T : ℝ) (hT : 1 ≤ T) :
    T ≤ ‖(σ : ℂ) + T * I‖ ∧ ‖(σ : ℂ) + T * I‖ ≤ (|σ| + 1) * T := by
  constructor
  · have := abs_im_le_norm ((σ : ℂ) + T * I)
    simp at this
    rwa [abs_of_pos (by linarith)] at this
  · have := norm_le_abs_re_add_abs_im ((σ : ℂ) + T * I)
    simp at this
    rw [abs_of_pos (show 0 < T by linarith)] at this
    nlinarith [abs_nonneg σ]

lemma gamma_succ (σ T : ℝ) (hT : 1 ≤ T) :
    ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + T * I)‖ =
      ‖(σ : ℂ) + T * I‖ * ‖Complex.Gamma ((σ : ℂ) + T * I)‖ := by
  have hs : (σ : ℂ) + T * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have e : ((σ + 1 : ℝ) : ℂ) + T * I = ((σ : ℂ) + T * I) + 1 := by push_cast; ring
  rw [e, Complex.Gamma_add_one _ hs, norm_mul]

lemma rpow_succ (σ T : ℝ) (hT : 1 ≤ T) : T ^ (σ + 1 - 1 / 2) = T * T ^ (σ - 1 / 2) := by
  rw [show σ + 1 - 1 / 2 = (σ - 1 / 2) + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
  ring

lemma Pb_up (σ : ℝ) (h : Pb σ) : Pb (σ + 1) := by
  obtain ⟨c, C, hc, hb⟩ := h
  refine ⟨c, (|σ| + 1) * C, hc, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hb T hT
  obtain ⟨n1, n2⟩ := norm_sT σ T hT
  rw [gamma_succ σ T hT, rpow_succ σ T hT]
  have hp : 0 ≤ T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)) := by
    have : 0 < T := by linarith
    positivity
  have hg : 0 ≤ ‖Complex.Gamma ((σ : ℂ) + T * I)‖ := norm_nonneg _
  constructor
  · calc c * (T * T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)))
        = T * (c * (T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)))) := by ring
      _ ≤ ‖(σ : ℂ) + T * I‖ * ‖Complex.Gamma ((σ : ℂ) + T * I)‖ :=
          mul_le_mul n1 h1 (by positivity) (norm_nonneg _)
  · calc ‖(σ : ℂ) + T * I‖ * ‖Complex.Gamma ((σ : ℂ) + T * I)‖
        ≤ ((|σ| + 1) * T) * (C * (T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)))) :=
          mul_le_mul n2 h2 hg (by positivity)
      _ = _ := by ring

lemma Pb_down (σ : ℝ) (h : Pb (σ + 1)) : Pb σ := by
  obtain ⟨c, C, hc, hb⟩ := h
  refine ⟨c / (|σ| + 1), C, by positivity, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hb T hT
  obtain ⟨n1, n2⟩ := norm_sT σ T hT
  rw [gamma_succ σ T hT, rpow_succ σ T hT] at h1 h2
  have hT0 : 0 < T := by linarith
  have hp : 0 ≤ T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2)) := by positivity
  have hg : 0 ≤ ‖Complex.Gamma ((σ : ℂ) + T * I)‖ := norm_nonneg _
  set G := ‖Complex.Gamma ((σ : ℂ) + T * I)‖
  set P := T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2))
  set N := ‖(σ : ℂ) + T * I‖
  have ha : 0 < |σ| + 1 := by positivity
  constructor
  · -- c T P ≤ N G ≤ (|σ|+1) T G
    have : c * (T * P) ≤ ((|σ| + 1) * T) * G := by
      calc c * (T * P) = c * (T * T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2))) := by
            simp only [P]; ring
        _ ≤ N * G := h1
        _ ≤ ((|σ| + 1) * T) * G := mul_le_mul_of_nonneg_right n2 hg
    rw [div_mul_eq_mul_div, div_le_iff₀ ha]
    have h3 : T * (c * P) ≤ T * (G * (|σ| + 1)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hT0
  · have : T * G ≤ C * (T * P) := by
      calc T * G ≤ N * G := mul_le_mul_of_nonneg_right n1 hg
        _ ≤ C * (T * T ^ (σ - 1 / 2) * Real.exp (-(Real.pi * T / 2))) := h2
        _ = C * (T * P) := by simp only [P]; ring
    have h3 : T * G ≤ T * (C * P) := by nlinarith
    exact le_of_mul_le_mul_left h3 hT0

theorem Pb_all (σ : ℝ) : Pb σ := by
  set k : ℤ := ⌊σ - 1 / 2⌋ with hk
  set σ0 := σ - k with hσ0
  have h1 : 1 / 2 ≤ σ0 := by
    have := Int.floor_le (σ - 1 / 2); rw [hσ0]; linarith
  have h2 : σ0 ≤ 3 / 2 := by
    have := Int.lt_floor_add_one (σ - 1 / 2); rw [hσ0]; linarith
  have hb := Pb_base σ0 h1 h2
  have key : ∀ m : ℤ, Pb (σ0 + m) := by
    intro m
    induction m using Int.induction_on with
    | zero => simpa using hb
    | succ i ih =>
      have e : σ0 + (((i : ℤ) + 1 : ℤ) : ℝ) = (σ0 + ((i : ℤ) : ℝ)) + 1 := by push_cast; ring
      rw [e]; exact Pb_up _ ih
    | pred i ih =>
      apply Pb_down
      have e : σ0 + ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = σ0 + ((-(i : ℤ) : ℤ) : ℝ) := by push_cast; ring
      rw [e]; exact ih
  convert key k using 1
  rw [hσ0]; ring

end LHGV


open Complex Filter Asymptotics Topology Set ComplexConjugate

namespace LHFEG

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

lemma cos_bounds (a b : ℝ) (hb : 1 ≤ b) :
    Real.exp b / 4 ≤ ‖Complex.cos ((a : ℂ) - b * I)‖ ∧
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
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (Real.cos a)]
  · rw [Real.sqrt_le_left (by positivity)]
    have := Real.cos_sq_le_one a
    nlinarith

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

lemma zeta_rel_bounds (σ : ℝ) : ∃ k K : ℝ, 0 < k ∧ 0 ≤ K ∧ ∀ T : ℝ, 1 ≤ T →
    k * T ^ (σ - 1 / 2) * ‖riemannZeta ((σ : ℂ) + T * I)‖ ≤
      ‖riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)‖ ∧
    ‖riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)‖ ≤
      K * T ^ (σ - 1 / 2) * ‖riemannZeta ((σ : ℂ) + T * I)‖ := by
  obtain ⟨c, C, hc, hb⟩ := LHGV.Pb_all σ
  have hq : 0 < (2 * Real.pi) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  have hC0 : 0 ≤ C := by
    obtain ⟨g1, g2⟩ := hb 1 le_rfl
    have := g1.trans g2
    have hpos : 0 < (1 : ℝ) ^ (σ - 1 / 2) * Real.exp (-(Real.pi * 1 / 2)) := by positivity
    nlinarith
  refine ⟨c * (2 * Real.pi) ^ (-σ) / 2, 2 * C * (2 * Real.pi) ^ (-σ), by positivity,
    by positivity, fun T hT => ?_⟩
  obtain ⟨g1, g2⟩ := hb T hT
  have hT0 : 0 < T := by linarith
  have hb1 : 1 ≤ Real.pi * T / 2 := by nlinarith [Real.pi_gt_three]
  obtain ⟨c1, c2⟩ := cos_bounds (Real.pi * σ / 2) (Real.pi * T / 2) hb1
  rw [zeta_rel σ T hT]
  set G := ‖Complex.Gamma ((σ : ℂ) + T * I)‖
  set Co := ‖Complex.cos ((((Real.pi * σ / 2 : ℝ)) : ℂ) - ((Real.pi * T / 2 : ℝ) : ℂ) * I)‖
  set Z := ‖riemannZeta ((σ : ℂ) + T * I)‖
  set P := T ^ (σ - 1 / 2)
  set ex := Real.exp (Real.pi * T / 2)
  have hP : 0 < P := Real.rpow_pos_of_pos hT0 _
  have hex : 0 < ex := Real.exp_pos _
  have hmul : Real.exp (-(Real.pi * T / 2)) * ex = 1 := by
    rw [← Real.exp_add]; simp
  have hZ : 0 ≤ Z := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  -- G * Co bounds
  have lo : c * P / 4 ≤ G * Co := by
    have := mul_le_mul g1 c1 (by positivity) hG
    calc c * P / 4 = c * (P * Real.exp (-(Real.pi * T / 2))) * (ex / 4) := by
          rw [show c * (P * Real.exp (-(Real.pi * T / 2))) * (ex / 4) =
            c * P / 4 * (Real.exp (-(Real.pi * T / 2)) * ex) by ring, hmul, mul_one]
      _ ≤ G * Co := this
  have hi : G * Co ≤ C * P := by
    have hC : 0 ≤ C := by
      have := g1.trans g2
      have hpos : 0 < P * Real.exp (-(Real.pi * T / 2)) := by positivity
      nlinarith
    have := mul_le_mul g2 c2 (norm_nonneg _) (by positivity)
    calc G * Co ≤ C * (P * Real.exp (-(Real.pi * T / 2))) * ex := this
      _ = C * P * (Real.exp (-(Real.pi * T / 2)) * ex) := by ring
      _ = C * P := by rw [hmul, mul_one]
  constructor
  · calc c * (2 * Real.pi) ^ (-σ) / 2 * P * Z = 2 * (2 * Real.pi) ^ (-σ) * (c * P / 4) * Z := by
          ring
      _ ≤ 2 * (2 * Real.pi) ^ (-σ) * (G * Co) * Z := by gcongr
      _ = _ := by ring
  · calc 2 * (2 * Real.pi) ^ (-σ) * G * Co * Z = 2 * (2 * Real.pi) ^ (-σ) * (G * Co) * Z := by
          ring
      _ ≤ 2 * (2 * Real.pi) ^ (-σ) * (C * P) * Z := by gcongr
      _ = _ := by ring

end LHFEG

open LindelofHypothesis in
theorem solution (σ : ℝ) : mu σ = mu (1 - σ) + ((1 / 2 - σ : ℝ) : EReal) := by
  obtain ⟨k, K, hk, hK, hrel⟩ := LHFEG.zeta_rel_bounds σ
  obtain ⟨f, -, hmu⟩ := LindelofHypothesis.mu_convex
  -- (i) a ∈ S_σ → a + σ - 1/2 ∈ S_{1-σ}
  have hi : ∀ a : ℝ, (fun T : ℝ => riemannZeta ((σ : ℂ) + T * I)) =O[atTop] (fun T : ℝ => T ^ a) →
      (fun T : ℝ => riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ (a + (σ - 1 / 2))) := by
    intro a ha
    obtain ⟨B, hB⟩ := ha.bound
    refine IsBigO.of_bound (K * B) ?_
    filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with T h1 hT
    have hT0 : 0 < T := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0.le _)] at h1 ⊢
    have h2 := (hrel T hT).2
    rw [Real.rpow_add hT0]
    calc ‖riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)‖
        ≤ K * T ^ (σ - 1 / 2) * ‖riemannZeta ((σ : ℂ) + T * I)‖ := h2
      _ ≤ K * T ^ (σ - 1 / 2) * (B * T ^ a) := by
          apply mul_le_mul_of_nonneg_left h1
          exact mul_nonneg hK (Real.rpow_nonneg hT0.le _)
      _ = K * B * (T ^ a * T ^ (σ - 1 / 2)) := by ring
  -- (ii) b ∈ S_{1-σ} → b - (σ - 1/2) ∈ S_σ
  have hii : ∀ b : ℝ, (fun T : ℝ => riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)) =O[atTop]
      (fun T : ℝ => T ^ b) →
      (fun T : ℝ => riemannZeta ((σ : ℂ) + T * I)) =O[atTop]
        (fun T : ℝ => T ^ (b - (σ - 1 / 2))) := by
    intro b hb
    obtain ⟨B, hB⟩ := hb.bound
    refine IsBigO.of_bound (B / k) ?_
    filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with T h1 hT
    have hT0 : 0 < T := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0.le _)] at h1 ⊢
    have h2 := (hrel T hT).1
    have hP : 0 < T ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hT0 _
    have e : T ^ b = T ^ (σ - 1 / 2) * T ^ (b - (σ - 1 / 2)) := by
      rw [← Real.rpow_add hT0]; congr 1; ring
    rw [e] at h1
    have h3 : k * T ^ (σ - 1 / 2) * ‖riemannZeta ((σ : ℂ) + T * I)‖ ≤
        k * T ^ (σ - 1 / 2) * (B / k * T ^ (b - (σ - 1 / 2))) := by
      calc _ ≤ _ := h2.trans h1
        _ = k * T ^ (σ - 1 / 2) * (B / k * T ^ (b - (σ - 1 / 2))) := by
            field_simp
    exact le_of_mul_le_mul_left h3 (by positivity)
  -- conclude
  have A : ∀ a ∈ {a : ℝ | (fun T : ℝ => riemannZeta ((σ : ℂ) + T * I)) =O[atTop]
      (fun T : ℝ => T ^ a)}, f (1 - σ) - (σ - 1 / 2) ≤ a := by
    intro a ha
    have : mu (1 - σ) ≤ ((a + (σ - 1 / 2) : ℝ) : EReal) := by
      unfold mu; exact sInf_le ⟨_, hi a ha, rfl⟩
    rw [hmu] at this
    have : f (1 - σ) ≤ a + (σ - 1 / 2) := by exact_mod_cast this
    linarith
  have B : ∀ b ∈ {b : ℝ | (fun T : ℝ => riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)) =O[atTop]
      (fun T : ℝ => T ^ b)}, f σ + (σ - 1 / 2) ≤ b := by
    intro b hb
    have : mu σ ≤ ((b - (σ - 1 / 2) : ℝ) : EReal) := by
      unfold mu; exact sInf_le ⟨_, hii b hb, rfl⟩
    rw [hmu] at this
    have : f σ ≤ b - (σ - 1 / 2) := by exact_mod_cast this
    linarith
  have C1 : ((f (1 - σ) - (σ - 1 / 2) : ℝ) : EReal) ≤ mu σ := by
    unfold mu
    apply le_sInf
    rintro _ ⟨a, ha, rfl⟩
    show ((_ : ℝ) : EReal) ≤ ((a : ℝ) : EReal)
    exact_mod_cast A a ha
  have C2 : ((f σ + (σ - 1 / 2) : ℝ) : EReal) ≤ mu (1 - σ) := by
    unfold mu
    apply le_sInf
    rintro _ ⟨b, hb, rfl⟩
    show ((_ : ℝ) : EReal) ≤ ((b : ℝ) : EReal)
    exact_mod_cast B b hb
  rw [hmu] at C1 C2
  have D1 : f (1 - σ) - (σ - 1 / 2) ≤ f σ := by exact_mod_cast C1
  have D2 : f σ + (σ - 1 / 2) ≤ f (1 - σ) := by exact_mod_cast C2
  rw [hmu, hmu, ← EReal.coe_add]
  congr 1
  linarith

