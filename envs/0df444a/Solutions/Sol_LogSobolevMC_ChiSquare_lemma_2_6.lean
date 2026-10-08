-- Prove2me | solution 1 for LogSobolevMC.ChiSquare.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:56:34.572705+00:00
-- url     : https://prove2.me/submissions/f638e9c7-b274-42a5-818c-5c0350ebe4b8

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

open MarkovMixing
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped BigOperators

namespace LogSobolevMC.ChiSquare

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- the entry map as a continuous linear map -/
noncomputable def entryCLM (x y : V) : Matrix V V ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ x y)

lemma entryCLM_apply (x y : V) (M : Matrix V V ℝ) : entryCLM x y M = M x y := rfl

lemma heatKernel_eq_exp (K : Matrix V V ℝ) (t : ℝ) :
    MarkovMixing.heatKernel K t = exp (t • (K - 1)) := by
  have hcomm : Commute (t • K) ((-t) • (1 : Matrix V V ℝ)) := by
    apply Commute.smul_left; apply Commute.smul_right; exact Commute.one_right _
  have e1 : t • (K - 1) = t • K + (-t) • (1 : Matrix V V ℝ) := by
    rw [smul_sub, neg_smul, sub_eq_add_neg]
  rw [e1, Matrix.exp_add_of_commute _ _ hcomm]
  have e2 : exp ((-t) • (1 : Matrix V V ℝ)) = Real.exp (-t) • (1 : Matrix V V ℝ) := by
    have h := algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix V V ℝ) (-t)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
    rw [Real.exp_eq_exp_ℝ]
    exact h.symm
  rw [e2]
  ext x y
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
  unfold MarkovMixing.heatKernel
  have hs : Summable (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (t • K) ^ n) := expSeries_summable' (t • K)
  rw [exp_eq_tsum (𝕂 := ℝ) (𝔸 := Matrix V V ℝ)]
  simp only
  have h3 : (∑' n : ℕ, (n.factorial⁻¹ : ℝ) • (t • K) ^ n) x y
      = ∑' n : ℕ, ((n.factorial⁻¹ : ℝ) • (t • K) ^ n) x y := (entryCLM x y).map_tsum hs
  rw [h3, ← tsum_mul_left]
  apply tsum_congr; intro k
  rw [smul_pow]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

lemma heatKernel_zero (K : Matrix V V ℝ) : MarkovMixing.heatKernel K 0 = 1 := by
  rw [heatKernel_eq_exp, zero_smul, exp_zero]

lemma hasDerivAt_heatKernel (K : Matrix V V ℝ) (t : ℝ) :
    HasDerivAt (fun s => MarkovMixing.heatKernel K s)
      (MarkovMixing.heatKernel K t * (K - 1)) t := by
  simp_rw [heatKernel_eq_exp]
  exact hasDerivAt_exp_smul_const (K - 1) t

lemma hasDerivAt_heatKernel_apply (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    HasDerivAt (fun s => MarkovMixing.heatKernel K s x y)
      ((MarkovMixing.heatKernel K t * (K - 1)) x y) t := by
  have := (entryCLM x y).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_heatKernel K t)
  exact this

lemma hasDerivAt_heatOp (K : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) (x : V) :
    HasDerivAt (fun s => heatOp K s f x)
      (((MarkovMixing.heatKernel K t * (K - 1)).mulVec f) x) t := by
  unfold heatOp
  simp only [Matrix.mulVec, dotProduct]
  apply HasDerivAt.fun_sum
  intro y _
  exact (hasDerivAt_heatKernel_apply K t x y).mul_const (f y)

lemma heatOp_zero (K : Matrix V V ℝ) (f : V → ℝ) : heatOp K 0 f = f := by
  unfold heatOp
  rw [heatKernel_zero, Matrix.one_mulVec]

lemma stationary_sum (K : Matrix V V ℝ) (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (f : V → ℝ) : ∑ x, (K.mulVec f) x * π x = ∑ x, f x * π x := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have := congrFun hπ.2 y
  simp only [Matrix.vecMul, dotProduct] at this
  rw [← this, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma heatKernel_comm (K : Matrix V V ℝ) (t : ℝ) :
    MarkovMixing.heatKernel K t * (K - 1) = (K - 1) * MarkovMixing.heatKernel K t := by
  rw [heatKernel_eq_exp]
  exact ((Commute.refl (K - 1)).smul_right t).exp_right.symm.eq

lemma hasDerivAt_heatOp' (K : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) (x : V) :
    HasDerivAt (fun s => heatOp K s f x)
      (((K - 1).mulVec (heatOp K t f)) x) t := by
  have h := hasDerivAt_heatOp K f t x
  rw [heatKernel_comm, ← Matrix.mulVec_mulVec] at h
  exact h

lemma KsubOne_mulVec (K : Matrix V V ℝ) (g : V → ℝ) (x : V) :
    ((K - 1).mulVec g) x = K.mulVec g x - g x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl

lemma mulVec_apply' (K : Matrix V V ℝ) (f : V → ℝ) (x : V) :
    K.mulVec f x = ∑ y, K x y * f y := by
  simp [Matrix.mulVec, dotProduct]

lemma mulVec_const (K : Matrix V V ℝ) (hK : IsStochastic K) (c : ℝ) (z : V) :
    K.mulVec (fun _ => c) z = c := by
  rw [mulVec_apply', ← Finset.sum_mul, hK.2 z, one_mul]

lemma pow_entry_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (k : ℕ) :
    ∀ x y, 0 ≤ (K ^ k) x y := by
  induction k with
  | zero => intro x y; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hK.1 z y)

lemma heatKernel_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t)
    (x y : V) : 0 ≤ MarkovMixing.heatKernel K t x y := by
  unfold MarkovMixing.heatKernel
  apply tsum_nonneg; intro k
  have h1 := pow_entry_nonneg K hK k x y
  have h2 := Real.exp_pos (-t)
  have h3 := pow_nonneg ht k
  positivity

lemma heatOp_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (x : V) : 0 ≤ heatOp K t f x := by
  unfold heatOp
  rw [mulVec_apply']
  exact Finset.sum_nonneg fun y _ => mul_nonneg (heatKernel_nonneg K hK t ht x y) (hf y)

lemma heatOp_const (K : Matrix V V ℝ) (hK : IsStochastic K) (c : ℝ) (t : ℝ) :
    heatOp K t (fun _ => c) = fun _ => c := by
  have hd : ∀ x, ∀ s, HasDerivAt (fun s => heatOp K s (fun _ => c) x) 0 s := by
    intro x s
    have h := hasDerivAt_heatOp K (fun _ => c) s x
    have h0 : (K - 1).mulVec (fun _ => c) = 0 := by
      ext z; rw [KsubOne_mulVec, mulVec_const K hK, sub_self]; rfl
    rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at h
    exact h
  ext x
  have := is_const_of_deriv_eq_zero (fun s => (hd x s).differentiableAt) (fun s => (hd x s).deriv) t 0
  rw [this, heatOp_zero]

lemma heatOp_sum_pi (K : Matrix V V ℝ) (π : V → ℝ) (hπ : IsStationary K π) (f : V → ℝ)
    (t : ℝ) : ∑ x, heatOp K t f x * π x = ∑ x, f x * π x := by
  have hd : ∀ s, HasDerivAt (fun s => ∑ x, heatOp K s f x * π x) 0 s := by
    intro s
    have h := HasDerivAt.fun_sum (u := Finset.univ)
      (fun x _ => (hasDerivAt_heatOp' K f s x).mul_const (π x))
    refine h.congr_deriv ?_
    have e : ∀ x, ((K - 1).mulVec (heatOp K s f)) x * π x
        = K.mulVec (heatOp K s f) x * π x - heatOp K s f x * π x := by
      intro x; rw [KsubOne_mulVec, sub_mul]
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, stationary_sum K π hπ, sub_self]
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  rw [this, heatOp_zero]

lemma dirichlet_eq_double (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (g h : V → ℝ) :
    dirichlet K π g h = ∑ x, ∑ y, π x * K x y * ((g x - g y) * h x) := by
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec, dotProduct]
  have : g x - ∑ y, K x y * g y = ∑ y, K x y * (g x - g y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hK.2 x, one_mul]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma double_sum_symm (w : V → V → ℝ) (hw : ∀ x y, w x y = w y x) (F : V → V → ℝ) :
    2 * (∑ x, ∑ y, w x y * F x y) = ∑ x, ∑ y, w x y * (F x y + F y x) := by
  have : ∑ x, ∑ y, w x y * F x y = ∑ x, ∑ y, w x y * F y x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [hw]
  rw [two_mul]
  nth_rewrite 2 [this]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _
  ring

lemma colsum_pi (K : Matrix V V ℝ) (π : V → ℝ) (hπ : IsStationary K π) (y : V) :
    ∑ x, π x * K x y = π y := by
  have h := congrFun hπ.2 y
  simpa [Matrix.vecMul, dotProduct] using h

/-- `2 ℰ(f,f) = Σ_x Σ_y π x K x y (f x - f y)^2`. -/
lemma two_dirichlet (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (f : V → ℝ) :
    2 * dirichlet K π f f = ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2 := by
  unfold dirichlet
  simp only [mulVec_apply']
  have e1 : ∀ x, ∑ y, π x * K x y * (f x - f y) ^ 2
      = π x * f x ^ 2 - 2 * (∑ y, K x y * f y) * f x * π x + ∑ y, π x * K x y * f y ^ 2 := by
    intro x
    have : ∑ y, π x * K x y * (f x - f y) ^ 2
        = ∑ y, (π x * f x ^ 2 * K x y - 2 * (K x y * f y) * f x * π x + π x * K x y * f y ^ 2) := by
      apply Finset.sum_congr rfl; intro y _; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hK.2 x,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have e2 : ∀ y, ∑ x, π x * K x y * f y ^ 2 = π y * f y ^ 2 := by
    intro y
    rw [← Finset.sum_mul, colsum_pi K π hπ]
  simp only [e2]
  have e3 : ∀ x, (f x - ∑ y, K x y * f y) * f x * π x
      = π x * f x ^ 2 - (∑ y, K x y * f y) * f x * π x := by intro x; ring
  simp only [e3, Finset.sum_sub_distrib]
  have e4 : ∑ x, (2 * ∑ y, K x y * f y) * f x * π x = 2 * ∑ x, (∑ y, K x y * f y) * f x * π x := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [e4]; ring

lemma dirichlet_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ)
    (hπ : IsStationary K π) (f : V → ℝ) :
    0 ≤ dirichlet K π f f := by
  have h := two_dirichlet K hK π hπ f
  have : 0 ≤ ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2 := by
    apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
    have := hπ.1.1 x; have := hK.1 x y; positivity
  linarith

lemma young_pt (p : ℝ) (hp : 2 ≤ p) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 / p * ((a ^ (p / 2) - b ^ (p / 2)) * a ^ (p / 2)) ≤ (a - b) * a ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hw1 : 0 ≤ 1 - 2 / p := by
    rw [sub_nonneg, div_le_one hp0]; linarith
  have key : b * a ^ (p - 1) ≤ (1 - 2 / p) * a ^ p + 2 / p * (a ^ (p / 2) * b ^ (p / 2)) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - 2 / p) (w₂ := 2 / p)
      (p₁ := a ^ p) (p₂ := a ^ (p / 2) * b ^ (p / 2)) hw1 (by positivity) (by positivity)
      (by positivity) (by ring)
    have e1 : (a ^ p) ^ (1 - 2 / p) = a ^ (p - 2) := by
      rw [← Real.rpow_mul ha]; congr 1; field_simp
    have e2 : (a ^ (p / 2) * b ^ (p / 2)) ^ (2 / p) = a * b := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha, ← Real.rpow_mul hb]
      have : p / 2 * (2 / p) = 1 := by field_simp
      rw [this, Real.rpow_one, Real.rpow_one]
    rw [e1, e2] at h
    have e3 : a ^ (p - 2) * (a * b) = b * a ^ (p - 1) := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add' ha (by intro h; linarith), Real.rpow_one]
      ring
    rw [e3] at h
    exact h
  have e4 : a ^ (p / 2) * a ^ (p / 2) = a ^ p := by
    rw [← Real.rpow_add' ha (by intro h; linarith)]; congr 1; ring
  have e5 : a * a ^ (p - 1) = a ^ p := by
    conv_rhs => rw [show p = 1 + (p - 1) by ring]
    rw [Real.rpow_add' ha (by intro h; linarith), Real.rpow_one]
  have g1 : 2 / p * ((a ^ (p / 2) - b ^ (p / 2)) * a ^ (p / 2))
      = 2 / p * a ^ p - 2 / p * (a ^ (p / 2) * b ^ (p / 2)) := by
    rw [← e4]; ring
  have g2 : (a - b) * a ^ (p - 1) = a ^ p - b * a ^ (p - 1) := by
    rw [← e5]; ring
  rw [g1, g2]
  linarith

theorem lemma_2_6_i (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 2 ≤ p) :
    2 / p * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1)) := by
  rw [dirichlet_eq_double K hK, dirichlet_eq_double K hK, Finset.mul_sum]
  apply Finset.sum_le_sum; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro y _
  have hw : 0 ≤ π x * K x y := mul_nonneg (hπ.1.1 x) (hK.1 x y)
  have := young_pt p hp (f x) (f y) (hf x) (hf y)
  calc 2 / p * (π x * K x y * ((f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2)))
      = π x * K x y * (2 / p * ((f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hw

lemma cs_rpow (p : ℝ) (hp : 1 < p) (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    4 * (p - 1) / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hr1 : (-1:ℝ) < p / 2 - 1 := by linarith
  have hr2 : (-1:ℝ) < p - 2 := by linarith
  set I1 := ∫ s in b..a, s ^ (p / 2 - 1) with hI1
  set I2 := ∫ s in b..a, s ^ (p - 2) with hI2
  have hI1v : I1 = (a ^ (p / 2) - b ^ (p / 2)) / (p / 2) := by
    rw [hI1, integral_rpow (Or.inl hr1)]
    rw [show p / 2 - 1 + 1 = p / 2 by ring]
  have hI2v : I2 = (a ^ (p - 1) - b ^ (p - 1)) / (p - 1) := by
    rw [hI2, integral_rpow (Or.inl hr2)]
    rw [show p - 2 + 1 = p - 1 by ring]
  have hg : IntervalIntegrable (fun s : ℝ => s ^ (p / 2 - 1)) MeasureTheory.volume b a :=
    intervalIntegral.intervalIntegrable_rpow' hr1
  have hg2 : IntervalIntegrable (fun s : ℝ => s ^ (p - 2)) MeasureTheory.volume b a :=
    intervalIntegral.intervalIntegrable_rpow' hr2
  have hnn : 0 ≤ ∫ s in b..a, ((a - b) * s ^ (p / 2 - 1) - I1) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le (fun s _ => sq_nonneg _)
  have hexp : ∫ s in b..a, ((a - b) * s ^ (p / 2 - 1) - I1) ^ 2
      = ∫ s in b..a, ((a - b) ^ 2 * s ^ (p - 2) - 2 * (a - b) * I1 * s ^ (p / 2 - 1) + I1 ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hab.le] at hs
    have hs0 : 0 ≤ s := le_trans hb hs.1
    simp only
    have : (s ^ (p / 2 - 1)) ^ 2 = s ^ (p - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]; congr 1; push_cast; ring
    rw [← this]; ring
  rw [hexp, intervalIntegral.integral_add ((hg2.const_mul _).sub (hg.const_mul _))
    intervalIntegrable_const,
    intervalIntegral.integral_sub (hg2.const_mul _) (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnn
  rw [← hI1, ← hI2] at hnn
  have hab' : 0 < a - b := by linarith
  have h2 : (a - b) * (I1 ^ 2) ≤ (a - b) * ((a - b) * I2) := by linarith
  have hcs : I1 ^ 2 ≤ (a - b) * I2 := le_of_mul_le_mul_left h2 hab'
  rw [hI1v, hI2v] at hcs
  have key : ((a ^ (p / 2) - b ^ (p / 2)) / (p / 2)) ^ 2
      = 4 / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2 := by
    field_simp
    ring
  rw [key] at hcs
  calc 4 * (p - 1) / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2
      = (p - 1) * (4 / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2) := by ring
    _ ≤ (p - 1) * ((a - b) * ((a ^ (p - 1) - b ^ (p - 1)) / (p - 1))) :=
        mul_le_mul_of_nonneg_left hcs hp1.le
    _ = (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by field_simp

lemma rev_pt (p : ℝ) (hp : 1 < p) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (p - 1) / p ^ 2 * (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by
  rcases lt_trichotomy b a with h | h | h
  · exact cs_rpow p hp a b hb h
  · subst h; simp
  · have := cs_rpow p hp b a ha h
    have e1 : (b ^ (p / 2) - a ^ (p / 2)) ^ 2 = (a ^ (p / 2) - b ^ (p / 2)) ^ 2 := by ring
    have e2 : (b - a) * (b ^ (p - 1) - a ^ (p - 1)) = (a - b) * (a ^ (p - 1) - b ^ (p - 1)) := by
      ring
    rw [e1, e2] at this; exact this

theorem lemma_2_6_ii (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hrev : DetailedBalance K π) (p : ℝ) (hp : 1 < p) :
    4 * (p - 1) / p ^ 2 *
          dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1)) := by
  have hw : ∀ x y, π x * K x y = π y * K y x := hrev
  have h1 : 2 * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2))
      = ∑ x, ∑ y, π x * K x y * ((f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2)
          + (f y ^ (p / 2) - f x ^ (p / 2)) * f y ^ (p / 2)) := by
    rw [dirichlet_eq_double K hK]
    exact double_sum_symm (fun x y => π x * K x y) hw
      (fun x y => (f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2))
  have h2 : 2 * dirichlet K π f (fun x => f x ^ (p - 1))
      = ∑ x, ∑ y, π x * K x y * ((f x - f y) * f x ^ (p - 1)
          + (f y - f x) * f y ^ (p - 1)) := by
    rw [dirichlet_eq_double K hK]
    exact double_sum_symm (fun x y => π x * K x y) hw
      (fun x y => (f x - f y) * f x ^ (p - 1))
  have h3 : 4 * (p - 1) / p ^ 2 * ∑ x, ∑ y, π x * K x y *
        ((f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2)
          + (f y ^ (p / 2) - f x ^ (p / 2)) * f y ^ (p / 2))
      ≤ ∑ x, ∑ y, π x * K x y * ((f x - f y) * f x ^ (p - 1)
          + (f y - f x) * f y ^ (p - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro y _
    have hw0 : 0 ≤ π x * K x y := mul_nonneg (hπ.1.1 x) (hK.1 x y)
    have := rev_pt p hp (f x) (f y) (hf x) (hf y)
    have e1 : (f x ^ (p / 2) - f y ^ (p / 2)) * f x ^ (p / 2)
        + (f y ^ (p / 2) - f x ^ (p / 2)) * f y ^ (p / 2)
        = (f x ^ (p / 2) - f y ^ (p / 2)) ^ 2 := by ring
    have e2 : (f x - f y) * f x ^ (p - 1) + (f y - f x) * f y ^ (p - 1)
        = (f x - f y) * (f x ^ (p - 1) - f y ^ (p - 1)) := by ring
    rw [e1, e2]
    calc 4 * (p - 1) / p ^ 2 * (π x * K x y * (f x ^ (p / 2) - f y ^ (p / 2)) ^ 2)
        = π x * K x y * (4 * (p - 1) / p ^ 2 * (f x ^ (p / 2) - f y ^ (p / 2)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hw0
  rw [← h1, ← h2] at h3
  linarith

theorem lemma_2_6_core (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∀ p : ℝ, 2 ≤ p →
      2 / p * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) ∧
    (DetailedBalance K π → ∀ p : ℝ, 1 < p →
      4 * (p - 1) / p ^ 2 *
          dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) :=
  ⟨fun p hp => lemma_2_6_i K hK π hπ f hf p hp,
   fun hrev p hp => lemma_2_6_ii K hK π hπ f hf hrev p hp⟩


end LogSobolevMC.ChiSquare

open LogSobolevMC.ChiSquare


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∀ p : ℝ, 2 ≤ p →
      2 / p * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) ∧
    (MarkovMixing.DetailedBalance K π → ∀ p : ℝ, 1 < p →
      4 * (p - 1) / p ^ 2 *
          dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) := by
  exact lemma_2_6_core K hK π hπ hπpos f hf
