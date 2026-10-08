-- Prove2me | solution 1 for LogSobolevMC.ChiSquare.theorem_3_5_iii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:06:22.256981+00:00
-- url     : https://prove2.me/submissions/adebac47-1654-4126-b79e-6c4c3601b553

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

lemma heatOp_pos (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) (x : V) : 0 < heatOp K t f x := by
  have : Nonempty V := ⟨x⟩
  obtain ⟨x0, _, hx0⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hm : 0 < f x0 := hf x0
  have h1 : 0 ≤ heatOp K t (fun y => f y - f x0) x :=
    heatOp_nonneg K hK t ht _ (fun y => by linarith [hx0 y (Finset.mem_univ y)]) x
  have h2 : heatOp K t (fun y => f y - f x0) x = heatOp K t f x - f x0 := by
    have hc := congrFun (heatOp_const K hK (f x0) t) x
    unfold heatOp at hc ⊢
    rw [show (fun y => f y - f x0) = f - (fun _ => f x0) from rfl, Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    rw [hc]
  linarith

theorem eq_3_2_core (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 < f x)
    (p : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hp : 1 ≤ p t)
    (p' : ℝ) (hp' : HasDerivAt p p' t) :
    let F := fun s : ℝ => lpNorm π (p s) (heatOp K s f)
    HasDerivAt F
      (F t ^ (-(p t) + 1) *
        (p' / (p t) ^ 2 * entLp π (p t) (heatOp K t f) -
          dirichlet K π (heatOp K t f)
            (fun x => heatOp K t f x ^ (p t - 1)))) t := by
  intro F
  have hpne : p t ≠ 0 := ne_of_gt (by linarith)
  rcases isEmpty_or_nonempty V with hV | hV
  · have hev : ∀ᶠ s in nhds t, p s ≠ 0 := hp'.continuousAt.eventually_ne hpne
    have hFeq : F =ᶠ[nhds t] fun _ => (0:ℝ) := by
      filter_upwards [hev] with s hs
      show lpNorm π (p s) (heatOp K s f) = 0
      unfold lpNorm
      rw [Finset.univ_eq_empty, Finset.sum_empty, Real.zero_rpow (one_div_ne_zero hs)]
    refine ((hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hFeq).congr_deriv ?_
    simp [entLp, dirichlet]
  set g := heatOp K t f with hg
  have hpos : ∀ x, 0 < g x := fun x => heatOp_pos K hK t ht f hf x
  have hev : ∀ᶠ s in nhds t, ∀ x, 0 < heatOp K s f x := by
    rw [Filter.eventually_all]
    intro x
    exact (hasDerivAt_heatOp' K f t x).continuousAt.tendsto.eventually
      (eventually_gt_nhds (hpos x))
  set G : ℝ → ℝ := fun s => ∑ x, heatOp K s f x ^ p s * π x with hGdef
  have hG : HasDerivAt G (∑ x, (((K - 1).mulVec g) x * p t * g x ^ (p t - 1)
      + p' * g x ^ p t * Real.log (g x)) * π x) t := by
    apply HasDerivAt.fun_sum; intro x _
    exact ((hasDerivAt_heatOp' K f t x).rpow hp' (hpos x)).mul_const (π x)
  set Gt := ∑ x, g x ^ p t * π x with hGt
  have hGtG : G t = Gt := rfl
  have hGpos : 0 < Gt :=
    Finset.sum_pos (fun x _ => mul_pos (Real.rpow_pos_of_pos (hpos x) _) (hπpos x))
      Finset.univ_nonempty
  have hinv : HasDerivAt (fun s => 1 / p s) (-p' / (p t) ^ 2) t := by
    simp only [one_div]; exact hp'.inv hpne
  have hFt := hG.rpow hinv (by rw [hGtG]; exact hGpos)
  have hFeq : F =ᶠ[nhds t] fun s => G s ^ (1 / p s) := by
    filter_upwards [hev] with s hs
    show lpNorm π (p s) (heatOp K s f) = (∑ x, heatOp K s f x ^ p s * π x) ^ (1 / p s)
    unfold lpNorm
    congr 1
    apply Finset.sum_congr rfl; intro x _
    rw [abs_of_pos (hs x)]
  refine (hFt.congr_of_eventuallyEq hFeq).congr_deriv ?_
  rw [hGtG]
  have hFtv : F t = Gt ^ (1 / p t) := hFeq.eq_of_nhds
  set L := ∑ x, g x ^ p t * Real.log (g x) * π x with hL
  set E := dirichlet K π g (fun x => g x ^ (p t - 1)) with hE
  have hG'eq : (∑ x, (((K - 1).mulVec g) x * p t * g x ^ (p t - 1)
      + p' * g x ^ p t * Real.log (g x)) * π x) = -(p t) * E + p' * L := by
    rw [hE, hL]
    unfold dirichlet
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [KsubOne_mulVec]; ring
  have hGabs : ∑ x, |g x| ^ p t * π x = Gt := by
    rw [hGt]; apply Finset.sum_congr rfl; intro x _; rw [abs_of_pos (hpos x)]
  have hnorm : lpNorm π (p t) g ^ p t = Gt := by
    unfold lpNorm
    rw [hGabs, ← Real.rpow_mul hGpos.le, one_div, inv_mul_cancel₀ hpne, Real.rpow_one]
  have hent : entLp π (p t) g = p t * L - Gt * Real.log Gt := by
    unfold entLp
    rw [hnorm]
    have e : ∀ x, |g x| ^ p t * Real.log (|g x| ^ p t / Gt) * π x
        = p t * (g x ^ p t * Real.log (g x) * π x) - Real.log Gt * (g x ^ p t * π x) := by
      intro x
      rw [abs_of_pos (hpos x), Real.log_div (Real.rpow_pos_of_pos (hpos x) _).ne' hGpos.ne',
        Real.log_rpow (hpos x)]
      ring
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hL, ← hGt]
    ring
  rw [hG'eq, hFtv, hent]
  have e1 : (Gt ^ (1 / p t)) ^ (-(p t) + 1) = Gt ^ (1 / p t - 1) := by
    rw [← Real.rpow_mul hGpos.le]; congr 1; field_simp; ring
  have e2 : Gt ^ (1 / p t) = Gt ^ (1 / p t - 1) * Gt := by
    rw [Real.rpow_sub_one hGpos.ne']; field_simp
  rw [e1, e2]
  field_simp
  ring

lemma lpNorm_nonneg (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (q : ℝ) (u : V → ℝ) :
    0 ≤ lpNorm π q u := by
  unfold lpNorm
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x)

lemma lpNorm_two_sq (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    lpNorm π 2 f ^ (2:ℝ) = ∑ x, |f x| ^ (2:ℝ) * π x := by
  unfold lpNorm
  have hs : 0 ≤ ∑ x, |f x| ^ (2:ℝ) * π x := by
    apply Finset.sum_nonneg; intro x _; have := hπ x; positivity
  rw [← Real.rpow_mul hs]; norm_num

lemma entL_nonneg (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ entL π f := by
  unfold entL
  rw [lpNorm_two_sq π hπ.1]
  set N := ∑ x, |f x| ^ (2:ℝ) * π x with hN
  have hN0 : 0 ≤ N := by
    apply Finset.sum_nonneg; intro x _; have := hπ.1 x; positivity
  have key : ∀ x, (|f x| ^ (2:ℝ) - N) * π x ≤ |f x| ^ (2:ℝ) * Real.log (|f x| ^ (2:ℝ) / N) * π x := by
    intro x
    apply mul_le_mul_of_nonneg_right _ (hπ.1 x)
    rcases (eq_or_lt_of_le (by positivity : (0:ℝ) ≤ |f x| ^ (2:ℝ))) with h | h
    · rw [← h]; simp; exact hN0
    · rcases (eq_or_lt_of_le hN0) with h2 | h2
      · exfalso
        have : |f x| ^ (2:ℝ) * π x ≤ N := by
          rw [hN]
          exact Finset.single_le_sum (f := fun x => |f x| ^ (2:ℝ) * π x)
            (fun y _ => by have := hπ.1 y; positivity) (Finset.mem_univ x)
        have hpx := hπpos x
        have : 0 < |f x| ^ (2:ℝ) * π x := mul_pos h hpx
        linarith
      · have hl := Real.one_sub_inv_le_log_of_pos (div_pos h h2)
        rw [inv_div] at hl
        have : |f x| ^ (2:ℝ) * (1 - N / |f x| ^ (2:ℝ)) = |f x| ^ (2:ℝ) - N := by
          field_simp
        calc |f x| ^ (2:ℝ) - N = |f x| ^ (2:ℝ) * (1 - N / |f x| ^ (2:ℝ)) := this.symm
          _ ≤ |f x| ^ (2:ℝ) * Real.log (|f x| ^ (2:ℝ) / N) :=
            mul_le_mul_of_nonneg_left hl h.le
  calc (0:ℝ) = ∑ x, (|f x| ^ (2:ℝ) - N) * π x := by
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2, mul_one]; ring
    _ ≤ _ := Finset.sum_le_sum (fun x _ => key x)

lemma ls_le (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (h : V → ℝ) :
    logSobolev K π * entL π h ≤ dirichlet K π h h := by
  have hE := dirichlet_nonneg K hK π hπ h
  have hL := entL_nonneg π hπ.1 hπpos h
  rcases eq_or_lt_of_le hL with h0 | h0
  · rw [← h0, mul_zero]; exact hE
  · have hbdd : BddBelow {r : ℝ | ∃ f : V → ℝ, entL π f ≠ 0 ∧ r = dirichlet K π f f / entL π f} := by
      refine ⟨0, ?_⟩
      rintro r ⟨f, _, rfl⟩
      exact div_nonneg (dirichlet_nonneg K hK π hπ f) (entL_nonneg π hπ.1 hπpos f)
    have hmem : dirichlet K π h h / entL π h ∈
        {r : ℝ | ∃ f : V → ℝ, entL π f ≠ 0 ∧ r = dirichlet K π f f / entL π f} :=
      ⟨h, h0.ne', rfl⟩
    have := csInf_le hbdd hmem
    unfold logSobolev
    rw [le_div_iff₀ h0] at this
    exact this

lemma logSobolev_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ)
    (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) : 0 ≤ logSobolev K π := by
  unfold logSobolev
  apply Real.sInf_nonneg
  rintro r ⟨f, _, rfl⟩
  exact div_nonneg (dirichlet_nonneg K hK π hπ f) (entL_nonneg π hπ.1 hπpos f)

lemma sum_rpow_pi (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (p : ℝ) (hp : 0 < p) (g : V → ℝ)
    (hg : ∀ x, 0 < g x) : lpNorm π p g ^ p = ∑ x, g x ^ p * π x := by
  unfold lpNorm
  have hs : ∑ x, |g x| ^ p * π x = ∑ x, g x ^ p * π x := by
    apply Finset.sum_congr rfl; intro x _; rw [abs_of_pos (hg x)]
  have hS : 0 ≤ ∑ x, g x ^ p * π x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (hg x).le _) (hπ x)
  rw [hs, ← Real.rpow_mul hS, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

lemma entLp_eq_entL (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (p : ℝ) (hp : 0 < p) (g : V → ℝ)
    (hg : ∀ x, 0 < g x) : entLp π p g = entL π (fun x => g x ^ (p / 2)) := by
  unfold entLp entL
  rw [lpNorm_two_sq π hπ, sum_rpow_pi π hπ p hp g hg]
  have e : ∀ x, |g x ^ (p / 2)| ^ (2:ℝ) = g x ^ p := by
    intro x
    rw [abs_of_pos (Real.rpow_pos_of_pos (hg x) _), ← Real.rpow_mul (hg x).le]
    congr 1; ring
  have e2 : ∑ x, |g x ^ (p / 2)| ^ (2:ℝ) * π x = ∑ x, g x ^ p * π x := by
    apply Finset.sum_congr rfl; intro x _; rw [e]
  rw [e2]
  apply Finset.sum_congr rfl; intro x _
  rw [e, abs_of_pos (hg x)]

lemma lpNorm_mono_exp (π : V → ℝ) (hπ : IsDist π) (q r : ℝ) (hq : 0 < q) (hqr : q ≤ r)
    (u : V → ℝ) : lpNorm π q u ≤ lpNorm π r u := by
  have hr : 0 < r := lt_of_lt_of_le hq hqr
  have hq' : q ≠ 0 := hq.ne'
  have hr' : r ≠ 0 := hr.ne'
  unfold lpNorm
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ π (fun x => |u x| ^ q)
    (fun x _ => hπ.1 x) hπ.2 (fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
    (show 1 ≤ r / q by rw [le_div_iff₀ hq]; linarith)
  have e1 : ∑ x, π x * |u x| ^ q = ∑ x, |u x| ^ q * π x := by
    apply Finset.sum_congr rfl; intro x _; ring
  have e2 : ∑ x, π x * (|u x| ^ q) ^ (r / q) = ∑ x, |u x| ^ r * π x := by
    apply Finset.sum_congr rfl; intro x _
    rw [← Real.rpow_mul (abs_nonneg _), show q * (r / q) = r by field_simp]; ring
  rw [e1, e2] at h
  have hS : 0 ≤ ∑ x, |u x| ^ q * π x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ.1 x)
  have := Real.rpow_le_rpow (Real.rpow_nonneg hS _) h (by positivity : 0 ≤ 1 / r)
  rw [← Real.rpow_mul hS, show r / q * (1 / r) = 1 / q by field_simp] at this
  exact this

lemma lpNorm_mono_abs (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (q : ℝ) (hq : 0 < q) (u v : V → ℝ)
    (h : ∀ x, |u x| ≤ |v x|) : lpNorm π q u ≤ lpNorm π q v := by
  unfold lpNorm
  apply Real.rpow_le_rpow
    (Finset.sum_nonneg fun x _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπ x)) _
    (by positivity)
  apply Finset.sum_le_sum; intro x _
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (h x) hq.le) (hπ x)

lemma abs_heatOp_le (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t)
    (f : V → ℝ) (x : V) : |heatOp K t f x| ≤ heatOp K t (fun y => |f y|) x := by
  unfold heatOp; rw [mulVec_apply', mulVec_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum; intro y _
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg K hK t ht x y)]

lemma F_antitone (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (c : ℝ) (hc : 0 ≤ c)
    (Hc : ∀ p : ℝ, 2 ≤ p → ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * (p - 1) / p ^ 2 * logSobolev K π * entLp π p g ≤
        dirichlet K π g (fun x => g x ^ (p - 1)))
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    AntitoneOn (fun s => lpNorm π (1 + Real.exp (c * logSobolev K π * s)) (heatOp K s f))
      (Set.Ici 0) := by
  set α := logSobolev K π with hα
  have hα0 : 0 ≤ α := logSobolev_nonneg K hK π hπ hπpos
  set p : ℝ → ℝ := fun s => 1 + Real.exp (c * α * s) with hpdef
  have hpd : ∀ s, HasDerivAt p (c * α * Real.exp (c * α * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s => c * α * s) (c * α) s := by
      simpa using (hasDerivAt_id s).const_mul (c * α)
    have := (h1.exp).const_add 1
    refine this.congr_deriv ?_
    ring
  have hp2 : ∀ s, 0 ≤ s → 2 ≤ p s := by
    intro s hs
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hc hα0) hs)
    show 2 ≤ 1 + Real.exp (c * α * s)
    linarith
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s => lpNorm π (p s) (heatOp K s f))
      (lpNorm π (p s) (heatOp K s f) ^ (-(p s) + 1) *
        (c * α * Real.exp (c * α * s) / (p s) ^ 2 * entLp π (p s) (heatOp K s f) -
          dirichlet K π (heatOp K s f) (fun x => heatOp K s f x ^ (p s - 1)))) s := by
    intro s hs
    exact eq_3_2_core K hK π hπ hπpos f hf p s hs (by linarith [hp2 s hs]) _ (hpd s)
  show AntitoneOn (fun s => lpNorm π (p s) (heatOp K s f)) (Set.Ici 0)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun s hs => (hd s (Set.mem_Ici.mp hs)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    exact fun s hs => (hd s (le_of_lt (Set.mem_Ioi.mp hs))).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs' : 0 ≤ s := le_of_lt (Set.mem_Ioi.mp hs)
    rw [(hd s hs').deriv]
    apply mul_nonpos_iff.mpr
    left
    refine ⟨Real.rpow_nonneg (lpNorm_nonneg π (fun x => (hπpos x).le) _ _) _, ?_⟩
    rw [sub_nonpos]
    have key := Hc (p s) (hp2 s hs') (heatOp K s f) (fun x => heatOp_pos K hK s hs' f hf x)
    have e : c * α * Real.exp (c * α * s) / (p s) ^ 2 * entLp π (p s) (heatOp K s f)
        = c * (p s - 1) / (p s) ^ 2 * α * entLp π (p s) (heatOp K s f) := by
      simp only [hpdef]; ring
    rw [e]
    exact key

theorem hyper_pos (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (c : ℝ) (hc : 0 ≤ c)
    (Hc : ∀ p : ℝ, 2 ≤ p → ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * (p - 1) / p ^ 2 * logSobolev K π * entLp π p g ≤
        dirichlet K π g (fun x => g x ^ (p - 1)))
    (t : ℝ) (ht : 0 ≤ t) (q : ℝ) (hq : 2 ≤ q) (hqt : q - 1 ≤ Real.exp (c * logSobolev K π * t))
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by
  have hanti := F_antitone K hK π hπ hπpos c hc Hc f hf
  have h1 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, heatOp_zero] at h1
  have h2 := lpNorm_mono_exp π hπ.1 q (1 + Real.exp (c * logSobolev K π * t))
    (by linarith) (by linarith) (heatOp K t f)
  calc lpNorm π q (heatOp K t f) ≤ _ := h2
    _ ≤ lpNorm π (1 + 1) f := h1
    _ = lpNorm π 2 f := by norm_num

theorem hyper_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (c : ℝ) (hc : 0 ≤ c)
    (Hc : ∀ p : ℝ, 2 ≤ p → ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * (p - 1) / p ^ 2 * logSobolev K π * entLp π p g ≤
        dirichlet K π g (fun x => g x ^ (p - 1)))
    (t : ℝ) (ht : 0 ≤ t) (q : ℝ) (hq : 2 ≤ q) (hqt : q - 1 ≤ Real.exp (c * logSobolev K π * t))
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by
  have hq0 : 0 < q := by linarith
  have hε : ∀ ε : ℝ, 0 < ε → lpNorm π q (heatOp K t f) ≤ lpNorm π 2 (fun x => f x + ε) := by
    intro ε hε
    have h := hyper_pos K hK π hπ hπpos c hc Hc t ht q hq hqt (fun x => f x + ε)
      (fun x => by linarith [hf x])
    refine le_trans ?_ h
    apply lpNorm_mono_abs π (fun x => (hπpos x).le) q hq0
    intro x
    have e : heatOp K t (fun x => f x + ε) x = heatOp K t f x + ε := by
      have hc := congrFun (heatOp_const K hK ε t) x
      unfold heatOp at hc ⊢
      rw [show (fun x => f x + ε) = f + (fun _ => ε) from rfl, Matrix.mulVec_add]
      simp only [Pi.add_apply]; rw [hc]
    have h0 := heatOp_nonneg K hK t ht f hf x
    rw [e, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    linarith
  have hcont : Continuous (fun ε : ℝ => lpNorm π 2 (fun x => f x + ε)) := by
    unfold lpNorm
    apply Continuous.rpow_const
    · apply continuous_finsetSum; intro x _
      exact ((continuous_abs.comp (continuous_const.add continuous_id)).rpow_const
        (fun _ => Or.inr (by norm_num))).mul continuous_const
    · intro _; exact Or.inr (by norm_num)
  have hlim : Filter.Tendsto (fun ε : ℝ => lpNorm π 2 (fun x => f x + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (lpNorm π 2 f)) := by
    have := (hcont.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
    simpa using this
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (eventually_nhdsWithin_of_forall (fun ε hε' => hε ε hε'))

theorem hyper_all (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (c : ℝ) (hc : 0 ≤ c)
    (Hc : ∀ p : ℝ, 2 ≤ p → ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * (p - 1) / p ^ 2 * logSobolev K π * entLp π p g ≤
        dirichlet K π g (fun x => g x ^ (p - 1)))
    (t : ℝ) (ht : 0 ≤ t) (q : ℝ) (hq : 2 ≤ q) (hqt : q - 1 ≤ Real.exp (c * logSobolev K π * t))
    (f : V → ℝ) : lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by
  have h := hyper_nonneg K hK π hπ hπpos c hc Hc t ht q hq hqt (fun x => |f x|)
    (fun x => abs_nonneg _)
  have h1 : lpNorm π q (heatOp K t f) ≤ lpNorm π q (heatOp K t (fun x => |f x|)) := by
    apply lpNorm_mono_abs π (fun x => (hπpos x).le) q (by linarith)
    intro x
    rw [abs_of_nonneg (heatOp_nonneg K hK t ht _ (fun y => abs_nonneg _) x)]
    exact abs_heatOp_le K hK t ht f x
  have h2 : lpNorm π 2 (fun x => |f x|) = lpNorm π 2 f := by
    unfold lpNorm; simp only [abs_abs]
  linarith

theorem theorem_3_5_iii_core (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K) :
    ∀ t : ℝ, 0 < t → ∀ q : ℝ, 2 ≤ q →
      q - 1 ≤ Real.exp (2 * logSobolev K π * t) →
      ∀ f : V → ℝ, lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by
  intro t ht q hq hqt f
  apply hyper_all K hK π hπ hπpos 2 (by norm_num) _ t ht.le q hq hqt f
  intro p hp g hg
  have hp0 : 0 < p := by linarith
  have hα := logSobolev_nonneg K hK π hπ hπpos
  have h1 := lemma_2_6_i K hK π hπ g (fun x => (hg x).le) p hp
  have h2 := ls_le K hK π hπ hπpos (fun x => g x ^ (p / 2))
  rw [← entLp_eq_entL π (fun x => (hπpos x).le) p hp0 g hg] at h2
  have hL : 0 ≤ entLp π p g := by
    rw [entLp_eq_entL π (fun x => (hπpos x).le) p hp0 g hg]
    exact entL_nonneg π hπ.1 hπpos _
  have h3 : 2 * (p - 1) / p ^ 2 * logSobolev K π * entLp π p g ≤
      2 / p * (logSobolev K π * entLp π p g) := by
    have hc : 2 * (p - 1) / p ^ 2 ≤ 2 / p := by
      rw [div_le_div_iff₀ (by positivity) hp0]; nlinarith
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hα hL)
    linarith
  calc _ ≤ 2 / p * (logSobolev K π * entLp π p g) := h3
    _ ≤ 2 / p * dirichlet K π (fun x => g x ^ (p / 2)) (fun x => g x ^ (p / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1


end LogSobolevMC.ChiSquare

open LogSobolevMC.ChiSquare


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K) :
    ∀ t : ℝ, 0 < t → ∀ q : ℝ, 2 ≤ q →
      q - 1 ≤ Real.exp (2 * logSobolev K π * t) →
      ∀ f : V → ℝ, lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by
  exact theorem_3_5_iii_core K hK π hπ hπpos hirr
