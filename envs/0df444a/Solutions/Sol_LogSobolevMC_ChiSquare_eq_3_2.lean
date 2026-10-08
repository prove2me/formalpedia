-- Prove2me | solution 1 for LogSobolevMC.ChiSquare.eq_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:59:21.800684+00:00
-- url     : https://prove2.me/submissions/aa129552-2707-4397-8d11-b13c12db4f65

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


end LogSobolevMC.ChiSquare

open LogSobolevMC.ChiSquare


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 < f x)
    (p : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hp : 1 ≤ p t)
    (p' : ℝ) (hp' : HasDerivAt p p' t) :
    let F := fun s : ℝ => lpNorm π (p s) (heatOp K s f)
    HasDerivAt F
      (F t ^ (-(p t) + 1) *
        (p' / (p t) ^ 2 * entLp π (p t) (heatOp K t f) -
          dirichlet K π (heatOp K t f)
            (fun x => heatOp K t f x ^ (p t - 1)))) t := by
  exact eq_3_2_core K hK π hπ hπpos f hf p t ht hp p' hp'
