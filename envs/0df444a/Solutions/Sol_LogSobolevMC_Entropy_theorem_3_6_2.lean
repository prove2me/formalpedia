-- Prove2me | solution 2 for LogSobolevMC.Entropy.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:34.100988+00:00
-- url     : https://prove2.me/submissions/9b34a541-8cd6-486c-9bda-30b05d33937e

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting
import Theorems.Thm_LogSobolevMC_Entropy_density_measHeat
import Theorems.Thm_LogSobolevMC_Entropy_entL_eq_relEnt
import Theorems.Thm_LogSobolevMC_Entropy_lemma_2_7

-- carved verbatim out of submission dae9eefd-bb54-46c5-8b3e-d223b02c4033, lines 772-782

section
open LogSobolevMC
open LogSobolevMC.Entropy
open scoped BigOperators
open scoped Matrix.Norms.Operator
open NormedSpace

lemma dirichlet_eq_double {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K) (π : V → ℝ) (g h : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π g h =
      ∑ x, ∑ y, π x * K x y * ((g x - g y) * h x) := by
  unfold LogSobolevMC.ChiSquare.dirichlet
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec, dotProduct]
  have : g x - ∑ y, K x y * g y = ∑ y, K x y * (g x - g y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hK.2 x, one_mul]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

end

section
open LogSobolevMC
open LogSobolevMC.Entropy
open scoped BigOperators
open scoped Matrix.Norms.Operator
open NormedSpace
variable {V : Type*} [Fintype V] [DecidableEq V]

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

lemma heatKernel_add (K : Matrix V V ℝ) (s t : ℝ) :
    MarkovMixing.heatKernel K (s + t) = MarkovMixing.heatKernel K s * MarkovMixing.heatKernel K t := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp, heatKernel_eq_exp, add_smul]
  apply Matrix.exp_add_of_commute
  exact (Commute.refl _).smul_left _ |>.smul_right _

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
    HasDerivAt (fun s => LogSobolevMC.ChiSquare.heatOp K s f x)
      (((MarkovMixing.heatKernel K t * (K - 1)).mulVec f) x) t := by
  unfold LogSobolevMC.ChiSquare.heatOp
  simp only [Matrix.mulVec, dotProduct]
  apply HasDerivAt.fun_sum
  intro y _
  exact (hasDerivAt_heatKernel_apply K t x y).mul_const (f y)

lemma heatOp_zero (K : Matrix V V ℝ) (f : V → ℝ) : LogSobolevMC.ChiSquare.heatOp K 0 f = f := by
  unfold LogSobolevMC.ChiSquare.heatOp
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

theorem lemma_2_5_ent_core (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    HasDerivAt (fun t : ℝ => entF π (LogSobolevMC.ChiSquare.heatOp K t f))
      (-LogSobolevMC.ChiSquare.dirichlet K π f (fun x => Real.log (f x))) 0 := by
  unfold entF
  have hx : ∀ x, HasDerivAt
      (fun t => LogSobolevMC.ChiSquare.heatOp K t f x * Real.log (LogSobolevMC.ChiSquare.heatOp K t f x) * π x)
      ((Real.log (f x) + 1) * (K.mulVec f x - f x) * π x) 0 := by
    intro x
    have h1 := hasDerivAt_heatOp K f 0 x
    rw [heatKernel_zero, one_mul] at h1
    have h0 : LogSobolevMC.ChiSquare.heatOp K 0 f x = f x := by rw [heatOp_zero]
    have h2 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log (f x) + 1)
        (LogSobolevMC.ChiSquare.heatOp K 0 f x) := by
      rw [h0]; exact Real.hasDerivAt_mul_log (hf x).ne'
    have h3 := (h2.comp 0 h1).mul_const (π x)
    refine h3.congr_deriv ?_
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hx x)
  refine hsum.congr_deriv ?_
  have hs := stationary_sum K π hπ f
  have h0 : ∑ x, (K.mulVec f x - f x) * π x = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, hs, sub_self]
  have e : ∑ x, (Real.log (f x) + 1) * (K.mulVec f x - f x) * π x
      = ∑ x, -((f x - K.mulVec f x) * Real.log (f x) * π x) + ∑ x, (K.mulVec f x - f x) * π x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [e, h0, add_zero, Finset.sum_neg_distrib]
  rfl

open MarkovMixing LogSobolevMC.ChiSquare in
lemma isStochastic_pow (K : Matrix V V ℝ) (hK : IsStochastic K) (k : ℕ) : IsStochastic (K ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ]
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Matrix.mul_apply]
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih.1 x z) (hK.1 z y))
    · simp_rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hK.2, mul_one]
      exact ih.2 x

lemma heat_summable (K : Matrix V V ℝ) (t : ℝ) (x y : V) :
    Summable (fun k : ℕ => Real.exp (-t) * t ^ k / k.factorial * (K ^ k) x y) := by
  have hs := (entryCLM x y).summable (expSeries_summable' (𝕂 := ℝ) (t • K))
  have e : (fun k : ℕ => Real.exp (-t) * t ^ k / k.factorial * (K ^ k) x y)
      = fun k => Real.exp (-t) * (entryCLM x y ((k.factorial⁻¹ : ℝ) • (t • K) ^ k)) := by
    funext k
    rw [entryCLM_apply, smul_pow]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact hs.mul_left _

lemma tsum_poisson (t : ℝ) : ∑' k : ℕ, Real.exp (-t) * t ^ k / k.factorial = 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) t
  have h2 := h.mul_left (Real.exp (-t))
  simp_rw [mul_div_assoc]
  rw [h2.tsum_eq, ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  simp

open MarkovMixing in
lemma heatKernel_isStochastic (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t) :
    IsStochastic (heatKernel K t) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold heatKernel
    apply tsum_nonneg
    intro k
    have := (isStochastic_pow K hK k).1 x y
    positivity
  · unfold heatKernel
    rw [← Summable.tsum_finsetSum (fun y _ => heat_summable K t x y)]
    simp_rw [← Finset.mul_sum, (isStochastic_pow K hK _).2 x, mul_one]
    exact tsum_poisson t

open MarkovMixing LogSobolevMC.ChiSquare in
lemma heatOp_pos (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) (x : V) : 0 < heatOp K t f x := by
  have hH := heatKernel_isStochastic K hK t ht
  unfold heatOp
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos' (fun y _ => mul_nonneg (hH.1 x y) (hf y).le)
  by_contra hcon
  push Not at hcon
  have hz : ∀ y, heatKernel K t x y = 0 := by
    intro y
    have h1 := hcon y (Finset.mem_univ y)
    have h2 := hH.1 x y
    by_contra hne
    have := mul_pos (lt_of_le_of_ne h2 (Ne.symm hne)) (hf y)
    linarith
  have := hH.2 x
  simp [hz] at this

open MarkovMixing in
lemma timeReversal_isStochastic (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) :
    IsStochastic (timeReversal K π) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold timeReversal
    exact div_nonneg (mul_nonneg (hπpos y).le (hK.1 y x)) (hπpos x).le
  · unfold timeReversal
    rw [← Finset.sum_div]
    have := congrFun hπ.2 x
    simp only [Matrix.vecMul, dotProduct] at this
    rw [this, div_self (hπpos x).ne']

open MarkovMixing in
lemma timeReversal_isStationary (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) :
    IsStationary (timeReversal K π) π := by
  refine ⟨hπ.1, ?_⟩
  funext y
  simp only [Matrix.vecMul, dotProduct]
  unfold timeReversal
  have e : ∀ x, π x * (π y * K y x / π x) = π y * K y x := fun x => by
    field_simp [(hπpos x).ne']
  simp_rw [e, ← Finset.mul_sum, hK.2 y, mul_one]

open LogSobolevMC.ChiSquare in
lemma heatOp_add (K : Matrix V V ℝ) (s t : ℝ) (f : V → ℝ) :
    heatOp K (s + t) f = heatOp K s (heatOp K t f) := by
  unfold heatOp
  rw [heatKernel_add, ← Matrix.mulVec_mulVec]

open MarkovMixing LogSobolevMC.ChiSquare in
lemma hasDerivAt_entF_heatOp (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => entF π (heatOp K s f))
      (-dirichlet K π (heatOp K t f) (fun x => Real.log (heatOp K t f x))) t := by
  have hpos : ∀ x, 0 < heatOp K t f x := heatOp_pos K hK t ht f hf
  have h0 := lemma_2_5_ent_core K hK π hπ hπpos (heatOp K t f) hpos
  have h1 := HasDerivAt.comp_add_const (f := fun s => entF π (heatOp K s (heatOp K t f))) t (-t)
    (by rw [add_neg_cancel]; exact h0)
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show entF π (heatOp K s f) = entF π (heatOp K (s + -t) (heatOp K t f))
  rw [← heatOp_add]
  congr 2
  ring

open MarkovMixing LogSobolevMC.ChiSquare in
lemma dirichlet_timeReversal (K : Matrix V V ℝ) (π : V → ℝ) (hπpos : ∀ x, 0 < π x)
    (f h : V → ℝ) :
    dirichlet (timeReversal K π) π f h = dirichlet K π h f := by
  unfold dirichlet
  have e1 : ∑ x, ((timeReversal K π).mulVec f) x * h x * π x
      = ∑ x, (K.mulVec h) x * f x * π x := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold timeReversal
    field_simp [(hπpos b).ne']
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [e1]
  congr 1
  apply Finset.sum_congr rfl; intro x _
  ring

open MarkovMixing LogSobolevMC.ChiSquare in
lemma dirichlet_self_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ dirichlet K π f f := by
  rw [dirichlet_eq_double K hK]
  have h1 : ∑ x, ∑ y, π x * K x y * f y ^ 2 = ∑ x, ∑ y, π x * K x y * f x ^ 2 := by
    rw [Finset.sum_comm]
    have hl : ∀ y, ∑ x, π x * K x y * f y ^ 2 = f y ^ 2 * π y := by
      intro y
      rw [← Finset.sum_mul]
      have := congrFun hπ.2 y
      simp only [Matrix.vecMul, dotProduct] at this
      rw [this]; ring
    have hr : ∀ x, ∑ y, π x * K x y * f x ^ 2 = f x ^ 2 * π x := by
      intro x
      rw [← Finset.sum_mul, ← Finset.mul_sum, hK.2 x]; ring
    simp_rw [hl, hr]
  have e : ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2
      = 2 * (∑ x, ∑ y, π x * K x y * ((f x - f y) * f x))
        - ∑ x, ∑ y, π x * K x y * f x ^ 2 + ∑ x, ∑ y, π x * K x y * f y ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    ring
  have h3 : 0 ≤ ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2 := by
    apply Finset.sum_nonneg; intro x _
    apply Finset.sum_nonneg; intro y _
    have := mul_nonneg (hπpos x).le (hK.1 x y)
    positivity
  rw [h1] at e
  linarith

open MarkovMixing LogSobolevMC.ChiSquare in
lemma entL_nonneg (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ entL π f := by
  unfold entL
  have hN' : lpNorm π 2 f ^ (2:ℝ) = ∑ x, |f x| ^ (2:ℝ) * π x := by
    unfold lpNorm
    rw [← Real.rpow_mul (Finset.sum_nonneg (fun x _ =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπpos x).le))]
    norm_num
  set N := lpNorm π 2 f ^ (2:ℝ) with hN
  have hterm : ∀ x, 0 ≤ |f x| ^ (2:ℝ) * π x := fun x =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπpos x).le
  have hNnn : 0 ≤ N := by rw [hN']; exact Finset.sum_nonneg (fun x _ => hterm x)
  have hpt : ∀ x, (|f x| ^ (2:ℝ) - N) * π x ≤ |f x| ^ (2:ℝ) * Real.log (|f x| ^ (2:ℝ) / N) * π x := by
    intro x
    apply mul_le_mul_of_nonneg_right _ (hπpos x).le
    have ha : 0 ≤ |f x| ^ (2:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    rcases ha.eq_or_lt with h | h
    · rw [← h]; simp; exact hNnn
    · have hNpos : 0 < N := by
        rw [hN']
        exact lt_of_lt_of_le (mul_pos h (hπpos x))
          (Finset.single_le_sum (fun y _ => hterm y) (Finset.mem_univ x))
      have := Real.one_sub_inv_le_log_of_pos (div_pos h hNpos)
      rw [inv_div] at this
      have h2 := mul_le_mul_of_nonneg_left this h.le
      rw [mul_sub, mul_one, mul_div_cancel₀ _ h.ne'] at h2
      exact h2
  have hsum : ∑ x, (|f x| ^ (2:ℝ) - N) * π x = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2, mul_one]
    rw [← hN']; ring
  rw [← hsum]
  exact Finset.sum_le_sum (fun x _ => hpt x)

open MarkovMixing LogSobolevMC.ChiSquare in
lemma logSobolev_mul_entL_le (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    logSobolev K π * entL π f ≤ dirichlet K π f f := by
  by_cases h : entL π f = 0
  · rw [h, mul_zero]; exact dirichlet_self_nonneg K hK π hπ hπpos f
  · have hpos : 0 < entL π f := lt_of_le_of_ne (entL_nonneg π hπ.1 hπpos f) (Ne.symm h)
    have hbdd : BddBelow {r : ℝ | ∃ g : V → ℝ, entL π g ≠ 0 ∧ r = dirichlet K π g g / entL π g} := by
      refine ⟨0, ?_⟩
      rintro r ⟨g, _, rfl⟩
      exact div_nonneg (dirichlet_self_nonneg K hK π hπ hπpos g) (entL_nonneg π hπ.1 hπpos g)
    have hmem : dirichlet K π f f / entL π f ∈
        {r : ℝ | ∃ g : V → ℝ, entL π g ≠ 0 ∧ r = dirichlet K π g g / entL π g} := ⟨f, h, rfl⟩
    have := csInf_le hbdd hmem
    unfold logSobolev
    rw [← le_div_iff₀ hpos]
    exact this

open MarkovMixing in
lemma measHeat_zero (K : Matrix V V ℝ) (μ : V → ℝ) : measHeat K 0 μ = μ := by
  unfold measHeat; rw [heatKernel_zero, Matrix.vecMul_one]

open MarkovMixing in
lemma measHeat_sum (K : Matrix V V ℝ) (hK : IsStochastic K) (t : ℝ) (ht : 0 ≤ t) (μ : V → ℝ) :
    ∑ y, measHeat K t μ y = ∑ x, μ x := by
  unfold measHeat
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.mul_sum, (heatKernel_isStochastic K hK t ht).2 x, mul_one]

lemma relEnt_density (π : V → ℝ) (hπpos : ∀ x, 0 < π x) (g : V → ℝ) :
    relEnt π (fun x => g x * π x) = entF π g := by
  unfold relEnt entF
  apply Finset.sum_congr rfl; intro x _
  rw [mul_div_assoc, div_self (hπpos x).ne', mul_one]
  ring

open MarkovMixing LogSobolevMC.ChiSquare in
lemma decay_pos (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : IsDist μ) (hμpos : ∀ x, 0 < μ x) (c : ℝ) (hc : 0 ≤ c)
    (hdir : ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * dirichlet K π (fun x => Real.sqrt (g x)) (fun x => Real.sqrt (g x)) ≤
        dirichlet K π (fun x => Real.log (g x)) g)
    (t : ℝ) (ht : 0 ≤ t) :
    relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-(c * logSobolev K π * t)) := by
  have hKr := timeReversal_isStochastic K hK π hπ hπpos
  have hπr := timeReversal_isStationary K hK π hπ hπpos
  set Kr := timeReversal K π with hKr_def
  set h : V → ℝ := fun x => μ x / π x with hh_def
  have hμh : μ = fun x => h x * π x := by
    funext x; simp only [hh_def]; rw [div_mul_cancel₀ _ (hπpos x).ne']
  have hh : ∀ x, 0 < h x := fun x => div_pos (hμpos x) (hπpos x)
  set Φ : ℝ → ℝ := fun s => relEnt π (measHeat K s μ) with hΦ_def
  have hdens : ∀ s, measHeat K s μ = fun y => heatOp Kr s h y * π y := by
    intro s
    rw [hμh]
    exact LogSobolevMC.Entropy.density_measHeat K hK π hπ hπpos h s
  have hΦ : ∀ s, Φ s = entF π (heatOp Kr s h) := by
    intro s
    simp only [hΦ_def]
    rw [hdens s, relEnt_density π hπpos]
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt Φ
      (-dirichlet Kr π (heatOp Kr s h) (fun x => Real.log (heatOp Kr s h x))) s := by
    intro s hs
    have hfun : Φ = fun s => entF π (heatOp Kr s h) := funext hΦ
    rw [hfun]
    exact hasDerivAt_entF_heatOp Kr hKr π hπr hπpos h hh s hs
  have hbound : ∀ s, 0 ≤ s →
      -dirichlet Kr π (heatOp Kr s h) (fun x => Real.log (heatOp Kr s h x)) ≤
        -(c * logSobolev K π) * Φ s := by
    intro s hs
    have hg : ∀ x, 0 < heatOp Kr s h x := fun x => heatOp_pos Kr hKr s hs h hh x
    rw [dirichlet_timeReversal K π hπpos]
    have h1 := hdir (heatOp Kr s h) hg
    have h2 := logSobolev_mul_entL_le K hK π hπ hπpos (fun x => Real.sqrt (heatOp Kr s h x))
    have hnorm : lpNorm π 2 (fun x => Real.sqrt (heatOp Kr s h x)) = 1 := by
      unfold lpNorm
      have e : ∑ x, |Real.sqrt (heatOp Kr s h x)| ^ (2:ℝ) * π x = ∑ x, heatOp Kr s h x * π x := by
        apply Finset.sum_congr rfl; intro x _
        rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hg x).le]
      rw [e]
      have e2 : ∑ x, heatOp Kr s h x * π x = ∑ y, measHeat K s μ y := by
        rw [hdens s]
      rw [e2, measHeat_sum K hK s hs μ, hμ.2, Real.one_rpow]
    have h3 : entL π (fun x => Real.sqrt (heatOp Kr s h x)) = Φ s := by
      rw [LogSobolevMC.Entropy.entL_eq_relEnt π hπ.1 hπpos _ (fun x => Real.sqrt_nonneg _) hnorm, hΦ s,
        ← relEnt_density π hπpos]
      congr 1
      funext x
      rw [Real.sq_sqrt (hg x).le]
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    linarith
  set β := c * logSobolev K π with hβ
  have hΨ : ∀ s, 0 ≤ s → HasDerivAt (fun u => Real.exp (β * u) * Φ u)
      (Real.exp (β * s) * (β * 1) * Φ s + Real.exp (β * s) *
        (-dirichlet Kr π (heatOp Kr s h) (fun x => Real.log (heatOp Kr s h x)))) s := by
    intro s hs
    have he : HasDerivAt (fun u => Real.exp (β * u)) (Real.exp (β * s) * (β * 1)) s :=
      (Real.hasDerivAt_exp _).comp s ((hasDerivAt_id s).const_mul β)
    exact he.mul (hderiv s hs)
  have hanti : AntitoneOn (fun u => Real.exp (β * u) * Φ u) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun s hs => (hΨ s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      exact (hΨ s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hΨ s (le_of_lt hs)).deriv]
      have hb := hbound s (le_of_lt hs)
      have he := Real.exp_pos (β * s)
      have := mul_le_mul_of_nonneg_left hb he.le
      nlinarith
  have hmono := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at hmono
  have hΦ0 : Φ 0 = relEnt π μ := by simp only [hΦ_def]; rw [measHeat_zero]
  rw [hΦ0] at hmono
  have hE := Real.exp_pos (β * t)
  have key : Φ t * Real.exp (β * t) ≤ relEnt π μ := by linarith
  calc Φ t = Φ t * Real.exp (β * t) * Real.exp (-(β * t)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ relEnt π μ * Real.exp (-(β * t)) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le

lemma relEnt_continuous (π : V → ℝ) (hπpos : ∀ x, 0 < π x) (ν : ℝ → V → ℝ)
    (hν : ∀ x, Continuous (fun ε => ν ε x)) : Continuous (fun ε => relEnt π (ν ε)) := by
  have e : ∀ ε, relEnt π (ν ε) = ∑ x, (ν ε x / π x) * Real.log (ν ε x / π x) * π x := by
    intro ε
    unfold relEnt
    apply Finset.sum_congr rfl; intro x _
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (hπpos x).ne']
  simp_rw [e]
  apply continuous_finset_sum; intro x _
  exact (Real.continuous_mul_log.comp ((hν x).div_const _)).mul continuous_const

open MarkovMixing in
lemma measHeat_mix (K : Matrix V V ℝ) (t : ℝ) (μ π : V → ℝ) (ε : ℝ) (y : V) :
    measHeat K t (fun x => (1 - ε) * μ x + ε * π x) y
      = (1 - ε) * measHeat K t μ y + ε * measHeat K t π y := by
  unfold measHeat
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

open MarkovMixing LogSobolevMC.ChiSquare in
lemma decay_general (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : IsDist μ) (c : ℝ) (hc : 0 ≤ c)
    (hdir : ∀ g : V → ℝ, (∀ x, 0 < g x) →
      c * dirichlet K π (fun x => Real.sqrt (g x)) (fun x => Real.sqrt (g x)) ≤
        dirichlet K π (fun x => Real.log (g x)) g)
    (t : ℝ) (ht : 0 ≤ t) :
    relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-(c * logSobolev K π * t)) := by
  set ν : ℝ → V → ℝ := fun ε x => (1 - ε) * μ x + ε * π x with hν_def
  have hν0 : ν 0 = μ := by funext x; simp [hν_def]
  have hcont1 : Continuous (fun ε => relEnt π (measHeat K t (ν ε))) := by
    have e : (fun ε => measHeat K t (ν ε)) = fun ε y => (1 - ε) * measHeat K t μ y + ε * measHeat K t π y := by
      funext ε y; exact measHeat_mix K t μ π ε y
    have : (fun ε => relEnt π (measHeat K t (ν ε))) = fun ε => relEnt π ((fun ε y => (1 - ε) * measHeat K t μ y + ε * measHeat K t π y) ε) := by
      funext ε; rw [← e]
    rw [this]
    apply relEnt_continuous π hπpos
    intro y; fun_prop
  have hcont2 : Continuous (fun ε => relEnt π (ν ε) * Real.exp (-(c * logSobolev K π * t))) := by
    apply Continuous.mul _ continuous_const
    apply relEnt_continuous π hπpos
    intro x; simp only [hν_def]; fun_prop
  have h1 : Filter.Tendsto (fun ε => relEnt π (measHeat K t (ν ε))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (relEnt π (measHeat K t μ))) := by
    have := hcont1.tendsto 0
    rw [hν0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun ε => relEnt π (ν ε) * Real.exp (-(c * logSobolev K π * t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (relEnt π μ * Real.exp (-(c * logSobolev K π * t)))) := by
    have := hcont2.tendsto 0
    rw [hν0] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto h1 h2
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  have hdist : IsDist (ν ε) := by
    refine ⟨fun x => ?_, ?_⟩
    · simp only [hν_def]
      have := hμ.1 x; have := (hπpos x).le
      nlinarith [hε.1, hε.2]
    · simp only [hν_def, Finset.sum_add_distrib, ← Finset.mul_sum, hμ.2, hπ.1.2]; ring
  have hpos : ∀ x, 0 < ν ε x := by
    intro x
    simp only [hν_def]
    have := hμ.1 x; have := hπpos x
    nlinarith [hε.1, hε.2]
  exact decay_pos K hK π hπ hπpos (ν ε) hdist hpos c hc hdir t ht

open MarkovMixing LogSobolevMC.ChiSquare in
theorem theorem_3_6_core (K : Matrix V V ℝ) (hK : IsStochastic K)
    (π : V → ℝ) (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : IsDist μ) :
    (∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-2 * logSobolev K π * t)) ∧
      (DetailedBalance K π → ∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤
          relEnt π μ * Real.exp (-4 * logSobolev K π * t)) := by
  constructor
  · intro t ht
    have := decay_general K hK π hπ hπpos μ hμ 2 (by norm_num)
      (fun g hg => (LogSobolevMC.Entropy.lemma_2_7 K hK π hπ hπpos g hg).1) t ht.le
    rw [show -2 * logSobolev K π * t = -(2 * logSobolev K π * t) by ring]
    exact this
  · intro hdb t ht
    have := decay_general K hK π hπ hπpos μ hμ 4 (by norm_num)
      (fun g hg => (LogSobolevMC.Entropy.lemma_2_7 K hK π hπ hπpos g hg).2 hdb) t ht.le
    rw [show -4 * logSobolev K π * t = -(4 * logSobolev K π * t) by ring]
    exact this

end

section
open LogSobolevMC.Entropy

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    (∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-2 * LogSobolevMC.ChiSquare.logSobolev K π * t)) ∧
      (MarkovMixing.DetailedBalance K π → ∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤
          relEnt π μ * Real.exp (-4 * LogSobolevMC.ChiSquare.logSobolev K π * t)) := by
  exact theorem_3_6_core K hK π hπ hπpos μ hμ

end
