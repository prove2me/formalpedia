-- Prove2me | solution 1 for LogSobolevMC.Entropy.lemma_2_5_ent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:37:02.599978+00:00
-- url     : https://prove2.me/submissions/f032c548-9d07-41aa-a206-afa47e58d541

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting



namespace LogSobolevMC.Entropy

open scoped BigOperators
open scoped Matrix.Norms.Operator
open NormedSpace

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

end LogSobolevMC.Entropy

open LogSobolevMC.Entropy


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    HasDerivAt (fun t : ℝ => entF π (LogSobolevMC.ChiSquare.heatOp K t f))
      (-LogSobolevMC.ChiSquare.dirichlet K π f (fun x => Real.log (f x))) 0 := by
  exact lemma_2_5_ent_core K hK π hπ hπpos f hf
