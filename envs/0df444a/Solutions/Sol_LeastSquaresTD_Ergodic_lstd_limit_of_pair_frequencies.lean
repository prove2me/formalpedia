-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.lstd_limit_of_pair_frequencies
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:04:37.556712+00:00
-- url     : https://prove2.me/submissions/6272fda3-1663-4bf4-90e0-543923c4f6a8

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD

set_option autoImplicit false

open MeasureTheory Matrix Filter Topology

namespace LSTD0cd3

open LeastSquaresTD.Ergodic

lemma sum_pairs {X : Type*} [Fintype X] [DecidableEq X] {M : Type*} [AddCommMonoid M]
    [Module ℝ M] (z : ℕ → X) (t : ℕ) (f : X → X → M) :
    ∑ k ∈ Finset.range t, f (z k) (z (k + 1)) =
      ∑ x, ∑ y, (pairCount z x y t : ℝ) • f x y := by
  have h : ∀ x y, (pairCount z x y t : ℝ) • f x y =
      ∑ k ∈ Finset.range t, if z k = x ∧ z (k + 1) = y then f x y else 0 := by
    intro x y
    rw [pairCount, Finset.card_filter, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have inner : ∀ k, ∑ x, ∑ y, (if z k = x ∧ z (k + 1) = y then f x y else 0) =
      f (z k) (z (k + 1)) := by
    intro k
    simp only [ite_and]
    rw [Finset.sum_eq_single (z k)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  simp_rw [h]
  calc ∑ k ∈ Finset.range t, f (z k) (z (k + 1))
      = ∑ k ∈ Finset.range t, ∑ x, ∑ y,
          (if z k = x ∧ z (k + 1) = y then f x y else 0) :=
        Finset.sum_congr rfl fun k _ => (inner k).symm
    _ = ∑ x, ∑ k ∈ Finset.range t, ∑ y,
          (if z k = x ∧ z (k + 1) = y then f x y else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm

end LSTD0cd3

open MeasureTheory Matrix Filter Topology LeastSquaresTD.Ergodic in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (z : ℕ → X)
    (hfreq : ∀ x y : X,
      Tendsto (fun t : ℕ => (pairCount z x y t : ℝ) / t) atTop (𝓝 (π x * C.P x y)))
    (hM : IsUnit (lemma5Matrix C φ π γ)) :
    Tendsto (fun t : ℕ => lstdTheta φ R γ t z) atTop
      (𝓝 ((lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π)) := by
  set V : X → X → Matrix (Fin m) (Fin m) ℝ :=
    fun x y => Matrix.vecMulVec (φ x) (φ x - γ • φ y) with hV
  set W : X → X → (Fin m → ℝ) := fun x y => R x y • φ x with hW
  have hA : ∀ t, lstdA φ γ t z = ∑ x, ∑ y, ((pairCount z x y t : ℝ) / t) • V x y := by
    intro t
    rw [lstdA, LSTD0cd3.sum_pairs z t V, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul]; congr 1; ring
  have hB : ∀ t, lstdB φ R t z = ∑ x, ∑ y, ((pairCount z x y t : ℝ) / t) • W x y := by
    intro t
    rw [lstdB, LSTD0cd3.sum_pairs z t W, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul]; congr 1; ring
  have hMeq : lemma5Matrix C φ π γ = ∑ x, ∑ y, (π x * C.P x y) • V x y := by
    ext i j
    simp only [lemma5Matrix, featureMatrix, hV, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e1 : ∀ y, φ x i * π x * ((if x = y then 1 else 0) - γ * C.P x y) * φ y j =
        (if x = y then φ x i * π x * φ y j else 0) - γ * (φ x i * π x * C.P x y * φ y j) := by
      intro y; split_ifs <;> ring
    have e2 : ∀ y, π x * C.P x y * (φ x i * (φ x j - γ * φ y j)) =
        C.P x y * (π x * φ x i * φ x j) - γ * (φ x i * π x * C.P x y * φ y j) := by
      intro y; ring
    simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, C.row_sum,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hVeq : lemma5Vector C R φ π = ∑ x, ∑ y, (π x * C.P x y) • W x y := by
    ext i
    simp only [lemma5Vector, featureMatrix, hW, Chain.rbar, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have tA : Tendsto (fun t : ℕ => lstdA φ γ t z) atTop (𝓝 (lemma5Matrix C φ π γ)) := by
    simp_rw [hA, hMeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have tB : Tendsto (fun t : ℕ => lstdB φ R t z) atTop (𝓝 (lemma5Vector C R φ π)) := by
    simp_rw [hB, hVeq]
    refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
    exact (hfreq x y).smul_const _
  have hdet : (lemma5Matrix C φ π γ).det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at hM
    exact hM.ne_zero
  have hinv : ContinuousAt Inv.inv (lemma5Matrix C φ π γ) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have tI := hinv.tendsto.comp tA
  have hc : Continuous fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => p.1 *ᵥ p.2 :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  exact (hc.tendsto _).comp (tI.prodMk_nhds tB)
