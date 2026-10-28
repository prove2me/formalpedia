-- Prove2me | solution 1 for HaahQSP.Decomp.mul_dagger_inv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:25:18.646247+00:00
-- url     : https://prove2.me/submissions/68fd91e7-c0e2-4da3-b251-fea833a8c2cd

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Mathlib
import Definitions.Def_HaahQSP_Decomp_Setting

open scoped Matrix

namespace Aux_HaahQSP_Decomp_mul_dagger_inv_eq_one

open Polynomial

noncomputable def cayley (r : ℝ) : ℂ := (1 + r * Complex.I) / (1 - r * Complex.I)

lemma den_ne (r : ℝ) : (1 - r * Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

lemma cayley_norm (r : ℝ) : ‖cayley r‖ = 1 := by
  unfold cayley
  rw [norm_div]
  have : (1 - r * Complex.I : ℂ) = (starRingEnd ℂ) (1 + r * Complex.I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [this, Complex.norm_conj, div_self]
  rw [Ne, norm_eq_zero]
  intro h0
  have := congrArg Complex.re h0
  simp at this

lemma cayley_inj : Function.Injective cayley := by
  intro r s h
  unfold cayley at h
  rw [div_eq_div_iff (den_ne r) (den_ne s)] at h
  have h2 : (2 * (r - s) : ℝ) * Complex.I = 0 := by
    push_cast
    linear_combination h
  have h3 : ((2 * (r - s) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact h4
    · exact absurd h4 Complex.I_ne_zero
  have : (2 * (r - s) : ℝ) = 0 := by exact_mod_cast h3
  linarith

lemma laurent_zero (n : ℕ) (c : ℤ → ℤ → ℂ) (δ : ℂ)
    (h : ∀ η : ℂ, ‖η‖ = 1 → (∑ j ∈ Finset.Icc (-(n : ℤ)) n, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      η ^ j * η⁻¹ ^ k * c j k) - δ = 0) :
    ∀ t : ℂ, t ≠ 0 → (∑ j ∈ Finset.Icc (-(n : ℤ)) n, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      t ^ j * t⁻¹ ^ k * c j k) - δ = 0 := by
  set I := Finset.Icc (-(n : ℤ)) n
  let P : ℂ[X] := (∑ j ∈ I, ∑ k ∈ I, C (c j k) * X ^ (j - k + 2 * n).toNat) - C δ * X ^ (2 * n)
  have hev : ∀ t : ℂ, t ≠ 0 → P.eval t = t ^ (2 * n) * ((∑ j ∈ I, ∑ k ∈ I,
      t ^ j * t⁻¹ ^ k * c j k) - δ) := by
    intro t ht
    simp only [P, eval_sub, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k hk
      simp only [I, Finset.mem_Icc] at hj hk
      have hnn : 0 ≤ j - k + 2 * (n : ℤ) := by omega
      have e1 : t ^ (j - k + 2 * (n : ℤ)).toNat = t ^ (j - k + 2 * (n : ℤ)) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
      have e2 : t ^ (2 * (n : ℤ)) = t ^ (2 * n) := by
        rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, zpow_add₀ ht, zpow_sub₀ ht, inv_zpow', zpow_neg, e2]
      field_simp
    · ring
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem cayley_inj
    intro r
    simp only [Set.mem_setOf_eq, IsRoot.def]
    have hne : cayley r ≠ 0 := by
      intro h0
      have := cayley_norm r
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [hev _ hne, h _ (cayley_norm r), mul_zero]
  intro t ht
  have := hev t ht
  rw [hP, eval_zero] at this
  have hpow : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht
  exact (mul_eq_zero.1 this.symm).resolve_left hpow

lemma star_eval (n : ℕ) (C : ℤ → HaahQSP.Decomp.Mat2) (η : ℂ) (hη : ‖η‖ = 1) :
    star (HaahQSP.Decomp.eval n C η) = HaahQSP.Decomp.daggerEval n C η⁻¹ := by
  unfold HaahQSP.Decomp.eval HaahQSP.Decomp.daggerEval
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_smul, Matrix.star_eq_conjTranspose]
  congr 1
  have hconj : star η = η⁻¹ := by
    have hη0 : η ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hη; exact zero_ne_one hη
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hη]
    simp
  rw [star_zpow₀, hconj]

lemma prod_expand (n : ℕ) (A B : ℤ → HaahQSP.Decomp.Mat2) (t s : ℂ) (a b : Fin 2) :
    ((∑ j ∈ Finset.Icc (-(n : ℤ)) n, t ^ j • A j) *
      (∑ k ∈ Finset.Icc (-(n : ℤ)) n, s ^ k • B k)) a b =
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      t ^ j * s ^ k * (A j * B k) a b := by
  rw [Finset.sum_mul_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [smul_mul_smul_comm, Matrix.smul_apply, smul_eq_mul]

end Aux_HaahQSP_Decomp_mul_dagger_inv_eq_one

open Aux_HaahQSP_Decomp_mul_dagger_inv_eq_one in
open HaahQSP.Decomp in
theorem solution (n : ℕ) (C : ℤ → Mat2) (hC : PSet n C) :
    ∀ t : ℂ, t ≠ 0 →
      eval n C t * daggerEval n C t⁻¹ = 1 ∧
      daggerEval n C t⁻¹ * eval n C t = 1 := by
  have hcirc : ∀ η : ℂ, ‖η‖ = 1 →
      eval n C η * daggerEval n C η⁻¹ = 1 ∧ daggerEval n C η⁻¹ * eval n C η = 1 := by
    intro η hη
    have hm := hC.2 η hη
    rw [Matrix.mem_specialUnitaryGroup_iff] at hm
    have hu := hm.1
    rw [← star_eval n C η hη]
    exact ⟨Matrix.mem_unitaryGroup_iff.1 hu, Matrix.mem_unitaryGroup_iff'.1 hu⟩
  intro t ht
  constructor
  · ext a b
    have key := laurent_zero n (fun j k => (C j * (C k)ᴴ) a b) ((1 : Mat2) a b)
      (fun η hη => by
        have h1 := congrFun (congrFun (hcirc η hη).1 a) b
        unfold eval daggerEval at h1
        rw [prod_expand] at h1
        rw [h1, sub_self]) t ht
    unfold eval daggerEval
    rw [prod_expand]
    exact sub_eq_zero.1 key
  · have hexp2 : ∀ x : ℂ, ∀ a b : Fin 2, (daggerEval n C x⁻¹ * eval n C x) a b =
        ∑ j ∈ Finset.Icc (-(n : ℤ)) n, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          x ^ j * x⁻¹ ^ k * ((C k)ᴴ * C j) a b := by
      intro x a b
      unfold eval daggerEval
      rw [prod_expand, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      ring
    ext a b
    have key := laurent_zero n (fun j k => ((C k)ᴴ * C j) a b) ((1 : Mat2) a b)
      (fun η hη => by
        have h1 := congrFun (congrFun (hcirc η hη).2 a) b
        rw [hexp2] at h1
        rw [h1, sub_self]) t ht
    rw [hexp2]
    exact sub_eq_zero.1 key
