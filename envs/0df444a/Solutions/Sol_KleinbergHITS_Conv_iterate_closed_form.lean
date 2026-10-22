-- Prove2me | solution 1 for KleinbergHITS.Conv.iterate_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:38:51.579373+00:00
-- url     : https://prove2.me/submissions/b73a04c7-c995-4573-a398-e2b0f5b93284

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

set_option autoImplicit false
open Matrix
open KleinbergHITS.Conv hiding normalize


theorem hit_opI {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (y : Fin n → ℝ) :
    opI E y = (adjMatrix E)ᵀ *ᵥ y := by
  funext p
  simp [opI, adjMatrix, Matrix.mulVec, dotProduct, Finset.sum_filter, Matrix.transpose_apply]

theorem hit_opO {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (x : Fin n → ℝ) :
    opO E x = adjMatrix E *ᵥ x := by
  funext p
  simp [opO, adjMatrix, Matrix.mulVec, dotProduct, Finset.sum_filter]

theorem hit_normalize_smul {n : ℕ} (c : ℝ) (hc : 0 < c) (v : Fin n → ℝ) :
    KleinbergHITS.Conv.normalize (c • v) = KleinbergHITS.Conv.normalize v := by
  unfold KleinbergHITS.Conv.normalize
  have h1 : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    simp [Finset.mul_sum, mul_pow]
  rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, mul_inv, smul_smul]
  congr 1
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

theorem hit_normalize_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    KleinbergHITS.Conv.normalize (B *ᵥ KleinbergHITS.Conv.normalize w) = KleinbergHITS.Conv.normalize (B *ᵥ w) := by
  by_cases hw : w = 0
  · subst hw; simp [KleinbergHITS.Conv.normalize]
  · have hS : 0 < ∑ i, w i ^ 2 := by
      by_contra h
      apply hw
      funext i
      have h0 : ∑ i, w i ^ 2 = 0 := le_antisymm (not_lt.mp h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp h0 i (Finset.mem_univ i)
      simpa using this
    have hc : 0 < (Real.sqrt (∑ i, w i ^ 2))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hS)
    unfold KleinbergHITS.Conv.normalize
    rw [show (Real.sqrt (∑ i, w i ^ 2))⁻¹ • w = (Real.sqrt (∑ i, w i ^ 2))⁻¹ • w from rfl,
      Matrix.mulVec_smul]
    exact hit_normalize_smul _ hc _

theorem hit_comm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Aᵀ * (A * Aᵀ) ^ m = (Aᵀ * A) ^ m * Aᵀ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]

theorem hit_y {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    ∀ k : ℕ, 1 ≤ k → (hitsIter E k).2 = KleinbergHITS.Conv.normalize (((adjMatrix E * (adjMatrix E)ᵀ) ^ k) *ᵥ allOnes n) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    simp only [hitsIter, hit_opI, hit_opO, Matrix.mulVec_mulVec, pow_one]
  | succ k hk ih =>
    have e : (hitsIter E (k + 1)).2 = KleinbergHITS.Conv.normalize (adjMatrix E *ᵥ (adjMatrix E)ᵀ *ᵥ (hitsIter E k).2) := by
      simp only [hitsIter, hit_opI, hit_opO]
    rw [e, ih, Matrix.mulVec_mulVec, hit_normalize_mulVec, Matrix.mulVec_mulVec, ← pow_succ']

theorem solution {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    ∀ k : ℕ, 1 ≤ k →
      (hitsIter E k).1 =
          KleinbergHITS.Conv.normalize ((((adjMatrix E)ᵀ * adjMatrix E) ^ (k - 1)) *ᵥ ((adjMatrix E)ᵀ *ᵥ allOnes n)) ∧
        (hitsIter E k).2 = KleinbergHITS.Conv.normalize (((adjMatrix E * (adjMatrix E)ᵀ) ^ k) *ᵥ allOnes n) := by
  intro k hk
  refine ⟨?_, hit_y E k hk⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · simp [hitsIter, hit_opI]
  · have e : (hitsIter E (j + 2)).1 = KleinbergHITS.Conv.normalize ((adjMatrix E)ᵀ *ᵥ (hitsIter E (j + 1)).2) := by
      simp only [hitsIter, hit_opI]
    rw [e, hit_y E (j + 1) (by omega), hit_normalize_mulVec, Matrix.mulVec_mulVec, hit_comm,
      ← Matrix.mulVec_mulVec]
    rfl
