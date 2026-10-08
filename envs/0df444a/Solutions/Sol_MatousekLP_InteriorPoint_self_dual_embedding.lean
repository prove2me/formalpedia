-- Prove2me | solution 1 for MatousekLP.InteriorPoint.self_dual_embedding
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:17:04.355736+00:00
-- url     : https://prove2.me/submissions/7937f2f0-b152-42ea-a271-c29c315ae83d

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_SelfDual

set_option autoImplicit false

open Matrix MatousekLP.InteriorPoint

private lemma sd_objective {m n : ℕ} (v : VIdx m n → ℝ) :
    qVec m n ⬝ᵥ v = (((n + m + 1 : ℕ) : ℝ) + 1) * vTheta v := by
  simp [dotProduct, qVec, vTheta, Fintype.sum_sum_type]

private lemma sd_zero_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : IsSDFeasible A b c 0 := by
  constructor
  · rw [mulVec_zero]
    intro i
    cases i with
    | inl i => simp [qVec]
    | inr i => simp [qVec]; positivity
  · exact le_refl _

private lemma sd_optimal_theta {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : VIdx m n → ℝ)
    (hv : IsSDOptimal A b c v) : vTheta v = 0 := by
  have hnonneg : 0 ≤ vTheta v := hv.1.2 (Sum.inr ())
  have hopt := hv.2 0 (sd_zero_feasible A b c)
  rw [sd_objective, sd_objective] at hopt
  simp [vTheta] at hopt
  have hk : (0 : ℝ) < ((n + m + 1 : ℕ) : ℝ) + 1 := by positivity
  change v (Sum.inr ()) = 0
  change 0 ≤ v (Sum.inr ()) at hnonneg
  simp only [Nat.cast_add, Nat.cast_one] at hk
  nlinarith

private lemma sd_to_gts {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : VIdx m n → ℝ)
    (hv : IsSDFeasible A b c v) (ht : vTheta v = 0) :
    IsGTSSolution A b c (uX (vU v)) (uY (vU v)) (uTau (vU v)) := by
  have htheta : v (Sum.inr ()) = 0 := ht
  have hrow (i : UIdx m n) : (M0 A b c *ᵥ vU v) i ≤ 0 := by
    have h := hv.1 (Sum.inl i)
    simpa [mulVec, dotProduct, Mmat, qVec, vU, Fintype.sum_sum_type,
      htheta] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [mulVec, dotProduct, M0, uX, uTau, uY, Fintype.sum_sum_type,
      sub_eq_add_neg, Finset.sum_add_distrib, mul_comm] using hrow (Sum.inl i)
  · intro j
    simpa [mulVec, dotProduct, M0, uX, uTau, uY, Fintype.sum_sum_type,
      Finset.sum_neg_distrib, mul_comm] using hrow (Sum.inr (Sum.inl j))
  · simpa [mulVec, dotProduct, M0, uX, uTau, uY, Fintype.sum_sum_type,
      Finset.sum_neg_distrib, sub_eq_add_neg] using hrow (Sum.inr (Sum.inr ()))
  · intro j; exact hv.2 (Sum.inl (Sum.inr (Sum.inl j)))
  · intro i; exact hv.2 (Sum.inl (Sum.inl i))
  · exact hv.2 (Sum.inl (Sum.inr (Sum.inr ())))

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    (∃ v : VIdx m n → ℝ, IsSDFeasible A b c v) ∧
    IsSDBoundedAbove A b c ∧
    (∀ v : VIdx m n → ℝ, IsSDOptimal A b c v →
        vTheta v = 0 ∧ IsGTSSolution A b c (uX (vU v)) (uY (vU v)) (uTau (vU v))) ∧
    (∀ v : VIdx m n → ℝ, IsSDOptimal A b c v → IsStrictlyComplementary A b c v →
        0 < uTau (vU v) ∨ 0 < gtsSlack b c (uX (vU v)) (uY (vU v))) := by
  refine ⟨⟨0, sd_zero_feasible A b c⟩, ⟨0, ?_⟩, ?_, ?_⟩
  · intro v hv
    rw [sd_objective]
    have h : 0 ≤ vTheta v := hv.2 (Sum.inr ())
    have hk : (0 : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) + 1 := by positivity
    exact neg_nonpos.mpr (mul_nonneg hk h)
  · intro v hv
    exact ⟨sd_optimal_theta A b c v hv, sd_to_gts A b c v hv.1
      (sd_optimal_theta A b c v hv)⟩
  · intro v hv hsc
    have htheta : v (Sum.inr ()) = 0 := sd_optimal_theta A b c v hv
    have h := hsc.2 (Sum.inl (Sum.inr (Sum.inr ())))
    simpa [sdSlack, qVec, mulVec, dotProduct, Mmat, M0, uTau, vU, uX, uY,
      gtsSlack, Fintype.sum_sum_type, htheta, Finset.sum_neg_distrib,
      sub_eq_add_neg] using h

