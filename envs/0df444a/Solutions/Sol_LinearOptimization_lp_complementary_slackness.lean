-- Prove2me | solution 1 for LinearOptimization.lp_complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:13:15.596142+00:00
-- url     : https://prove2.me/submissions/38915d6f-edf5-4bf0-b76c-c2268a99439d

import Theorems.Thm_LinearOptimization_lp_strong_duality
import Theorems.Thm_LinearOptimization_lp_optimal_certificate
import Theorems.Thm_LinearOptimization_lp_weak_duality
import Mathlib.Tactic.Linarith

open Matrix

private lemma gap_identity {m n : ℕ} (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (p : Fin m → ℝ) :
    (∑ i : Fin m, p i * (P.A i ⬝ᵥ x - P.b i)) +
        (∑ j : Fin n, (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j) =
      P.c ⬝ᵥ x - p ⬝ᵥ P.b := by
  classical
  simp only [dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ i : Fin m, p i * ∑ j : Fin n, P.A i j * x j) =
      ∑ j : Fin n, (∑ i : Fin m, p i * P.A i j) * x j by
    calc
      (∑ i : Fin m, p i * ∑ j : Fin n, P.A i j * x j) =
          ∑ i : Fin m, ∑ j : Fin n, p i * (P.A i j * x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ i : Fin m, p i * (P.A i j * x j) :=
        Finset.sum_comm
      _ = ∑ j : Fin n, (∑ i : Fin m, p i * P.A i j) * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  ring

private lemma row_product_nonneg {m n : ℕ}
    (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.generalFeasibleSet P)
    (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P))
    (i : Fin m) : 0 ≤ p i * (P.A i ⬝ᵥ x - P.b i) := by
  have hxi := hx.1 i
  have hpi := hp.2 i
  cases hrel : P.rowRel i with
  | ge =>
      simp [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
        LinearOptimization.VarSign.IsSatisfiedBy, hrel] at hpi
      simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
      exact mul_nonneg hpi (sub_nonneg.mpr hxi)
  | le =>
      simp [LinearOptimization.dualLP, LinearOptimization.ConstraintRel.dualSign,
        LinearOptimization.VarSign.IsSatisfiedBy, hrel] at hpi
      simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
      exact mul_nonneg_of_nonpos_of_nonpos hpi (sub_nonpos.mpr hxi)
  | eq =>
      simp [LinearOptimization.LinearConstraint.IsSatisfiedAt, hrel] at hxi
      simp [hxi]

private lemma col_product_nonneg {m n : ℕ}
    (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.generalFeasibleSet P)
    (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P))
    (j : Fin n) : 0 ≤ (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j := by
  have hpj := hp.1 j
  have hxj := hx.2 j
  have hneg : (-P.Aᵀ) j ⬝ᵥ p = -(p ⬝ᵥ (fun i ↦ P.A i j)) := by
    simp [dotProduct, mul_comm]
  cases hsign : P.colSign j with
  | nonneg =>
      simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
        LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
      simp [LinearOptimization.VarSign.IsSatisfiedBy, hsign] at hxj
      exact mul_nonneg (sub_nonneg.mpr hpj) hxj
  | nonpos =>
      simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
        LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
      simp [LinearOptimization.VarSign.IsSatisfiedBy, hsign] at hxj
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpj) hxj
  | free =>
      simp [LinearOptimization.dualLP, LinearOptimization.VarSign.dualRel,
        LinearOptimization.LinearConstraint.IsSatisfiedAt, hsign, hneg] at hpj
      simp [hpj]

theorem solution {m n : ℕ}
    (P : LinearOptimization.GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.generalFeasibleSet P)
    (p : Fin m → ℝ)
    (hp : p ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) :
    (LinearOptimization.IsLpOptimal P.c
        (LinearOptimization.generalFeasibleSet P) x ∧
      LinearOptimization.IsLpDualOptimal P.b
        (LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) p) ↔
    ((∀ i, p i * (P.A i ⬝ᵥ x - P.b i) = 0) ∧
      ∀ j, (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j = 0) := by
  classical
  let rowGap : Fin m → ℝ := fun i ↦ p i * (P.A i ⬝ᵥ x - P.b i)
  let colGap : Fin n → ℝ := fun j ↦
    (P.c j - p ⬝ᵥ (fun i ↦ P.A i j)) * x j
  have hrow_nonneg (i : Fin m) : 0 ≤ rowGap i :=
    row_product_nonneg P x hx p hp i
  have hcol_nonneg (j : Fin n) : 0 ≤ colGap j :=
    col_product_nonneg P x hx p hp j
  have hrows_nonneg : 0 ≤ ∑ i : Fin m, rowGap i :=
    Finset.sum_nonneg fun i hi ↦ hrow_nonneg i
  have hcols_nonneg : 0 ≤ ∑ j : Fin n, colGap j :=
    Finset.sum_nonneg fun j hj ↦ hcol_nonneg j
  constructor
  · rintro ⟨hxopt, hpopt⟩
    obtain ⟨q, hqopt, hqeq⟩ := LinearOptimization.lp_strong_duality P x hxopt
    have hpq : q ⬝ᵥ P.b ≤ p ⬝ᵥ P.b := hpopt.2 q hqopt.1
    have hweak := LinearOptimization.lp_weak_duality P x hx p hp
    have heq : p ⬝ᵥ P.b = P.c ⬝ᵥ x := by linarith
    have htotal : (∑ i : Fin m, rowGap i) + (∑ j : Fin n, colGap j) = 0 := by
      simpa [rowGap, colGap, heq] using gap_identity P x p
    constructor
    · intro i
      have hle : rowGap i ≤ ∑ k : Fin m, rowGap k :=
        Finset.single_le_sum (fun k hk ↦ hrow_nonneg k) (Finset.mem_univ i)
      have hnon : 0 ≤ rowGap i := hrow_nonneg i
      change rowGap i = 0
      linarith
    · intro j
      have hle : colGap j ≤ ∑ k : Fin n, colGap k :=
        Finset.single_le_sum (fun k hk ↦ hcol_nonneg k) (Finset.mem_univ j)
      have hnon : 0 ≤ colGap j := hcol_nonneg j
      change colGap j = 0
      linarith
  · rintro ⟨hrow_zero, hcol_zero⟩
    have hrows_zero : (∑ i : Fin m, rowGap i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hrow_zero i
    have hcols_zero : (∑ j : Fin n, colGap j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hcol_zero j
    have hid := gap_identity P x p
    have heq : p ⬝ᵥ P.b = P.c ⬝ᵥ x := by
      simp [rowGap, colGap] at hrows_zero hcols_zero
      linarith
    exact LinearOptimization.lp_optimal_certificate P x hx p hp heq
