-- Prove2me | solution 1 for LinearOptimization.network_flow_integrality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T04:18:29.780505+00:00
-- url     : https://prove2.me/submissions/74b8aec1-66d2-40a2-abed-ceb39cf79c4b

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_network_basis_inverse_integer
import Theorems.Thm_LinearOptimization_network_incidence_rank
import Theorems.Thm_LinearOptimization_lp_standard_form_basic_iff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

private lemma eq_inv_mulVec_of_mulVec_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hunit : IsUnit A.det)
    {x b : Fin n → ℝ} (h : A.mulVec x = b) :
    x = A⁻¹.mulVec b := by
  calc
    x = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x := by simp
    _ = (A⁻¹ * A).mulVec x := by rw [A.nonsing_inv_mul hunit]
    _ = A⁻¹.mulVec (A.mulVec x) := by rw [Matrix.mulVec_mulVec]
    _ = A⁻¹.mulVec b := by rw [h]

private lemma integer_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hA : ∀ i j, ∃ z : ℤ, A i j = (z : ℝ))
    (hv : ∀ j, ∃ z : ℤ, v j = (z : ℝ)) :
    ∀ i, ∃ z : ℤ, A.mulVec v i = (z : ℝ) := by
  choose a ha using hA
  choose b hb using hv
  intro i
  refine ⟨∑ j, a i j * b j, ?_⟩
  simp [Matrix.mulVec, dotProduct, ha, hb]

private lemma basis_mulVec_restrict {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Fin n ↪ Fin m)
    (f : Fin m → ℝ) (hsupp : ∀ k, k ∉ Set.range B → f k = 0) :
    (LinearOptimization.basisMatrix A B).mulVec (fun i ↦ f (B i)) = A.mulVec f := by
  funext r
  simp only [LinearOptimization.basisMatrix, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, id_eq]
  rw [← Finset.sum_image (f := fun k ↦ A r k * f k) B.injective.injOn]
  apply Finset.sum_subset (by simp)
  intro k _ hk
  have hk' : k ∉ Set.range B := by
    simpa using hk
  rw [hsupp k hk', mul_zero]

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (cost : Fin m → ℝ)
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (hconn : LinearOptimization.IsConnectedNetwork arcs)
    (_hsum : ∑ i, bsupply i = 0) :
    (∀ B : Fin n ↪ Fin m,
      LinearOptimization.IsStdBasis (LinearOptimization.truncatedIncidence arcs) B →
      ∀ i j, ∃ z : ℤ,
        (LinearOptimization.basisMatrix
          (LinearOptimization.truncatedIncidence arcs) B)⁻¹ i j = (z : ℝ)) ∧
    ((∀ i, ∃ z : ℤ, bsupply i = (z : ℝ)) →
      ∀ f, LinearOptimization.IsBasicSolution
          (LinearOptimization.stdFormSystem
            (LinearOptimization.truncatedIncidence arcs)
            (LinearOptimization.truncatedSupply bsupply)) f →
        ∀ k, ∃ z : ℤ, f k = (z : ℝ)) ∧
    ((∀ k, ∃ z : ℤ, cost k = (z : ℝ)) →
      ∀ B : Fin n ↪ Fin m,
        LinearOptimization.IsStdBasis (LinearOptimization.truncatedIncidence arcs) B →
        ∀ p : Fin n → ℝ,
          (LinearOptimization.basisMatrix
            (LinearOptimization.truncatedIncidence arcs) B)ᵀ.mulVec p =
            (fun i ↦ cost (B i)) →
          ∀ i, ∃ z : ℤ, p i = (z : ℝ)) := by
  classical
  let A := LinearOptimization.truncatedIncidence arcs
  have hA : LinearIndependent ℝ (fun i ↦ A i) := by
    exact LinearOptimization.network_incidence_rank arcs hloop hconn
  have hinv : ∀ B : Fin n ↪ Fin m, LinearOptimization.IsStdBasis A B →
      ∀ i j, ∃ z : ℤ,
        (LinearOptimization.basisMatrix A B)⁻¹ i j = (z : ℝ) := by
    intro B hB
    exact LinearOptimization.network_basis_inverse_integer arcs B hB
  refine ⟨hinv, ?_, ?_⟩
  · intro hbs f hf k
    obtain ⟨hAf, B, hB, hsupport⟩ :=
      (LinearOptimization.lp_standard_form_basic_iff A
        (LinearOptimization.truncatedSupply bsupply) hA f).mp hf
    by_cases hk : k ∈ Set.range B
    · obtain ⟨i, rfl⟩ := hk
      let BM := LinearOptimization.basisMatrix A B
      have hBMunit : IsUnit BM.det := by
        apply (BM.isUnit_iff_isUnit_det.mp)
        apply Matrix.linearIndependent_cols_iff_isUnit.mp
        exact hB
      have hrestrict : BM.mulVec (fun i ↦ f (B i)) =
          LinearOptimization.truncatedSupply bsupply := by
        rw [basis_mulVec_restrict A B f hsupport]
        exact hAf
      have hsolve : (fun i ↦ f (B i)) =
          BM⁻¹.mulVec (LinearOptimization.truncatedSupply bsupply) :=
        eq_inv_mulVec_of_mulVec_eq BM hBMunit hrestrict
      rw [congrFun hsolve i]
      apply integer_mulVec
      · exact hinv B hB
      · intro j
        exact hbs j.castSucc
    · exact ⟨0, by simpa using hsupport k hk⟩
  · intro hcost B hB p hp
    let BM := LinearOptimization.basisMatrix A B
    have hBMunit : IsUnit BM.det := by
      apply (BM.isUnit_iff_isUnit_det.mp)
      apply Matrix.linearIndependent_cols_iff_isUnit.mp
      exact hB
    have hBTunit : IsUnit BMᵀ.det := Matrix.isUnit_det_transpose BM hBMunit
    have hsolve : p = (BMᵀ)⁻¹.mulVec (fun i ↦ cost (B i)) :=
      eq_inv_mulVec_of_mulVec_eq BMᵀ hBTunit hp
    rw [hsolve]
    apply integer_mulVec
    · intro i j
      rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]
      exact hinv B hB j i
    · intro j
      exact hcost (B j)
