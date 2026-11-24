-- Prove2me | solution 1 for GlobalTheory.MonoTrace.trace_lift_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:09.052492+00:00
-- url     : https://prove2.me/submissions/798b3da2-a7bc-4466-be83-5a169f96874d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvalues
import Theorems.Thm_GlobalTheory_MonoTrace_bijOn_pow_eq_one
import Theorems.Thm_GlobalTheory_T_finrank_eigenspace_monomial_matrix_lift
import Theorems.Thm_GlobalTheory_T_sum_charpoly_roots_eq_finsum_eigenspace_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoTrace
namespace GlobalTheory.MonoTrace
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n N : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → (N : k) ≠ 0 → (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1 → (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1 → Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) = ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  intro k _ _ θ hθ n N σ c hc hN hA hB
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hE := GlobalTheory.T.finrank_eigenspace_monomial_matrix_lift k θ hθ n σ c hc
  set A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if i = σ j then c j else 0 with hAdef
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = σ j then θ (c j) else 0 with hBdef
  have h1 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank k (Fin n → k) (Matrix.toLin' A) N hN
    (by rw [← Matrix.toLin'_pow, hA, Matrix.toLin'_one]; rfl) θ
  have h2 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank ℂ (Fin n → ℂ) (Matrix.toLin' B) N (by exact_mod_cast hN0)
    (by rw [← Matrix.toLin'_pow, hB, Matrix.toLin'_one]; rfl) id
  rw [Matrix.charpoly_toLin'] at h1 h2
  rw [Matrix.trace_eq_sum_roots_charpoly, h1]
  rw [Multiset.map_id] at h2
  rw [h2]
  symm
  apply finsum_mem_eq_of_bijOn θ (bijOn_pow_eq_one k θ hθ N hN)
  intro μ hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp [hN0] at hμ
  rw [hE μ hμ0]
  rfl
end GlobalTheory.MonoTrace
