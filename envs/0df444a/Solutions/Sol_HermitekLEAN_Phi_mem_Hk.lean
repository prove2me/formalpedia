-- Prove2me | solution 1 for HermitekLEAN.Phi_mem_Hk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:48.526412+00:00
-- url     : https://prove2.me/submissions/5751795b-a2b7-44d0-a276-0d025ddda12f

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_phi_orthonormal
public import Theorems.Thm_HermitekLEAN_integrable_weightedDiag
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k n : ℕ) : Phi k n ∈ Hk k := by
  refine ⟨integrable_weightedDiag k n, ?_⟩
  intro z
  have hterm : (fun m => weightedInner (Phi k n) (Phi k m) * Phi k m z) =
      fun m => if m = n then Phi k n z else 0 := by
    ext m
    rw [phi_orthonormal]
    by_cases h : n = m
    · simp_all only [↓reduceIte, one_mul]
    · simp [h, show m ≠ n from Ne.symm h]
  rw [hterm]
  exact hasSum_ite_eq n (Phi k n z)
end HermitekLEAN
