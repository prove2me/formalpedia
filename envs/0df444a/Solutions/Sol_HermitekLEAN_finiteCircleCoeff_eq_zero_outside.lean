-- Prove2me | solution 1 for HermitekLEAN.finiteCircleCoeff_eq_zero_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:59.239382+00:00
-- url     : https://prove2.me/submissions/8f3c6655-f49c-40d3-93d9-83ea4e391e26

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin D → ℂ) {n : ℕ},
      D ≤ n →
        finiteCircleCoeff k r a n = 0 := by
  intro k D r a n hn
  simp [finiteCircleCoeff, Nat.not_lt.mpr hn]
end HermitekLEAN
