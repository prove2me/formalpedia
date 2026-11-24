-- Prove2me | solution 1 for HermitekLEAN.hermiteCoeff_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:00.397801+00:00
-- url     : https://prove2.me/submissions/f0d43e41-171c-4881-b033-d49439523b23

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_finiteHermiteSum
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_truncate_eq_finiteHermiteSum
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
    ∀ {k J : ℕ} {G : ℂ → ℂ} (n : ℕ),
      hermiteCoeff k (truncate k J G) n =
        if _h : n < J + 1 then hermiteCoeff k G n else 0 := by
  intro k J G n
  classical
  simp [truncate_eq_finiteHermiteSum, hermiteCoeff_finiteHermiteSum]
end HermitekLEAN
