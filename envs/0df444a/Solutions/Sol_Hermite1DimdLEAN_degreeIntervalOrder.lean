-- Prove2me | solution 1 for Hermite1DimdLEAN.degreeIntervalOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:40.012261+00:00
-- url     : https://prove2.me/submissions/18884496-4299-4e8e-8c4f-4467d69f901f

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeIntervalLower j M ≤ degreeIntervalUpper j M := by
  dsimp [degreeIntervalLower, degreeIntervalUpper]
  refine Finset.sum_le_sum fun q _ => ?_
  have hsquare : (max (j q) M - M) ^ 2 ≤ (j q) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hmono : (j q + 1) ^ 2 ≤ (j q + M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hstep : (j q) ^ 2 + 1 ≤ (j q + 1) ^ 2 := by ring_nf; omega
  omega
end Hermite1DimdLEAN
