-- Prove2me | solution 1 for Hermite1DimdLEAN.rhoPointwiseSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:30.865809+00:00
-- url     : https://prove2.me/submissions/c925ce41-c434-43e7-a860-33be50a6e8b6

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
public import Theorems.Thm_Hermite1DimdLEAN_rhoPointwise

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (a u v : ℂ) :
    rho a u ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h := rhoPointwise a u v
  have hsq : (rho a u) ^ 2 ≤ (rho a v + ‖u - v‖) ^ 2 := by
    have hnonneg : 0 ≤ rho a u := abs_nonneg _
    have hneg0 : -(rho a v + ‖u - v‖) ≤ 0 := by
      linarith only [h, hnonneg, abs_nonneg (rho a v), norm_nonneg (u - v)]
    have hneg : -(rho a v + ‖u - v‖) ≤ rho a u := le_trans hneg0 hnonneg
    exact sq_le_sq' hneg h
  have hsum : (rho a v + ‖u - v‖) ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
    linarith only [two_mul_le_add_sq (rho a v) ‖u - v‖]
  exact le_trans hsq hsum
end Hermite1DimdLEAN
