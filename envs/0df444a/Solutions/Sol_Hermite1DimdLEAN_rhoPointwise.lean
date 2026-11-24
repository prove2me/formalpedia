-- Prove2me | solution 1 for Hermite1DimdLEAN.rhoPointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:01.280041+00:00
-- url     : https://prove2.me/submissions/5a71e3b2-8e37-4a59-bc99-165ccacd4566

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
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
    (a u v : ℂ) :
    rho a u ≤ rho a v + ‖u - v‖ := by
  unfold rho
  let A : ℝ := ‖a + u‖ - ‖a‖
  let B : ℝ := ‖a + v‖ - ‖a‖
  have hAB : |A - B| ≤ ‖u - v‖ := by
    calc
      |A - B| = |‖a + u‖ - ‖a + v‖| := by simp [A, B]
      _ ≤ ‖(a + u) - (a + v)‖ := abs_norm_sub_norm_le (a + u) (a + v)
      _ = ‖u - v‖ := by
        simp_all
  calc
    |A| = |(A - B) + B| := by ring_nf
    _ ≤ |A - B| + |B| := abs_add_le _ _
    _ ≤ ‖u - v‖ + |B| := by gcongr
    _ = rho a v + ‖u - v‖ := by simp [rho, B, add_comm]
end Hermite1DimdLEAN
