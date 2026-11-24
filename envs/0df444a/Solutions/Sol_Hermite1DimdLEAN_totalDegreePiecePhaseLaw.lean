-- Prove2me | solution 1 for Hermite1DimdLEAN.totalDegreePiecePhaseLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:16.202028+00:00
-- url     : https://prove2.me/submissions/59463ab2-d5b6-4386-9750-72125756f825

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_productBasisPhaseLaw
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
    {d : ℕ} (κ : MultiIndex d) (n : ℕ) (G : FiniteHermiteSum d) (t : ℝ) (z : CSpace d) :
    evalHermiteSum κ (totalDegreePiece n G) (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((n : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        evalHermiteSum κ (totalDegreePiece n G) z := by
  unfold evalHermiteSum totalDegreePiece
  simp_rw [Finsupp.onFinset_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro α hα
  by_cases hdeg : totalDegree α = n
  · rw [if_pos hdeg, productBasisPhaseLaw]
    simp [hdeg, mul_assoc, mul_left_comm, mul_comm]
  · simp [hdeg]
end Hermite1DimdLEAN
