-- Prove2me | solution 1 for Hermite1DimdLEAN.productBasisPhaseLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:37.107646+00:00
-- url     : https://prove2.me/submissions/3774362b-ecd8-4328-ae9f-938c945d5a35

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_oneVariableAngularFactorization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma oneDimPhi_phaseLaw
    (k n : ℕ) (t : ℝ) (z : ℂ) :
    oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) * oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ)]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    rw [mul_add, Complex.exp_add]
    conv_lhs => rw [← hz]
    ring
  have hleft :
      oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hrot, hleft, hexp, hright]
  ring
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (κ α : MultiIndex d) (t : ℝ) (z : CSpace d) :
    PhiKappaAlpha κ α (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((totalDegree α : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        PhiKappaAlpha κ α z := by
  /-
  Scaffolding guidance:
  later files use only the induced phase law by total degree, so expose that
  form directly here.
  -/
  unfold PhiKappaAlpha
  simp_rw [oneDimPhi_phaseLaw]
  rw [Finset.prod_mul_distrib]
  have haux :
      (∏ q, Complex.exp (Complex.I * (((α q : ℤ) - (κ q : ℤ) : ℂ) * t))) =
        Complex.exp (Complex.I * ((↑↑(∑ q, α q) - ↑↑(∑ q, κ q)) * ↑t)) := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
  exact
    congrArg (fun c : ℂ => c * ∏ q, oneDimPhi (κ q) (α q) (z q)) haux
end Hermite1DimdLEAN
