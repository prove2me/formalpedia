-- Prove2me | solution 1 for HermitekLEAN.phase_normalized_orthogonal_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:12.89287+00:00
-- url     : https://prove2.me/submissions/584ee1f8-e829-4b24-a9d7-af8f9941883c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Theorems.Thm_HermiteLEAN_phase_normalized_orthogonal_reduction


set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (defect : H → ℝ)
    (hdefect_nonneg : ∀ h : H, 0 ≤ defect h)
    (f0 : H)
    (hf0 : ‖f0‖ = 1)
    (C : ℝ)
    (hC : 0 < C)
    (horth : ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ C * defect g)
    (hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖))
    (hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ h : H, ‖h‖ ≤ δ → (inner ℂ h f0).im = 0 → ‖h‖ ≤ Mloc * defect h := by
  exact
    HermiteLEAN.phase_normalized_orthogonal_reduction
      defect hdefect_nonneg f0 hf0 C hC horth hscalar hcompare
end HermitekLEAN
