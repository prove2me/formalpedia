-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagModel.lam_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:13.959549+00:00
-- url     : https://prove2.me/submissions/ae0fca63-9cdd-486a-9e3a-15e40cd4244d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagModel_exists_frame
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagModel_x_chart_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [instance] FlagModel.fieldΩ FlagModel.charΩ FlagModel.alg
open GlobalTheory.CompanionTheory.Ar.PB.FlagModel
variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
namespace GlobalTheory.CompanionTheory.Ar.PB.FlagModel
theorem _root_.solution (p : Ψ × Fin N) (hp : M.blk p = none) : M.lam p ≠ 0 := by
  obtain ⟨F, hF, hG⟩ := M.exists_frame
  intro h0
  have h := hF.2.2.2 p hp
  rw [h0, mul_zero] at h
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (M.x_chart_ne le_rfl hG k))
    (hG.2.2 p hp).1 h.symm
end GlobalTheory.CompanionTheory.Ar.PB.FlagModel
