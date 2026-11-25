-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagModel.isRelevant_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:35.432653+00:00
-- url     : https://prove2.me/submissions/2e044d43-477c-45f9-8034-eff6697e8fba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

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
theorem _root_.solution : IsRelevant (mCoordIdeal M.x) := fun k => by
  obtain ⟨i, hi⟩ := M.x_ne k
  refine ⟨i, fun h => hi ?_⟩
  have h' : mConeMap M.x (X ⟨k, i⟩) = 0 := h
  rw [mConeMap, aeval_X] at h'
  exact C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right (X_ne_zero _))
end GlobalTheory.CompanionTheory.Ar.PB.FlagModel
