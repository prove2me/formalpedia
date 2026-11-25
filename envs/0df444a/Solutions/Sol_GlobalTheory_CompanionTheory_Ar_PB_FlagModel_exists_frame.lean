-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagModel.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:26.855904+00:00
-- url     : https://prove2.me/submissions/37c324cb-9bf1-477c-86ca-5796c953b864

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagModel_isRelevant_alt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagModel_isPrime_alt

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
theorem _root_.solution : ∃ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F ∧ M.GoodAt F (mCoordIdeal M.x) :=
  M.frames _ M.isPrime_alt M.isRelevant_alt le_rfl
end GlobalTheory.CompanionTheory.Ar.PB.FlagModel
