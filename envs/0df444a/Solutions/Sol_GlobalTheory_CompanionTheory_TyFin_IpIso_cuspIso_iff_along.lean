-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.cuspIso_iff_along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:00.532162+00:00
-- url     : https://prove2.me/submissions/b496c839-0f3f-40cb-8925-8bf70b0e5795

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_along_of_along

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.IpIso
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.TyFin.IpIso
theorem _root_.solution (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    CuspIso K lam mu ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  constructor
  · rintro ⟨e', φ, h⟩
    exact along_of_along lam mu e e' φ h
  · rintro ⟨φ, h⟩
    exact ⟨e, φ, h⟩
end GlobalTheory.CompanionTheory.TyFin.IpIso
