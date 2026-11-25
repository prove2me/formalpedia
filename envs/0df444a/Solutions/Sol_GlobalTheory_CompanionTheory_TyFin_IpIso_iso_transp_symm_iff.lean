-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.iso_transp_symm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:01.097224+00:00
-- url     : https://prove2.me/submissions/ad6e0ea4-be5b-42b3-8bf2-bde5379ba7b0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_glEquiv_symm_symm
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible
import Theorems.Thm_P2M_PI_GreenLabelSurjWork_transp___fec5525b2b85


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
    Nonempty (lam ≅ transp e.symm mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL α K) lam (transp e.symm mu)]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h g x
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun g x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    exact h g x
end GlobalTheory.CompanionTheory.TyFin.IpIso
