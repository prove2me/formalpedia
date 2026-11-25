-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.iso_transp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:55.392892+00:00
-- url     : https://prove2.me/submissions/3a89363f-9a9d-4137-8560-67cba8c816c6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
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
    Nonempty (transp e lam ≅ mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL β K) (transp e lam) mu]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h (glEquiv K e g) x
    rw [PI.GreenLabelSurjWork.transp_ρ, MulEquiv.symm_apply_apply] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun γ x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ]
    have := h ((glEquiv K e).symm γ) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this
end GlobalTheory.CompanionTheory.TyFin.IpIso
