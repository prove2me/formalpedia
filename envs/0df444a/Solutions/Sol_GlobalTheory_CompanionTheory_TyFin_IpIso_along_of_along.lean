-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.along_of_along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:24.010816+00:00
-- url     : https://prove2.me/submissions/384a9c33-f048-4da6-ad08-5cfa1bfefd56

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_glEquiv_conj

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
theorem _root_.solution (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e e' : α ≃ β)
    (φ : lam ≃ₗ[ℂ] mu) (h : ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e' g) (φ x)) :
    ∃ ψ : lam ≃ₗ[ℂ] mu, ∀ g x, ψ (lam.ρ g x) = mu.ρ (glEquiv K e g) (ψ x) := by
  set P : GL β K := pm K (e.symm.trans e') with hP
  let m : (mu : Type) ≃ₗ[ℂ] (mu : Type) := LinearEquiv.ofLinear (mu.ρ P⁻¹) (mu.ρ P)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
  refine ⟨φ.trans m, fun g x => ?_⟩
  have hm : ∀ y, m y = mu.ρ P⁻¹ y := fun _ => rfl
  simp only [LinearEquiv.trans_apply, hm]
  rw [h, glEquiv_conj e e' g, ← hP]
  have : P⁻¹ * (P * glEquiv K e g * P⁻¹) = glEquiv K e g * P⁻¹ := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]
end GlobalTheory.CompanionTheory.TyFin.IpIso
