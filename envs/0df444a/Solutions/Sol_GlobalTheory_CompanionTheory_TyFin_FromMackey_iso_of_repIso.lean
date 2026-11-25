-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.iso_of_repIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:47.47531+00:00
-- url     : https://prove2.me/submissions/5d7a9985-0e4e-411a-aa02-d81b17d1af16

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_simpleIffIrr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.FromMackey
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.TyFin.FromMackey
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ τ' : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W)
    (h₁ : RepIso τ.ρ ρ) (h₂ : RepIso ρ σ) (h₃ : RepIso τ'.ρ σ) : Nonempty (τ ≅ τ') := by
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  obtain ⟨e₃, he₃⟩ := h₃
  refine (hS.2 Γ τ τ').2 ⟨(e₁.trans e₂).trans e₃.symm, fun γ v => ?_⟩
  apply e₃.injective
  simp [he₁, he₂, he₃]
end GlobalTheory.CompanionTheory.TyFin.FromMackey
