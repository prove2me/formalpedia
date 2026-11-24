-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:47:31.666261+00:00
-- url     : https://prove2.me/submissions/f00b89a4-226f-4f06-bdaf-941d2678f56c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_mem_intw_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ U}
    {φ : V →ₗ[ℂ] W} {ψ : W →ₗ[ℂ] U} (hφ : φ ∈ Intw ρ σ) (hψ : ψ ∈ Intw σ τ) :
    ψ ∘ₗ φ ∈ Intw ρ τ := by
  intro g
  ext v
  simp only [LinearMap.comp_apply]
  rw [mem_intw_apply hφ, mem_intw_apply hψ]
end GlobalTheory.CompanionTheory.TyFin.Maschke
