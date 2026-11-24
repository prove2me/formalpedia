-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.avg_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:18.715875+00:00
-- url     : https://prove2.me/submissions/408029da-9cce-4aac-b896-93fe06d454db

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_apply
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
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : W →ₗ[ℂ] U) :
    avg σ τ f ∘ₗ φ = avg ρ τ (f ∘ₗ φ) := by
  ext v
  simp only [LinearMap.comp_apply, avg_apply]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mem_intw_apply hφ]
end GlobalTheory.CompanionTheory.TyFin.Maschke
