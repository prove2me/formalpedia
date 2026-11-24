-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.exists_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:53.854907+00:00
-- url     : https://prove2.me/submissions/44254334-e297-4080-b80d-47da5a3fcf4a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_id_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_comp

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
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hinj : Function.Injective φ) :
    ∃ ψ ∈ Intw σ ρ, ψ ∘ₗ φ = LinearMap.id := by
  obtain ⟨q, hq⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨avg σ ρ q, avg_mem σ ρ q, ?_⟩
  rw [avg_comp ρ hφ, hq, avg_of_mem (id_mem ρ)]
end GlobalTheory.CompanionTheory.TyFin.Maschke
