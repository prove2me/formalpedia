-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.surjective_of_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:44:16.645333+00:00
-- url     : https://prove2.me/submissions/22707880-4870-463f-a0f4-ab592a96db2e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties

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
variable {Γ : Type} [Group Γ]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hσ : IsIrr σ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Surjective φ := by
  have hinv : ∀ g, ∀ w ∈ LinearMap.range φ, σ g w ∈ LinearMap.range φ := fun g w hw => by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨ρ g v, LinearMap.congr_fun (hφ g) v⟩
  rcases hσ.2 _ hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) h0
  · exact LinearMap.range_eq_top.mp h
end GlobalTheory.CompanionTheory.TyFin.Maschke
