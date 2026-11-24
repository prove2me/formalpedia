-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.injective_of_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:47:33.399974+00:00
-- url     : https://prove2.me/submissions/545e33a9-52d7-45c5-8b30-81f2a0316e3e

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
    (hρ : IsIrr ρ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Injective φ := by
  have hinv : ∀ g, ∀ v ∈ LinearMap.ker φ, ρ g v ∈ LinearMap.ker φ := fun g v hv => by
    have h1 : φ (ρ g v) = σ g (φ v) := LinearMap.congr_fun (hφ g) v
    rw [LinearMap.mem_ker] at hv ⊢
    rw [h1, hv, map_zero]
  rcases hρ.2 _ hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) h0
end GlobalTheory.CompanionTheory.TyFin.Maschke
