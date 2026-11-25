-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.repIso_of_constituent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:03.699896+00:00
-- url     : https://prove2.me/submissions/85f50e88-7564-4584-8480-57b170b7c8d8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_maschkeFacts
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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrr ρ)
    (hc : IsConstituent τ ρ) : RepIso τ.ρ ρ := by
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨φ, hφ, hne⟩ := hc
  have hpos : 0 < Module.finrank ℂ (Intw τ.ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨φ, hφ⟩, fun h => hne (congrArg Subtype.val h)⟩
  exact hM.2.2.2 Γ _ _ τ.ρ ρ ((hS.1 Γ τ).1 hτ) hρ hpos.ne'
end GlobalTheory.CompanionTheory.TyFin.FromMackey
