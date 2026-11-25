-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:07.432385+00:00
-- url     : https://prove2.me/submissions/7d3647fd-95f2-482f-8e0c-9299db6db8c5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_repIso_of_constituent
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_iso_of_repIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_cuspIso_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_cuspIso_trans
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_sqfreeIrr
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_maschkeFacts


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
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {K}
namespace GlobalTheory.CompanionTheory.TyFin.FromMackey
theorem _root_.solution (hMk : MackeyCusp K) : SqfreeUnique K := by
  intro n s s' b b' lam mu τ τ' hτ hτ' hl hm hd ⟨π, hπ⟩
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hd' : ∀ c c', CuspIso K (mu c) (mu c') → c = c' := by
    intro c c' h
    obtain ⟨d, rfl⟩ := π.surjective c
    obtain ⟨d', rfl⟩ := π.surjective c'
    exact congrArg π
      (hd d d' (cuspIso_trans K (hπ d) (cuspIso_trans K h (cuspIso_symm K (hπ d')))))
  have hI : IsIrr (hcRep K b lam) := sqfreeIrr hMk n s b lam hl.1 hl.2.1 hd
  have hI' : IsIrr (hcRep K b' mu) := sqfreeIrr hMk n s' b' mu hm.1 hm.2.1 hd'
  have hne : Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b' mu)) ≠ 0 := by
    rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1]
    haveI : Nonempty {π : Fin s ≃ Fin s' // ∀ c, CuspIso K (lam c) (mu (π c))} := ⟨⟨π, hπ⟩⟩
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  exact iso_of_repIso τ τ' (hcRep K b lam) (hcRep K b' mu)
    (repIso_of_constituent τ _ hτ hI hl.2.2)
    (hM.2.2.2 (GL (Fin n) K) _ _ _ _ hI hI' hne)
    (repIso_of_constituent τ' _ hτ' hI' hm.2.2)
end GlobalTheory.CompanionTheory.TyFin.FromMackey
