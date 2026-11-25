-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters.isIrreducible_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:16.397209+00:00
-- url     : https://prove2.me/submissions/abcb6b94-b8c5-482e-a357-3a211a57c997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
import Theorems.Thm_GlobalTheory_UnimodularLatticeExistence_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open Matrix
namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
theorem _root_.solution {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeExistence.main
  | exact _root_.GlobalTheory.UnimodularLatticeExistence.main
  | (apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeExistence.main ..)
end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
