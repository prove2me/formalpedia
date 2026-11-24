-- Prove2me | solution 1 for GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:49.8106+00:00
-- url     : https://prove2.me/submissions/e43be095-8f5a-4459-9d95-8a0526dc50db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConjStatement
import Theorems.Thm_GlobalTheory_doubleCoset_fibre_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G), Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) => DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  first | exact @GlobalTheory.doubleCoset_fibre_card | exact GlobalTheory.doubleCoset_fibre_card | (intros; apply GlobalTheory.doubleCoset_fibre_card <;> assumption)
end _root_.GlobalTheory.T
