-- Prove2me | solution 1 for GlobalTheory.exists_isPrimitiveRoot_of_injective_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:25:42.259581+00:00
-- url     : https://prove2.me/submissions/c058724d-ffb0-4e77-9328-57b92b3e70c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsIsPrimitiveRootOfInjectiveCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _
end GlobalTheory
