-- Prove2me | solution 1 for GlobalTheory.T.mass_degType_le_card_cycleType_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:53.954814+00:00
-- url     : https://prove2.me/submissions/37c9338b-febc-497d-869d-38d815adb19d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleType
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Theorems.Thm_GlobalTheory_BadShare_mass_degType_le_cycleType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop), (mass g N fun f => A (degType g f)) ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  first | exact @GlobalTheory.BadShare.mass_degType_le_cycleType | exact GlobalTheory.BadShare.mass_degType_le_cycleType | (intros; apply GlobalTheory.BadShare.mass_degType_le_cycleType <;> assumption)
end _root_.GlobalTheory.T
