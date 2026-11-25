-- Prove2me | solution 1 for GlobalTheory.BadShare.sqSet_eq_monicOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:28:03.394064+00:00
-- url     : https://prove2.me/submissions/8e025af5-ffa0-4b00-b53b-a9d4839497a0

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
theorem _root_.solution (N : ℕ) : sqSet g N =
    (Finset.univ.image fun c : Fin N → ZMod g => Formalism.CyclotomicNorms.monicOf c).filter fun f => Squarefree f ∧ f.coeff 0 ≠ 0 := rfl
end GlobalTheory.BadShare
