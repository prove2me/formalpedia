-- Prove2me | solution 1 for GlobalTheory.InertZeta.exists_of_dosetOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:29.175939+00:00
-- url     : https://prove2.me/submissions/32a09ef9-d509-4756-ab07-d5329ac6613f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
import Theorems.Thm_GlobalTheory_InertZeta_mem_dosetOf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open GlobalTheory GlobalTheory.InertZeta
open Formalism.UG
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.InertZeta
theorem _root_.solution {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    ∃ a b : K, y.out = (a : G) * x.out * b := by
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (mem_dosetOf_iff.2 h)
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
end GlobalTheory.InertZeta
