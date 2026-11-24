-- Prove2me | solution 1 for GlobalTheory.InertZeta.biInv_of_dosetOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:57.323181+00:00
-- url     : https://prove2.me/submissions/34d911d0-315a-428e-808c-0a5cc4456281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
import Theorems.Thm_GlobalTheory_InertZeta_exists_of_dosetOf_eq

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
theorem _root_.solution {F : G → ℂ} (hF : IsBiInv K F) {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    F y.out = F x.out := by
  obtain ⟨a, b, e⟩ := exists_of_dosetOf_eq h
  rw [e, hF a b]
end GlobalTheory.InertZeta
