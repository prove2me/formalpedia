-- Prove2me | solution 1 for GlobalTheory.BadShare.mass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:44.320368+00:00
-- url     : https://prove2.me/submissions/22fdffa6-d373-41b5-876b-0784ce24942f

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
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution (N : ℕ) (A : (ZMod g)[X] → Prop) : 0 ≤ _root_.GlobalTheory.BadShare.mass g N A :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
