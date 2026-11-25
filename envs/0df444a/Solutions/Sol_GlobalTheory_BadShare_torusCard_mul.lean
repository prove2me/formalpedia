-- Prove2me | solution 1 for GlobalTheory.BadShare.torusCard_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:13.547802+00:00
-- url     : https://prove2.me/submissions/dcc2b693-557c-4e67-bcde-6c73d4b54342

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
theorem _root_.solution {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    _root_.GlobalTheory.BadShare.torusCard g (f * h) = _root_.GlobalTheory.BadShare.torusCard g f * _root_.GlobalTheory.BadShare.torusCard g h := by
  unfold _root_.GlobalTheory.BadShare.torusCard _root_.GlobalTheory.BadShare.degType
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hf hh, Multiset.map_add, Multiset.map_add, Multiset.prod_add]
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
