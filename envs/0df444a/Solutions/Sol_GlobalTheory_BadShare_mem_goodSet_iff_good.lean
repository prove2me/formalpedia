-- Prove2me | solution 1 for GlobalTheory.BadShare.mem_goodSet_iff_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:54.789452+00:00
-- url     : https://prove2.me/submissions/34044c13-366c-4580-992e-7619dcd0f8da

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Theorems.Thm_GlobalTheory_BadShare_good_iff

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
theorem _root_.solution {ι : Type} [Fintype ι] {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ}
    {F : ι → (ZMod g)[X]} : F ∈ _root_.GlobalTheory.BadShare.goodSet g N ch ↔ _root_.GlobalTheory.BadShare.Good g N ch F := by
  rw [_root_.GlobalTheory.BadShare.goodSet, Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨(_root_.GlobalTheory.BadShare.good_iff.1 h).1, h⟩⟩
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
