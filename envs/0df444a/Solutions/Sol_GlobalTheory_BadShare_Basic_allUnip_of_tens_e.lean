-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.allUnip_of_tens_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:25.456744+00:00
-- url     : https://prove2.me/submissions/c3603c01-201b-4691-bc73-b1f496f6c65e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_isNilpotent_of_isUp

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
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {ι : Type} [Fintype ι] (L : ι → Lev g N) (γ : ι → GG g N)
    (h : tens (fun v => (L v).e) γ ≠ 0) : AllUnip γ := by
  intro v
  have h1 : (L v).e (γ v) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) v (Finset.mem_univ _)
  by_contra h2
  exact h1 (if_neg fun hm => h2 (isNilpotent_of_isUp hm.1))
end GlobalTheory.BadShare.Basic
