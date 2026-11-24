-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.coeff_mul_eq_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:15.563599+00:00
-- url     : https://prove2.me/submissions/55740aba-edff-40dc-85ac-7fafc218ef1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

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
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = conv (fun y => a.coeff y) (fun y => b.coeff y) x := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · rfl
  · simp
end GlobalTheory.BadShare.Basic
