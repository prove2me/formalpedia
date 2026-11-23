-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.op_reg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:48.378927+00:00
-- url     : https://prove2.me/submissions/800858d9-9fba-416b-8e2d-c60134b0a4a5

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
variable (G : Type) [Group G] [Fintype G]
variable {G}
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (e f : G → ℂ) : op (regFn G) e f = conv e f := by
  ext x
  simp [op, regFn, conv, LinearMap.sum_apply, LinearMap.funLeft_apply]
end GlobalTheory.BadShare.Basic
