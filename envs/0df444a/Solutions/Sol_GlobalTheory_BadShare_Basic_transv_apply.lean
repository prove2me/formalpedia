-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.transv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:48.51298+00:00
-- url     : https://prove2.me/submissions/5ee4e871-f264-486f-8ddc-6d84ef56dd86

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
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (a b : Fin N) (h : a ≠ b) (i j : Fin N) :
    (transv (g := g) a b h).val i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then 1 else 0) := by
  simp [transv, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
end GlobalTheory.BadShare.Basic
