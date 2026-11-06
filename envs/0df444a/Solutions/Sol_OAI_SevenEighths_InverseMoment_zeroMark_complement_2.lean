-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.zeroMark_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:38.501997+00:00
-- url     : https://prove2.me/submissions/11dfe437-91b9-4594-a598-1845bf6dbd66

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
omit [Fintype F]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · simp [zeroMark, hx, MulChar.map_zero]
  · rw [zeroMark, if_neg hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    ring
end OAI.SevenEighths.InverseMoment
