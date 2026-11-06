-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.localFourier_trivial_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:45.096096+00:00
-- url     : https://prove2.me/submissions/d2d51d0c-2437-4ead-bfa6-b8bd52a45e6f

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
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he
end OAI.SevenEighths.InverseMoment
