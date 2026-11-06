-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.marked_inactive_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:42.711086+00:00
-- url     : https://prove2.me/submissions/58dd0f44-c196-4ce6-88a5-a2104ad408a1

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
import Theorems.Thm_OAI_SevenEighths_InverseMoment_localFourier_zeroMark

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by
  rw [localFourier_zeroMark, mul_one]
end OAI.SevenEighths.InverseMoment
