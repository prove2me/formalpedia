-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.marked_active_eq_neg_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:40.904778+00:00
-- url     : https://prove2.me/submissions/a5878033-fc93-410b-9034-f11e67c572f4

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
import Theorems.Thm_OAI_SevenEighths_InverseMoment_localFourier_zeroMark
import Theorems.Thm_OAI_SevenEighths_InverseMoment_localFourier_trivial_nonzero

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring
end OAI.SevenEighths.InverseMoment
