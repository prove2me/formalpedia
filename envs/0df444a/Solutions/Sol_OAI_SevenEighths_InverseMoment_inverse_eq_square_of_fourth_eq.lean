-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.inverse_eq_square_of_fourth_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:08.252557+00:00
-- url     : https://prove2.me/submissions/7e1f5827-7cd8-4cdb-910c-578a34004473

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp
end OAI.SevenEighths.InverseMoment
