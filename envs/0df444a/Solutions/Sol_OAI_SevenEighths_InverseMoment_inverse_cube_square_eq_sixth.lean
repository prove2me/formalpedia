-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.inverse_cube_square_eq_sixth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:01.952643+00:00
-- url     : https://prove2.me/submissions/dbacb19c-0ae4-43cf-9345-0d1e974557b6

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
theorem _root_.solution {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num
end OAI.SevenEighths.InverseMoment
