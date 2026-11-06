-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.inverse_square_cube_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:11.760938+00:00
-- url     : https://prove2.me/submissions/fa4913d1-2639-4523-a4f3-f66db65ba9dc

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
import Theorems.Thm_OAI_SevenEighths_InverseMoment_inverse_cube_square_eq_sixth

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring
end OAI.SevenEighths.InverseMoment
