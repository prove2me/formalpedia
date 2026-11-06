-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cubic_row_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:08.292049+00:00
-- url     : https://prove2.me/submissions/1fb87535-10d3-4085-8752-70af82be76dc

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_square_eq_star
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_cube_eq_mask

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)
    (a b c : R) :
    χ (a * b ^ 2 * c ^ 3) =
      χ a * star (χ b) * (if IsUnit c then 1 else 0) := by
  rw [map_mul, map_mul, map_pow, cubic_square_eq_star χ hχ,
    cubic_cube_eq_mask χ hχ]
end OAI.SevenEighths.CubicSieve
