-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.cubic_inv_eq_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:51.362034+00:00
-- url     : https://prove2.me/submissions/69452c7f-6153-4f8a-a9f9-7e86d4e0a199

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
omit [Finite Rˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  calc
    χ⁻¹ = χ⁻¹ * χ ^ 3 := by rw [hχ, mul_one]
    _ = χ ^ 2 := by group
end OAI.SevenEighths.CubicSieve
