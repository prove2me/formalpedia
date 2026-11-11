-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_exponent_injective
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:05:02.281228+00:00
-- url     : https://prove2.me/submissions/3f356d7c-445e-43c7-bd95-6465071c5445

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exp_exponent_injective
import Definitions.Def_levy_foundations_levyKhintchineTriple
open MeasureTheory

theorem solution
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, LevyFoundations.exponent T ξ = LevyFoundations.exponent U ξ) :
    T = U :=
  LevyFoundations.leanlevy_chat16_exp_exponent_injective T U
    (fun ξ => congrArg Complex.exp (h ξ))
