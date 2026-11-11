-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat16_exp_exponent_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:06:09.979993+00:00
-- url     : https://prove2.me/submissions/0415b8ce-8201-4bb6-a360-95b8241f1b9f

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_zero
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_continuous
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_injective
import Theorems.Thm_ProbabilityTheory_leanlevy_chat16_continuous_log_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, Complex.exp (LevyFoundations.exponent T ξ) =
       Complex.exp (LevyFoundations.exponent U ξ)) :
    T = U := by
  have hlog : LevyFoundations.exponent T = LevyFoundations.exponent U :=
    ProbabilityTheory.leanlevy_chat16_continuous_log_unique
      (LevyFoundations.leanlevy_chat16_exponent_continuous T)
      (LevyFoundations.leanlevy_chat16_exponent_continuous U)
      (by rw [LevyFoundations.leanlevy_chat16_exponent_zero T,
              LevyFoundations.leanlevy_chat16_exponent_zero U])
      h
  exact LevyFoundations.leanlevy_chat16_exponent_injective T U
    (fun ξ => congrFun hlog ξ)
