-- Prove2me | solution 1 for MarkovProcess.Semigroup.norm_exp_le_exp_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:36:11.630754+00:00
-- url     : https://prove2.me/submissions/a671143d-4fd5-46ce-acc1-e268d477932b

import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Theorems.Thm_MarkovProcess_Semigroup_norm_exp_le_exp_norm_of_norm_one_le

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess.Semigroup

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/












end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/


open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/




namespace MarkovProcess.Semigroup

end MarkovProcess.Semigroup
open MarkovProcess.Semigroup
theorem solution [NormOneClass A] (a : A) : ‖exp a‖ ≤ Real.exp ‖a‖ :=
  norm_exp_le_exp_norm_of_norm_one_le (by rw [norm_one]) a
