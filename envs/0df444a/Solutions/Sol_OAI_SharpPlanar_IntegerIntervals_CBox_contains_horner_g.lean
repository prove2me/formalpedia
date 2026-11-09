-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:51.558583+00:00
-- url     : https://prove2.me/submissions/32986cce-fb18-4bb5-bb02-d4132307354b

import Mathlib
import Definitions.Def_OAIQ098G073
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_add_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_horner_step_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_horner_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ) :
    (a.horner k n).Contains (expHorner z k n) := by
  induction n generalizing k with
  | zero =>
    simpa [CBox.horner,expHorner] using CBox.contains_rat_g 1 (k.factorial:ℤ) 0 1
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num)
  | succ n ih =>
    exact horner_step_g hz (ih (k+1)) (CBox.rat_check_g _ _ _ _
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num))
      (CBox.mul_check_g _ _) (CBox.add_check_g _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_horner_g_oai
