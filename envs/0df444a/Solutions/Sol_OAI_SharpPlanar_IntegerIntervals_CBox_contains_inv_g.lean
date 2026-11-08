-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:07:25.751201+00:00
-- url     : https://prove2.me/submissions/8ad889e7-5c4e-43de-bcd4-48ed5b304f71

import Mathlib
import Definitions.Def_OAIQ098G087
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_inv_checked_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_g

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


lemma CBox.contains_inv_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z)
    (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
      ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
    a.inv.Contains z⁻¹ :=
  CBox.inv_checked_g hz (RBox.mul_check_g _ _) (RBox.mul_check_g _ _) (RBox.add_check_g _ _)
    hi (RBox.mul_check_g _ _) (RBox.mul_check_g _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g_oai
