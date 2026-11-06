-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:20:46.880879+00:00
-- url     : https://prove2.me/submissions/8d0a1cc5-998c-4bae-a242-5c62817e855d

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_inv_checked_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_e

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

lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩


lemma CBox.contains_inv_e_oai {a : CBox} {z : ℂ} (hz : a.Contains z)
    (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
      ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
    a.inv.Contains z⁻¹ :=
  CBox.inv_checked_e hz (RBox.mul_check_e _ _) (RBox.mul_check_e _ _) (RBox.add_check _ _)
    hi (RBox.mul_check_e _ _) (RBox.mul_check_e _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e_oai
