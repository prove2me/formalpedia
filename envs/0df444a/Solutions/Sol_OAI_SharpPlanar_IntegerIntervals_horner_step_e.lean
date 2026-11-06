-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.horner_step_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:30:26.070264+00:00
-- url     : https://prove2.me/submissions/caf2df2a-2793-4238-aa3e-138b92aa3bad

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_add_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_e

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

namespace SharpPlanar
namespace IntegerIntervals

lemma horner_step_e_oai {a b p m c : CBox} {z : ℂ} {k n : ℕ}
    (hz : a.Contains z) (hb : b.Contains (expHorner z (k+1) n))
    (hp : p.RatCheck 1 (k.factorial:ℤ) 0 1) (hm : a.MulCheck b m)
    (hc : p.AddCheck m c) : c.Contains (expHorner z k (n+1)) := by
  have hr : p.Contains ((k.factorial:ℂ)⁻¹) := by simpa using CBox.rat_contains_e hp
  exact CBox.add_contains_e hr (CBox.mul_contains_e hz hb hm) hc

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.horner_step_e_oai := @OAI.SharpPlanar.IntegerIntervals.horner_step_e_oai
