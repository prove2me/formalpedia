-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:25:03.765996+00:00
-- url     : https://prove2.me/submissions/312cef60-f7bb-406b-a310-4339f405e9db

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_e

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

lemma CBox.neg_contains_e_oai {a : CBox} {z : ℂ} (hz : a.Contains z) : a.neg.Contains (-z) :=
  ⟨RBox.neg_contains_e hz.1,RBox.neg_contains_e hz.2⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_e_oai
