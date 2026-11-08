-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:39:23.493765+00:00
-- url     : https://prove2.me/submissions/1f530513-a8e9-4bf6-9606-fc2b29fb240c

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_inv_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g

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


lemma CBox.inv_checked_g_oai {a c : CBox} {rr ii den dinv : RBox} {z : ℂ}
    (hz : a.Contains z) (hrr : a.re.MulCheck a.re rr) (hii : a.im.MulCheck a.im ii)
    (hs : rr.AddCheck ii den) (hi : den.InvCheck dinv)
    (hr : a.re.MulCheck dinv c.re) (him : a.im.neg.MulCheck dinv c.im) :
    c.Contains z⁻¹ := by
  have hden : den.Contains (Complex.normSq z) :=
    RBox.add_contains_g (RBox.mul_contains_g hz.1 hz.1 hrr) (RBox.mul_contains_g hz.2 hz.2 hii) hs
  have hdinv := RBox.inv_contains_g hden hi
  constructor
  · simpa [Complex.inv_re,div_eq_mul_inv] using RBox.mul_contains_g hz.1 hdinv hr
  · simpa [Complex.inv_im,div_eq_mul_inv] using RBox.mul_contains_g (RBox.neg_contains_g hz.2) hdinv him

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_g_oai
