-- Prove2me | solution 1 for MazurTransfer.order27_second_denominator_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:38:25.533895+00:00
-- url     : https://prove2.me/submissions/80192a39-7cb2-432e-a669-7154d3572d1c

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




/-!
# Generated third-leg chunks

This file is one load-balanced shard of the generated polynomial data used by
the order-27 third-leg certificate.
The `order27_rat%` wrapper fixes rational-operation instances during
elaboration while retaining the standard rational expressions after reduction.
-/



section

namespace MazurTorsion.Kubert

lemma quad_ne (f : ℚ) : f ^ 2 - f + 1 ≠ 0 := by
  intro h
  nlinarith [sq_nonneg (2 * f - 1)]

































































































































































































end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.Bezout. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Third-leg denominator nonvanishing certificate

The Bezout identity makes the common denominator nonzero under the noncuspidality
hypotheses. The certificate imports only its polynomial chunks, keeping unrelated
third-leg stages out of the elaboration environment.
-/



section

namespace MazurTorsion.Kubert

lemma zl_bezout {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (tlBezB0 f Z + tlBezB1 f Z + tlBezB2 f Z + tlBezB3 f Z) * zlE0 f Z =
      (f * (f - 1) * (f ^ 2 - f + 1) ^ 6 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 18) := by
  linear_combination (norm := skip)
    (-(tlBezA0 f Z + tlBezA1 f Z + tlBezA2 f Z + tlBezA3 f Z + tlBezA4 Z)) * hM
  simp only [kernelCubicM, tlBezA0, tlBezA1, tlBezA2, tlBezA3, tlBezA4, tlBezB0, tlBezB1,
      tlBezB2, tlBezB3, zlE0]
  ring1

lemma zl_e_ne {f Z : ℚ} (hM : kernelCubicM f Z = 0) (hf0 : f ≠ 0)
    (hf1 : f ≠ 1) (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) :
    zlE0 f Z ≠ 0 := by
  intro h0
  have hb := zl_bezout hM
  rw [h0, mul_zero] at hb
  rcases mul_eq_zero.mp hb.symm with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hf0 h''
      · exact hf1 (sub_eq_zero.mp h'')
    · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h')
  · exact hK (pow_eq_zero_iff (by norm_num) |>.mp h)

end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution {f Z : ℚ} (hM : kernelCubicM f Z = 0) (hf0 : f ≠ 0)
    (hf1 : f ≠ 1) (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) :
    zlE0 f Z ≠ 0  := by
  exact MazurTorsion.Kubert.zl_e_ne hM hf0 hf1 hK

#print axioms solution

end
