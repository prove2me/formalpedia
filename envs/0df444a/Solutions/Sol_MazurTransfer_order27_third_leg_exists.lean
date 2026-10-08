-- Prove2me | solution 1 for MazurTransfer.order27_third_leg_exists
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:15:12.101109+00:00
-- url     : https://prove2.me/submissions/990b0d03-6d1a-47d6-aea4-1bf10b155125

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_denominator_nonzero
import Theorems.Thm_MazurTransfer_order27_kernel_coordinate
import Theorems.Thm_MazurTransfer_order27_second_denominator_nonzero
import Theorems.Thm_MazurTransfer_order27_third_leg_polynomial

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


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.DenominatorNonzero. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Nonvanishing of the trisection denominator

The independent nonvanishing steps and their denominator consequence.
-/



section

namespace MazurTorsion.Kubert









lemma tl_d_ne {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) ≠ 0 := by
  exact MazurTransfer.order27_denominator_nonzero hf0 hf1 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Scalars. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Trisection and branch scalar identities

The scalar identities used by the order-twenty-seven kernel calculation.
-/



section

namespace MazurTorsion.Kubert

lemma trisection_chunks {f ξ : ℚ} (hT : trisectionPoly f ξ = 0) :
    (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0 := by
  simp only [trisectionPoly] at hT
  simp only [tlT0, tlT1, tlT2, tlT3]
  linear_combination hT








end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.KernelCubic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The kernel cubic identity

The cubic identity obtained from the combined numerator certificate.
-/



section

namespace MazurTorsion.Kubert

lemma kernel_cubic_at {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0)
    (hD : tlD0 f ξ + tlD1 f ξ ≠ 0) :
    kernelCubicM f (((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) / (tlD0 f ξ + tlD1 f ξ)) = 0
      := by
  exact MazurTransfer.order27_kernel_coordinate hT hD



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



lemma zl_e_ne {f Z : ℚ} (hM : kernelCubicM f Z = 0) (hf0 : f ≠ 0)
    (hf1 : f ≠ 1) (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) :
    zlE0 f Z ≠ 0 := by
  exact MazurTransfer.order27_second_denominator_nonzero hM hf0 hf1 hK


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.BigIdentity. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Final third-leg correspondence identity

The staged certificates combine into the cleared Fricke-twisted correspondence
identity for the third leg.
-/



section

namespace MazurTorsion.Kubert

lemma zl_big {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 3 + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f *
      (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 2 * zlE0 f Z
      ^ 2 + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) +
      26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 +
      531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) * zlE0 f Z ^ 4 + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * zlE0 f Z ^ 6 = 0 := by
  exact MazurTransfer.order27_third_leg_polynomial hM


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenThirdLeg. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The third hauptmodul leg of the order-twenty-seven tower

The trisection abscissa produces a third leg completing the `X₀(9)` chain after the two family legs.
-/

namespace MazurTorsion.Kubert



lemma G9F_cleared_atoms (f B : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    orderNineG9F (a2legN f / a2legD f) B * a2legD f ^ 3 =
      a2legN f ^ 2 * a2legD f * B ^ 3 + 36 * a2legN f ^ 2 * a2legD f * B ^ 2 +
        270 * a2legN f ^ 2 * a2legD f * B - a2legN f ^ 3 +
        729 * a2legN f * a2legD f ^ 2 * B ^ 2 + 26244 * a2legN f * a2legD f ^ 2 * B +
        531441 * a2legD f ^ 3 * B := by
  have hD : a2legD f ≠ 0 := by
    simp only [a2legD]
    exact mul_ne_zero (mul_ne_zero hf0 (sub_ne_zero.mpr hf1))
      (pow_ne_zero 3 (quad_ne f))
  simp only [orderNineG9F]
  field_simp

lemma G9F_cleared_eq (f B : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    orderNineG9F (a2legN f / a2legD f) B * a2legD f ^ 3 =
      ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * B ^ 3 + (36 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) * B ^ 2 + (270 * (f
        ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 * (f * (f -
        1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * B + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) := by
  rw [G9F_cleared_atoms f B hf0 hf1]
  simp only [a2legN, a2legD]
  ring

lemma G9F_of_cleared (f B : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hnum :
      ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * B ^ 3 + (36 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) * B ^ 2 + (270 * (f
        ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 * (f * (f -
        1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * B + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) = 0) :
    orderNineG9F (a2legN f / a2legD f) B = 0 := by
  have hD2c : a2legD f ^ 3 ≠ 0 := by
    simp only [a2legD]
    exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero hf0 (sub_ne_zero.mpr hf1))
      (pow_ne_zero 3 (quad_ne f)))
  have h := G9F_cleared_eq f B hf0 hf1
  rw [hnum] at h
  exact (mul_eq_zero.mp h).resolve_right hD2c

/-- The trisection abscissa produces a third leg completing the
`X₀(9)` chain after the two family legs. -/
theorem thirdLeg_exists (f ξ : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, orderNineG9F (a2legN f / a2legD f) s₃ = 0 := by
  have hT' := trisection_chunks hT
  have hD := tl_d_ne hf0 hf1 hT'
  have hMz := kernel_cubic_at hT' hD
  set Z : ℚ := ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) / (tlD0 f ξ + tlD1 f ξ)
  have hE := zl_e_ne hMz hf0 hf1 hK
  have hbig := zl_big hMz
  refine ⟨((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) / zlE0 f Z ^ 2, ?_⟩
  apply G9F_of_cleared f _ hf0 hf1
  have hE2 : zlE0 f Z ^ 2 ≠ 0 := pow_ne_zero 2 hE
  field_simp
  linear_combination hbig

end MazurTorsion.Kubert

end

theorem MazurTransfer.order27_third_leg_exists (f ξ : ℚ)
    (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : MazurTorsion.Kubert.trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s₃ = 0 := by
  exact MazurTorsion.Kubert.thirdLeg_exists f ξ hf0 hf1 hK hT

theorem solution (f ξ : ℚ)
    (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : MazurTorsion.Kubert.trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s₃ = 0 := by
  exact MazurTransfer.order27_third_leg_exists f ξ hf0 hf1 hK hT

#print axioms MazurTransfer.order27_third_leg_exists
#print axioms solution

end
