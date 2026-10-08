-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_numerator_three
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:08:36.791595+00:00
-- url     : https://prove2.me/submissions/ac88cc4e-a2d9-43e4-8773-9668283da4fd

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_certificate_tlDSq_s0
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s0_tlTOne_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s2_tlTOne_s3
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s4
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s5_tlTOne_s6
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s7_tlTOne_s8
import Theorems.Thm_MazurTransfer_order27_certificate_tlTOne_s9
import Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s0_tlWOneX_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s2
import Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s3_tlWOneX_s4
import Theorems.Thm_MazurTransfer_order27_certificate_tlWOneX_s5

noncomputable section


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





lemma tl_brM1 (f : ℚ) :
    tlMOneV0 f =
      -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4
        - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) := by
  simp only [tlMOneV0]
  ring1




end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.DenominatorSquare. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Denominator-square identities for the order-twenty-seven certificate

The denominator-square coefficient and value identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlDSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlDSq_s0 hT


lemma tlDSq_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ) := by
  linear_combination
    (tlDSq_s0 hT)


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps0To4. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# First-power product identities 0 through 4

The first independent identities for the first-power product.
-/



section

namespace MazurTorsion.Kubert

lemma tlTOne_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ := by
  exact MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1.1 hT


lemma tlTOne_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1.2 hT


lemma tlTOne_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP2c0 f ξ + tlTOneP2c1 f ξ) + (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ)) +
        ((tlTOneP2c4 f ξ + tlTOneP2c5 f ξ) + (tlTOneP2c6 f ξ + tlTOneP2c7 f ξ))) +
        ((tlTOneP2c8 f ξ + tlTOneP2c9 f ξ) + (tlTOneP2c10 f ξ + tlTOneP2c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3.1 hT


lemma tlTOne_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP3c0 f ξ + tlTOneP3c1 f ξ) + (tlTOneP3c2 f ξ + tlTOneP3c3 f ξ)) +
        ((tlTOneP3c4 f ξ + tlTOneP3c5 f ξ) + (tlTOneP3c6 f ξ + tlTOneP3c7 f ξ))) +
        (((tlTOneP3c8 f ξ + tlTOneP3c9 f ξ) + (tlTOneP3c10 f ξ + tlTOneP3c11 f ξ)) +
        tlTOneP3c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3.2 hT


lemma tlTOne_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)) +
        ((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ))) +
        (((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ)) +
        tlTOneP4c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s4 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps5To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# First-power product identities 5 through 9

The remaining independent identities for the first-power product.
-/



section

namespace MazurTorsion.Kubert

lemma tlTOne_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP5c0 f ξ + tlTOneP5c1 f ξ) + (tlTOneP5c2 f ξ + tlTOneP5c3 f ξ)) +
        ((tlTOneP5c4 f ξ + tlTOneP5c5 f ξ) + (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ))) +
        (((tlTOneP5c8 f ξ + tlTOneP5c9 f ξ) + (tlTOneP5c10 f ξ + tlTOneP5c11 f ξ)) +
        tlTOneP5c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s5_tlTOne_s6.1 hT


lemma tlTOne_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP6c0 f ξ + tlTOneP6c1 f ξ) + (tlTOneP6c2 f ξ + tlTOneP6c3 f ξ)) +
        ((tlTOneP6c4 f ξ + tlTOneP6c5 f ξ) + (tlTOneP6c6 f ξ + tlTOneP6c7 f ξ))) +
        (((tlTOneP6c8 f ξ + tlTOneP6c9 f ξ) + (tlTOneP6c10 f ξ + tlTOneP6c11 f ξ)) +
        tlTOneP6c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s5_tlTOne_s6.2 hT


lemma tlTOne_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP7c0 f ξ + tlTOneP7c1 f ξ) + (tlTOneP7c2 f ξ + tlTOneP7c3 f ξ)) +
        ((tlTOneP7c4 f ξ + tlTOneP7c5 f ξ) + (tlTOneP7c6 f ξ + tlTOneP7c7 f ξ))) +
        (((tlTOneP7c8 f ξ + tlTOneP7c9 f ξ) + (tlTOneP7c10 f ξ + tlTOneP7c11 f ξ)) +
        tlTOneP7c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s7_tlTOne_s8.1 hT


lemma tlTOne_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        tlTOneP8c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s7_tlTOne_s8.2 hT


lemma tlTOne_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP9c0 f ξ + tlTOneP9c1 f ξ) + (tlTOneP9c2 f ξ + tlTOneP9c3 f ξ)) +
        ((tlTOneP9c4 f ξ + tlTOneP9c5 f ξ) + (tlTOneP9c6 f ξ + tlTOneP9c7 f ξ))) +
        (((tlTOneP9c8 f ξ + tlTOneP9c9 f ξ) + (tlTOneP9c10 f ξ + tlTOneP9c11 f ξ)) +
        tlTOneP9c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTOne_s9 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOne. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The first-power product value

The aggregate first-power product identity.
-/



section

namespace MazurTorsion.Kubert

lemma tlTOne_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f ξ +
      tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ + tlDSqP0c9 f ξ)) *
      ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        (((tlTOneP0c8 f ξ + tlTOneP1c0 f ξ) + (tlTOneP1c1 f ξ + tlTOneP1c2 f ξ)) +
        ((tlTOneP1c3 f ξ + tlTOneP1c4 f ξ) + (tlTOneP1c5 f ξ + tlTOneP1c6 f ξ)))) +
        ((((tlTOneP1c7 f ξ + tlTOneP1c8 f ξ) + (tlTOneP1c9 f ξ + tlTOneP2c0 f ξ)) +
        ((tlTOneP2c1 f ξ + tlTOneP2c2 f ξ) + (tlTOneP2c3 f ξ + tlTOneP2c4 f ξ))) +
        (((tlTOneP2c5 f ξ + tlTOneP2c6 f ξ) + (tlTOneP2c7 f ξ + tlTOneP2c8 f ξ)) +
        ((tlTOneP2c9 f ξ + tlTOneP2c10 f ξ) + (tlTOneP2c11 f ξ + tlTOneP3c0 f ξ))))) +
        (((((tlTOneP3c1 f ξ + tlTOneP3c2 f ξ) + (tlTOneP3c3 f ξ + tlTOneP3c4 f ξ)) +
        ((tlTOneP3c5 f ξ + tlTOneP3c6 f ξ) + (tlTOneP3c7 f ξ + tlTOneP3c8 f ξ))) +
        (((tlTOneP3c9 f ξ + tlTOneP3c10 f ξ) + (tlTOneP3c11 f ξ + tlTOneP3c12 f ξ)) +
        ((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)))) +
        ((((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ)) +
        ((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ))) +
        (((tlTOneP4c12 f ξ + tlTOneP5c0 f ξ) + (tlTOneP5c1 f ξ + tlTOneP5c2 f ξ)) +
        ((tlTOneP5c3 f ξ + tlTOneP5c4 f ξ) + (tlTOneP5c5 f ξ + tlTOneP5c6 f ξ)))))) +
        ((((((tlTOneP5c7 f ξ + tlTOneP5c8 f ξ) + (tlTOneP5c9 f ξ + tlTOneP5c10 f ξ)) +
        ((tlTOneP5c11 f ξ + tlTOneP5c12 f ξ) + (tlTOneP6c0 f ξ + tlTOneP6c1 f ξ))) +
        (((tlTOneP6c2 f ξ + tlTOneP6c3 f ξ) + (tlTOneP6c4 f ξ + tlTOneP6c5 f ξ)) +
        ((tlTOneP6c6 f ξ + tlTOneP6c7 f ξ) + (tlTOneP6c8 f ξ + tlTOneP6c9 f ξ)))) +
        ((((tlTOneP6c10 f ξ + tlTOneP6c11 f ξ) + (tlTOneP6c12 f ξ + tlTOneP7c0 f ξ)) +
        ((tlTOneP7c1 f ξ + tlTOneP7c2 f ξ) + (tlTOneP7c3 f ξ + tlTOneP7c4 f ξ))) +
        (((tlTOneP7c5 f ξ + tlTOneP7c6 f ξ) + (tlTOneP7c7 f ξ + tlTOneP7c8 f ξ)) +
        ((tlTOneP7c9 f ξ + tlTOneP7c10 f ξ) + (tlTOneP7c11 f ξ + tlTOneP7c12 f ξ))))) +
        (((((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        ((tlTOneP8c12 f ξ + tlTOneP9c0 f ξ) + (tlTOneP9c1 f ξ + tlTOneP9c2 f ξ)))) +
        ((((tlTOneP9c3 f ξ + tlTOneP9c4 f ξ) + (tlTOneP9c5 f ξ + tlTOneP9c6 f ξ)) +
        ((tlTOneP9c7 f ξ + tlTOneP9c8 f ξ) + (tlTOneP9c9 f ξ + tlTOneP9c10 f ξ))) +
        (tlTOneP9c11 f ξ + tlTOneP9c12 f ξ)))) := by
  linear_combination
    ((((tlTOne_s0 hT) + (tlTOne_s1 hT)) + ((tlTOne_s2 hT) + (tlTOne_s3 hT))) + (((tlTOne_s4 hT) +
      (tlTOne_s5 hT)) + ((tlTOne_s6 hT) + (tlTOne_s7 hT)))) + ((tlTOne_s8 hT) + (tlTOne_s9 hT))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneXSteps0To2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# First-weight identities 0 through 2

The first independent first-weight identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlWOneX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP2c0 f ξ +
      tlTOneP2c1 f ξ) * tlMOneV0 f =
      (((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + tlWOneXP0c14 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1.1 hT


lemma tlWOneX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ +
      tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
      tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ +
      tlTOneP3c10 f ξ) * tlMOneV0 f =
      ((((tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ) + (tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ)) +
        ((tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ))) +
        (((tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ)) +
        ((tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ) + (tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ))))
        + tlWOneXP1c16 f ξ := by
  exact MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1.2 hT


lemma tlWOneX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
      tlTOneP5c5 f ξ) * tlMOneV0 f =
      ((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + tlWOneXP2c18 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWOneX_s2 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneXSteps3To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# First-weight identities 3 through 5

The remaining independent first-weight identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlWOneX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ))
        := by
  exact MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4.1 hT


lemma tlWOneX_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4.2 hT


lemma tlWOneX_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWOneX_s5 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WOneX. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The first-weight value

The aggregate first-weight identity.
-/



section

namespace MazurTorsion.Kubert

lemma tlWOneX_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (((((((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) + ((tlTOneP0c4 f
      ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) + (((tlTOneP0c8 f ξ + tlTOneP1c0 f
      ξ) + (tlTOneP1c1 f ξ + tlTOneP1c2 f ξ)) + ((tlTOneP1c3 f ξ + tlTOneP1c4 f ξ) + (tlTOneP1c5 f
      ξ + tlTOneP1c6 f ξ)))) + ((((tlTOneP1c7 f ξ + tlTOneP1c8 f ξ) + (tlTOneP1c9 f ξ + tlTOneP2c0
      f ξ)) + ((tlTOneP2c1 f ξ + tlTOneP2c2 f ξ) + (tlTOneP2c3 f ξ + tlTOneP2c4 f ξ))) +
      (((tlTOneP2c5 f ξ + tlTOneP2c6 f ξ) + (tlTOneP2c7 f ξ + tlTOneP2c8 f ξ)) + ((tlTOneP2c9 f ξ
      + tlTOneP2c10 f ξ) + (tlTOneP2c11 f ξ + tlTOneP3c0 f ξ))))) + (((((tlTOneP3c1 f ξ +
      tlTOneP3c2 f ξ) + (tlTOneP3c3 f ξ + tlTOneP3c4 f ξ)) + ((tlTOneP3c5 f ξ + tlTOneP3c6 f ξ) +
      (tlTOneP3c7 f ξ + tlTOneP3c8 f ξ))) + (((tlTOneP3c9 f ξ + tlTOneP3c10 f ξ) + (tlTOneP3c11 f
      ξ + tlTOneP3c12 f ξ)) + ((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f
      ξ)))) + ((((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ)) +
      ((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ))) + (((tlTOneP4c12
      f ξ + tlTOneP5c0 f ξ) + (tlTOneP5c1 f ξ + tlTOneP5c2 f ξ)) + ((tlTOneP5c3 f ξ + tlTOneP5c4 f
      ξ) + (tlTOneP5c5 f ξ + tlTOneP5c6 f ξ)))))) + ((((((tlTOneP5c7 f ξ + tlTOneP5c8 f ξ) +
      (tlTOneP5c9 f ξ + tlTOneP5c10 f ξ)) + ((tlTOneP5c11 f ξ + tlTOneP5c12 f ξ) + (tlTOneP6c0 f ξ
      + tlTOneP6c1 f ξ))) + (((tlTOneP6c2 f ξ + tlTOneP6c3 f ξ) + (tlTOneP6c4 f ξ + tlTOneP6c5 f
      ξ)) + ((tlTOneP6c6 f ξ + tlTOneP6c7 f ξ) + (tlTOneP6c8 f ξ + tlTOneP6c9 f ξ)))) +
      ((((tlTOneP6c10 f ξ + tlTOneP6c11 f ξ) + (tlTOneP6c12 f ξ + tlTOneP7c0 f ξ)) + ((tlTOneP7c1
      f ξ + tlTOneP7c2 f ξ) + (tlTOneP7c3 f ξ + tlTOneP7c4 f ξ))) + (((tlTOneP7c5 f ξ + tlTOneP7c6
      f ξ) + (tlTOneP7c7 f ξ + tlTOneP7c8 f ξ)) + ((tlTOneP7c9 f ξ + tlTOneP7c10 f ξ) +
      (tlTOneP7c11 f ξ + tlTOneP7c12 f ξ))))) + (((((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) +
      (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) + ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ +
      tlTOneP8c7 f ξ))) + (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f
      ξ)) + ((tlTOneP8c12 f ξ + tlTOneP9c0 f ξ) + (tlTOneP9c1 f ξ + tlTOneP9c2 f ξ)))) +
      ((((tlTOneP9c3 f ξ + tlTOneP9c4 f ξ) + (tlTOneP9c5 f ξ + tlTOneP9c6 f ξ)) + ((tlTOneP9c7 f ξ
      + tlTOneP9c8 f ξ) + (tlTOneP9c9 f ξ + tlTOneP9c10 f ξ))) + (tlTOneP9c11 f ξ + tlTOneP9c12 f
      ξ))))) * tlMOneV0 f =
      ((((((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP0c14 f ξ + tlWOneXP1c0 f ξ)))) +
        ((((tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ) + (tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ)) +
        ((tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ))) +
        (((tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ)) +
        ((tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ) + (tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ)))))
        + (((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + (tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ))
        + ((tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ))) +
        (((tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ) + (tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ)) +
        ((tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ) + (tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ))))))
        + ((((((tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ) + (tlWOneXP3c15 f ξ + tlWOneXP3c16 f
        ξ)) + ((tlWOneXP3c17 f ξ + tlWOneXP3c18 f ξ) + (tlWOneXP3c19 f ξ + tlWOneXP4c0
        f))) + (((tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ) + (tlWOneXP4c3 f ξ + tlWOneXP4c4 f
        ξ)) + ((tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP4c7 f ξ + tlWOneXP4c8 f
        ξ)))) + ((((tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ) + (tlWOneXP4c11 f ξ + tlWOneXP4c12
        f ξ)) + ((tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ) + (tlWOneXP4c15 f ξ + tlWOneXP4c16
        f ξ))) + (((tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ) + (tlWOneXP4c19 f ξ +
        tlWOneXP4c20 f ξ)) + ((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ +
        tlWOneXP5c3 f ξ))))) + (((((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ
        + tlWOneXP5c7 f ξ)) + ((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ +
        tlWOneXP5c11 f ξ))) + (((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ
        + tlWOneXP5c15 f ξ)) + ((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ
        + tlWOneXP5c19 f ξ)))) + tlWOneXP5c20 f ξ)) := by
  linear_combination
    (((tlWOneX_s0 hT) + (tlWOneX_s1 hT)) + ((tlWOneX_s2 hT) + (tlWOneX_s3 hT))) + ((tlWOneX_s4 hT)
      + (tlWOneX_s5 hT))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumThree. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The third kernel numerator term

The third independently elaborated numerator term.
-/



section

namespace MazurTorsion.Kubert

lemma tl_mnum₃ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 -
      145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) *
      (tlD0 f ξ + tlD1 f ξ) ^ 2 =
      ((((((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP0c14 f ξ + tlWOneXP1c0 f ξ)))) +
        ((((tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ) + (tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ)) +
        ((tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ))) +
        (((tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ)) +
        ((tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ) + (tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ))))) +
        (((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ)))) +
        ((((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + (tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ)) +
        ((tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ))) +
        (((tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ) + (tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ)) +
        ((tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ) + (tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ)))))) +
        ((((((tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ) + (tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ)) +
        ((tlWOneXP3c17 f ξ + tlWOneXP3c18 f ξ) + (tlWOneXP3c19 f ξ + tlWOneXP4c0 f))) +
        (((tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ) + (tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ)) +
        ((tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ)))) +
        ((((tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ) + (tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ)) +
        ((tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ) + (tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ))) +
        (((tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ) + (tlWOneXP4c19 f ξ + tlWOneXP4c20 f ξ)) +
        ((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ))))) +
        (((((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ)) +
        ((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ))) +
        (((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ)) +
        ((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ)))) +
        tlWOneXP5c20 f ξ)) := by
  linear_combination
    -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 -
      145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * (((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)))
      * tlDSq_val hT + -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f
      ^ 5 + 187 * f ^ 4 - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * tlTOne_val hT -
      (((((((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) + ((tlTOneP0c4
      f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) + (((tlTOneP0c8 f ξ + tlTOneP1c0
      f ξ) + (tlTOneP1c1 f ξ + tlTOneP1c2 f ξ)) + ((tlTOneP1c3 f ξ + tlTOneP1c4 f ξ) + (tlTOneP1c5
      f ξ + tlTOneP1c6 f ξ)))) + ((((tlTOneP1c7 f ξ + tlTOneP1c8 f ξ) + (tlTOneP1c9 f ξ +
      tlTOneP2c0 f ξ)) + ((tlTOneP2c1 f ξ + tlTOneP2c2 f ξ) + (tlTOneP2c3 f ξ + tlTOneP2c4 f ξ)))
      + (((tlTOneP2c5 f ξ + tlTOneP2c6 f ξ) + (tlTOneP2c7 f ξ + tlTOneP2c8 f ξ)) + ((tlTOneP2c9 f
      ξ + tlTOneP2c10 f ξ) + (tlTOneP2c11 f ξ + tlTOneP3c0 f ξ))))) + (((((tlTOneP3c1 f ξ +
      tlTOneP3c2 f ξ) + (tlTOneP3c3 f ξ + tlTOneP3c4 f ξ)) + ((tlTOneP3c5 f ξ + tlTOneP3c6 f ξ) +
      (tlTOneP3c7 f ξ + tlTOneP3c8 f ξ))) + (((tlTOneP3c9 f ξ + tlTOneP3c10 f ξ) + (tlTOneP3c11 f
      ξ + tlTOneP3c12 f ξ)) + ((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f
      ξ)))) + ((((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ)) +
      ((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ))) + (((tlTOneP4c12
      f ξ + tlTOneP5c0 f ξ) + (tlTOneP5c1 f ξ + tlTOneP5c2 f ξ)) + ((tlTOneP5c3 f ξ + tlTOneP5c4 f
      ξ) + (tlTOneP5c5 f ξ + tlTOneP5c6 f ξ)))))) + ((((((tlTOneP5c7 f ξ + tlTOneP5c8 f ξ) +
      (tlTOneP5c9 f ξ + tlTOneP5c10 f ξ)) + ((tlTOneP5c11 f ξ + tlTOneP5c12 f ξ) + (tlTOneP6c0 f ξ
      + tlTOneP6c1 f ξ))) + (((tlTOneP6c2 f ξ + tlTOneP6c3 f ξ) + (tlTOneP6c4 f ξ + tlTOneP6c5 f
      ξ)) + ((tlTOneP6c6 f ξ + tlTOneP6c7 f ξ) + (tlTOneP6c8 f ξ + tlTOneP6c9 f ξ)))) +
      ((((tlTOneP6c10 f ξ + tlTOneP6c11 f ξ) + (tlTOneP6c12 f ξ + tlTOneP7c0 f ξ)) + ((tlTOneP7c1
      f ξ + tlTOneP7c2 f ξ) + (tlTOneP7c3 f ξ + tlTOneP7c4 f ξ))) + (((tlTOneP7c5 f ξ + tlTOneP7c6
      f ξ) + (tlTOneP7c7 f ξ + tlTOneP7c8 f ξ)) + ((tlTOneP7c9 f ξ + tlTOneP7c10 f ξ) +
      (tlTOneP7c11 f ξ + tlTOneP7c12 f ξ))))) + (((((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) +
      (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) + ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ +
      tlTOneP8c7 f ξ))) + (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f
      ξ)) + ((tlTOneP8c12 f ξ + tlTOneP9c0 f ξ) + (tlTOneP9c1 f ξ + tlTOneP9c2 f ξ)))) +
      ((((tlTOneP9c3 f ξ + tlTOneP9c4 f ξ) + (tlTOneP9c5 f ξ + tlTOneP9c6 f ξ)) + ((tlTOneP9c7 f ξ
      + tlTOneP9c8 f ξ) + (tlTOneP9c9 f ξ + tlTOneP9c10 f ξ))) + (tlTOneP9c11 f ξ + tlTOneP9c12 f
      ξ))))) * tl_brM1 f + tlWOneX_val hT


end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 -
      145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) *
      (tlD0 f ξ + tlD1 f ξ) ^ 2 =
      ((((((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP0c14 f ξ + tlWOneXP1c0 f ξ)))) +
        ((((tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ) + (tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ)) +
        ((tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ))) +
        (((tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ)) +
        ((tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ) + (tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ))))) +
        (((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ)))) +
        ((((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + (tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ)) +
        ((tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ))) +
        (((tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ) + (tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ)) +
        ((tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ) + (tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ)))))) +
        ((((((tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ) + (tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ)) +
        ((tlWOneXP3c17 f ξ + tlWOneXP3c18 f ξ) + (tlWOneXP3c19 f ξ + tlWOneXP4c0 f))) +
        (((tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ) + (tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ)) +
        ((tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ)))) +
        ((((tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ) + (tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ)) +
        ((tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ) + (tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ))) +
        (((tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ) + (tlWOneXP4c19 f ξ + tlWOneXP4c20 f ξ)) +
        ((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ))))) +
        (((((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ)) +
        ((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ))) +
        (((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ)) +
        ((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ)))) +
        tlWOneXP5c20 f ξ)))
 := by
  exact MazurTorsion.Kubert.tl_mnum₃

#print axioms solution

end
