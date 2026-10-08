-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_numerator_four
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:08:38.667122+00:00
-- url     : https://prove2.me/submissions/6bb38d8a-275f-4b99-9acb-d7384bac338e

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_certificate_tlDSq_s0
import Theorems.Thm_MazurTransfer_order27_certificate_tlDCb_s0_tlDCb_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlDCb_s2_tlDCb_s3
import Theorems.Thm_MazurTransfer_order27_certificate_tlWZeroX_s0_tlWZeroX_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlWZeroX_s2_tlWZeroX_s3

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







lemma tl_brM0 (f : ℚ) :
    tlMZeroV0 f =
      -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 *
        f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 *
        f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) := by
  simp only [tlMZeroV0]
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


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.DenominatorCube. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Denominator-cube identities for the order-twenty-seven certificate

The denominator-cube coefficient and value identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlDCb_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f
        ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlDCb_s0_tlDCb_s1.1 hT


lemma tlDCb_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c3 f ξ + tlDSqP0c4 f ξ + tlDSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP1c0 f ξ + tlDCbP1c1 f ξ) + (tlDCbP1c2 f ξ + tlDCbP1c3 f ξ)) + ((tlDCbP1c4 f
        ξ + tlDCbP1c5 f ξ) + (tlDCbP1c6 f ξ + tlDCbP1c7 f ξ))) + (((tlDCbP1c8 f ξ +
        tlDCbP1c9 f ξ) + (tlDCbP1c10 f ξ + tlDCbP1c11 f ξ)) + tlDCbP1c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlDCb_s0_tlDCb_s1.2 hT


lemma tlDCb_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) + (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ)) + ((tlDCbP2c4 f
        ξ + tlDCbP2c5 f ξ) + (tlDCbP2c6 f ξ + tlDCbP2c7 f ξ))) + (((tlDCbP2c8 f ξ +
        tlDCbP2c9 f ξ) + (tlDCbP2c10 f ξ + tlDCbP2c11 f ξ)) + (tlDCbP2c12 f ξ + tlDCbP2c13
        f ξ)) := by
  exact MazurTransfer.order27_certificate_tlDCb_s2_tlDCb_s3.1 hT


lemma tlDCb_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) + (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ)) + ((tlDCbP3c4 f
        ξ + tlDCbP3c5 f ξ) + (tlDCbP3c6 f ξ + tlDCbP3c7 f ξ))) + ((tlDCbP3c8 f ξ +
        tlDCbP3c9 f ξ) + (tlDCbP3c10 f ξ + tlDCbP3c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlDCb_s2_tlDCb_s3.2 hT


lemma tlDCb_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f ξ +
      tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ + tlDSqP0c9 f ξ)) *
      (tlD0 f ξ + tlD1 f ξ) =
      (((((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4
        f ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (((tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ) + (tlDCbP1c0 f ξ + tlDCbP1c1 f ξ)) + ((tlDCbP1c2 f ξ + tlDCbP1c3 f
        ξ) + (tlDCbP1c4 f ξ + tlDCbP1c5 f ξ)))) + ((((tlDCbP1c6 f ξ + tlDCbP1c7 f ξ) +
        (tlDCbP1c8 f ξ + tlDCbP1c9 f ξ)) + ((tlDCbP1c10 f ξ + tlDCbP1c11 f ξ) +
        (tlDCbP1c12 f ξ + tlDCbP2c0 f ξ))) + (((tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) +
        (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ)) + ((tlDCbP2c5 f ξ + tlDCbP2c6 f ξ) + (tlDCbP2c7 f
        ξ + tlDCbP2c8 f ξ))))) + (((((tlDCbP2c9 f ξ + tlDCbP2c10 f ξ) + (tlDCbP2c11 f ξ +
        tlDCbP2c12 f ξ)) + ((tlDCbP2c13 f ξ + tlDCbP3c0 f ξ) + (tlDCbP3c1 f ξ + tlDCbP3c2
        f ξ))) + (((tlDCbP3c3 f ξ + tlDCbP3c4 f ξ) + (tlDCbP3c5 f ξ + tlDCbP3c6 f ξ)) +
        ((tlDCbP3c7 f ξ + tlDCbP3c8 f ξ) + (tlDCbP3c9 f ξ + tlDCbP3c10 f ξ)))) +
        tlDCbP3c11 f ξ) := by
  linear_combination
    ((tlDCb_s0 hT) + (tlDCb_s1 hT)) + ((tlDCb_s2 hT) + (tlDCb_s3 hT))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WZeroXSteps. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Zero-weight coefficient identities

The independent zero-weight coefficient identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlWZeroX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1
      f ξ + tlDCbP1c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ))
        + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f
        ξ)))) + tlWZeroXP0c16 f ξ := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1.1 hT


lemma tlWZeroX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP2c0 f ξ +
      tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ) + (tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ)) +
        ((tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ) + (tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ))) +
        (((tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ) + (tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ))
        + ((tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f
        ξ)))) + ((tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ) + tlWZeroXP1c18 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1.2 hT


lemma tlWZeroX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3.1 hT


lemma tlWZeroX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ))) := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3.2 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WZeroX. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The zero-weight value

The aggregate zero-weight identity.
-/



section

namespace MazurTorsion.Kubert

lemma tlWZeroX_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f ξ +
      tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (((tlDCbP0c8 f ξ + tlDCbP0c9 f ξ) +
      (tlDCbP1c0 f ξ + tlDCbP1c1 f ξ)) + ((tlDCbP1c2 f ξ + tlDCbP1c3 f ξ) + (tlDCbP1c4 f ξ +
      tlDCbP1c5 f ξ)))) + ((((tlDCbP1c6 f ξ + tlDCbP1c7 f ξ) + (tlDCbP1c8 f ξ + tlDCbP1c9 f ξ)) +
      ((tlDCbP1c10 f ξ + tlDCbP1c11 f ξ) + (tlDCbP1c12 f ξ + tlDCbP2c0 f ξ))) + (((tlDCbP2c1 f ξ +
      tlDCbP2c2 f ξ) + (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ)) + ((tlDCbP2c5 f ξ + tlDCbP2c6 f ξ) +
      (tlDCbP2c7 f ξ + tlDCbP2c8 f ξ))))) + (((((tlDCbP2c9 f ξ + tlDCbP2c10 f ξ) + (tlDCbP2c11 f ξ
      + tlDCbP2c12 f ξ)) + ((tlDCbP2c13 f ξ + tlDCbP3c0 f ξ) + (tlDCbP3c1 f ξ + tlDCbP3c2 f ξ))) +
      (((tlDCbP3c3 f ξ + tlDCbP3c4 f ξ) + (tlDCbP3c5 f ξ + tlDCbP3c6 f ξ)) + ((tlDCbP3c7 f ξ +
      tlDCbP3c8 f ξ) + (tlDCbP3c9 f ξ + tlDCbP3c10 f ξ)))) + tlDCbP3c11 f ξ)) * tlMZeroV0 f =
      ((((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ))
        + ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ)))
        + (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f
        ξ)) + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ +
        tlWZeroXP0c15 f ξ)))) + ((((tlWZeroXP0c16 f ξ + tlWZeroXP1c0 f ξ) + (tlWZeroXP1c1
        f ξ + tlWZeroXP1c2 f ξ)) + ((tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ) + (tlWZeroXP1c5
        f ξ + tlWZeroXP1c6 f ξ))) + (((tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ) +
        (tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f ξ)) + ((tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ)
        + (tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ))))) + (((((tlWZeroXP1c15 f ξ +
        tlWZeroXP1c16 f ξ) + (tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ)) + ((tlWZeroXP2c0 f ξ
        + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ))) + (((tlWZeroXP2c4 f
        ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ)) + ((tlWZeroXP2c8 f
        ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ)))) +
        ((((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ))) + (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ
        + tlWZeroXP3c3 f ξ)) + ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ
        + tlWZeroXP3c7 f ξ)))))) + (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) +
        (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ)) + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f
        ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f ξ))) := by
  linear_combination
    ((tlWZeroX_s0 hT) + (tlWZeroX_s1 hT)) + ((tlWZeroX_s2 hT) + (tlWZeroX_s3 hT))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumFour. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The fourth kernel numerator term

The fourth independently elaborated numerator term.
-/



section

namespace MazurTorsion.Kubert

lemma tl_mnum₄ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f
      ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^
      4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * (tlD0 f ξ + tlD1 f ξ) ^ 3 =
      ((((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ)) +
        ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f ξ)))) +
        ((((tlWZeroXP0c16 f ξ + tlWZeroXP1c0 f ξ) + (tlWZeroXP1c1 f ξ + tlWZeroXP1c2 f ξ)) +
        ((tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ) + (tlWZeroXP1c5 f ξ + tlWZeroXP1c6 f ξ))) +
        (((tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ) + (tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f ξ)) +
        ((tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ) + (tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ))))) +
        (((((tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ) + (tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ)) +
        ((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ))) +
        (((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ)) +
        ((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ)))) +
        ((((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ)) +
        ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ))) +
        (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ)))))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ)) +
        ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f ξ))) := by
  linear_combination
    -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f
      ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^
      4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * ((tlD0 f ξ + tlD1 f ξ)) * tlDSq_val hT + -(f
      * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f ^
      10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^ 4
      - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * tlDCb_val hT - ((((((tlDCbP0c0 f ξ + tlDCbP0c1
      f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ
      + tlDCbP0c7 f ξ))) + (((tlDCbP0c8 f ξ + tlDCbP0c9 f ξ) + (tlDCbP1c0 f ξ + tlDCbP1c1 f ξ)) +
      ((tlDCbP1c2 f ξ + tlDCbP1c3 f ξ) + (tlDCbP1c4 f ξ + tlDCbP1c5 f ξ)))) + ((((tlDCbP1c6 f ξ +
      tlDCbP1c7 f ξ) + (tlDCbP1c8 f ξ + tlDCbP1c9 f ξ)) + ((tlDCbP1c10 f ξ + tlDCbP1c11 f ξ) +
      (tlDCbP1c12 f ξ + tlDCbP2c0 f ξ))) + (((tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) + (tlDCbP2c3 f ξ +
      tlDCbP2c4 f ξ)) + ((tlDCbP2c5 f ξ + tlDCbP2c6 f ξ) + (tlDCbP2c7 f ξ + tlDCbP2c8 f ξ))))) +
      (((((tlDCbP2c9 f ξ + tlDCbP2c10 f ξ) + (tlDCbP2c11 f ξ + tlDCbP2c12 f ξ)) + ((tlDCbP2c13 f ξ
      + tlDCbP3c0 f ξ) + (tlDCbP3c1 f ξ + tlDCbP3c2 f ξ))) + (((tlDCbP3c3 f ξ + tlDCbP3c4 f ξ) +
      (tlDCbP3c5 f ξ + tlDCbP3c6 f ξ)) + ((tlDCbP3c7 f ξ + tlDCbP3c8 f ξ) + (tlDCbP3c9 f ξ +
      tlDCbP3c10 f ξ)))) + tlDCbP3c11 f ξ)) * tl_brM0 f + tlWZeroX_val hT


end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f
      ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^
      4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * (tlD0 f ξ + tlD1 f ξ) ^ 3 =
      ((((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ)) +
        ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f ξ)))) +
        ((((tlWZeroXP0c16 f ξ + tlWZeroXP1c0 f ξ) + (tlWZeroXP1c1 f ξ + tlWZeroXP1c2 f ξ)) +
        ((tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ) + (tlWZeroXP1c5 f ξ + tlWZeroXP1c6 f ξ))) +
        (((tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ) + (tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f ξ)) +
        ((tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ) + (tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ))))) +
        (((((tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ) + (tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ)) +
        ((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ))) +
        (((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ)) +
        ((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ)))) +
        ((((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ)) +
        ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ))) +
        (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ)))))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ)) +
        ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f ξ))))
 := by
  exact MazurTorsion.Kubert.tl_mnum₄

#print axioms solution

end
