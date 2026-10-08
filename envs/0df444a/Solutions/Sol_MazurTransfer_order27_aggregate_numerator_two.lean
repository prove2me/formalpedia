-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_numerator_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:08:35.06132+00:00
-- url     : https://prove2.me/submissions/66cda856-d0d9-4c36-8b8b-56f87bb09cba

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_certificate_tlNSq_s0_tlNSq_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlNSq_s2_tlNSq_s3
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s0_tlTTwo_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s2_tlTTwo_s3
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s4_tlTTwo_s5
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s6
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s7_tlTTwo_s8
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s9
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s10_tlTTwo_s11
import Theorems.Thm_MazurTransfer_order27_certificate_tlTTwo_s12_tlTTwo_s13
import Theorems.Thm_MazurTransfer_order27_certificate_tlWTwoX_s0_tlWTwoX_s1
import Theorems.Thm_MazurTransfer_order27_certificate_tlWTwoX_s2_tlWTwoX_s3
import Theorems.Thm_MazurTransfer_order27_certificate_tlWTwoX_s4

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorSquare. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Numerator-square identities for the order-twenty-seven certificate

The numerator-square coefficient identities, isolated to bound elaboration memory.
-/



section

namespace MazurTorsion.Kubert

lemma tlNSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f
        ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + tlNSqP0c8 f ξ := by
  exact MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1.1 hT


lemma tlNSq_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) + (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ)) + ((tlNSqP1c4 f
        ξ + tlNSqP1c5 f ξ) + (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ))) + (tlNSqP1c8 f ξ +
        tlNSqP1c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1.2 hT


lemma tlNSq_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP2c0 f ξ + tlNSqP2c1 f ξ) + (tlNSqP2c2 f ξ + tlNSqP2c3 f ξ)) + ((tlNSqP2c4 f
        ξ + tlNSqP2c5 f ξ) + (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ))) + ((tlNSqP2c8 f ξ +
        tlNSqP2c9 f ξ) + (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlNSq_s2_tlNSq_s3.1 hT


lemma tlNSq_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP3c0 f ξ + tlNSqP3c1 f ξ) + (tlNSqP3c2 f ξ + tlNSqP3c3 f ξ)) + ((tlNSqP3c4 f
        ξ + tlNSqP3c5 f ξ) + (tlNSqP3c6 f ξ + tlNSqP3c7 f ξ))) + ((tlNSqP3c8 f ξ +
        tlNSqP3c9 f ξ) + (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlNSq_s2_tlNSq_s3.2 hT


lemma tlNSq_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f
      ξ)) =
      (((((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4
        f ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + (((tlNSqP0c8 f ξ +
        tlNSqP1c0 f ξ) + (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ)) + ((tlNSqP1c3 f ξ + tlNSqP1c4 f
        ξ) + (tlNSqP1c5 f ξ + tlNSqP1c6 f ξ)))) + ((((tlNSqP1c7 f ξ + tlNSqP1c8 f ξ) +
        (tlNSqP1c9 f ξ + tlNSqP2c0 f ξ)) + ((tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) + (tlNSqP2c3 f
        ξ + tlNSqP2c4 f ξ))) + (((tlNSqP2c5 f ξ + tlNSqP2c6 f ξ) + (tlNSqP2c7 f ξ +
        tlNSqP2c8 f ξ)) + ((tlNSqP2c9 f ξ + tlNSqP2c10 f ξ) + (tlNSqP2c11 f ξ + tlNSqP3c0
        f ξ))))) + ((((tlNSqP3c1 f ξ + tlNSqP3c2 f ξ) + (tlNSqP3c3 f ξ + tlNSqP3c4 f ξ)) +
        ((tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) + (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ))) + ((tlNSqP3c9
        f ξ + tlNSqP3c10 f ξ) + tlNSqP3c11 f ξ)) := by
  linear_combination
    ((tlNSq_s0 hT) + (tlNSq_s1 hT)) + ((tlNSq_s2 hT) + (tlNSq_s3 hT))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps0To6. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Second-power product identities 0 through 6

The first independent identities for the second-power product.
-/



section

namespace MazurTorsion.Kubert

lemma tlTTwo_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s0_tlTTwo_s1.1 hT


lemma tlTTwo_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s0_tlTTwo_s1.2 hT


lemma tlTTwo_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ + tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ) + (tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ)) +
        ((tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ) + (tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ))) +
        (((tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ) + (tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ)) +
        ((tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ) + (tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ))) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s2_tlTTwo_s3.1 hT


lemma tlTTwo_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ) + (tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ)) +
        ((tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) + (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ))) +
        ((tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ) + (tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s2_tlTTwo_s3.2 hT


lemma tlTTwo_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s4_tlTTwo_s5.1 hT


lemma tlTTwo_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ) + (tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ)) +
        ((tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ) + (tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ))) +
        (((tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ) + (tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ)) +
        (tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s4_tlTTwo_s5.2 hT


lemma tlTTwo_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c0 f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ) + (tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ)) +
        ((tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ) + (tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ))) +
        (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s6 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps7To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Second-power product identities 7 through 9

The independent second-power product identities for steps 7 through 9.
-/



section

namespace MazurTorsion.Kubert

lemma tlTTwo_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s7_tlTTwo_s8.1 hT


lemma tlTTwo_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s7_tlTTwo_s8.2 hT


lemma tlTTwo_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      ((((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ)) +
        ((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ))) +
        (((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ)) +
        ((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)))) +
        (tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s9 hT


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwoSteps10To13. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Second-power product identities 10 through 13

The remaining independent identities for the second-power product.
-/



section

namespace MazurTorsion.Kubert

lemma tlTTwo_s10 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) + (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ)) +
        ((tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ) + (tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ))) +
        ((tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ) + (tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s10_tlTTwo_s11.1 hT


lemma tlTTwo_s11 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ) + (tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ)) +
        ((tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ) + (tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ))) +
        (((tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ) + (tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ)) +
        (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s10_tlTTwo_s11.2 hT


lemma tlTTwo_s12 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ + tlNSqP3c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
        ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
        (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
        (tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s12_tlTTwo_s13.1 hT


lemma tlTTwo_s13 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ) + (tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ)) +
        ((tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ) + (tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ))) +
        (((tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ) + (tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ)) +
        tlTTwoP13c12 f ξ) := by
  exact MazurTransfer.order27_certificate_tlTTwo_s12_tlTTwo_s13.2 hT


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwo. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The second-power product value

The aggregate second-power product identity.
-/



section

namespace MazurTorsion.Kubert

lemma tlTTwo_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f ξ +
      tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + (((tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) +
      (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ)) + ((tlNSqP1c3 f ξ + tlNSqP1c4 f ξ) + (tlNSqP1c5 f ξ +
      tlNSqP1c6 f ξ)))) + ((((tlNSqP1c7 f ξ + tlNSqP1c8 f ξ) + (tlNSqP1c9 f ξ + tlNSqP2c0 f ξ)) +
      ((tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) + (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ))) + (((tlNSqP2c5 f ξ +
      tlNSqP2c6 f ξ) + (tlNSqP2c7 f ξ + tlNSqP2c8 f ξ)) + ((tlNSqP2c9 f ξ + tlNSqP2c10 f ξ) +
      (tlNSqP2c11 f ξ + tlNSqP3c0 f ξ))))) + ((((tlNSqP3c1 f ξ + tlNSqP3c2 f ξ) + (tlNSqP3c3 f ξ +
      tlNSqP3c4 f ξ)) + ((tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) + (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ))) +
      ((tlNSqP3c9 f ξ + tlNSqP3c10 f ξ) + tlNSqP3c11 f ξ))) * (tlD0 f ξ + tlD1 f ξ) =
      (((((((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (((tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) + (tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ)) +
        ((tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ) + (tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ)))) +
        ((((tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ) + (tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ)) +
        ((tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ) + (tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ))) +
        (((tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ) + (tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ)) +
        ((tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ) + (tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ))))) +
        (((((tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ) + (tlTTwoP2c11 f ξ + tlTTwoP2c12 f ξ)) +
        ((tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ) + (tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ))) +
        (((tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ) + (tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ)) +
        ((tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ) + (tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ)))) +
        ((((tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ) + (tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ)) +
        ((tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ) + (tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ))) +
        (((tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ) + (tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ)) +
        ((tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ) + (tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ)))))) +
        ((((((tlTTwoP4c13 f ξ + tlTTwoP5c0 f ξ) + (tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ)) +
        ((tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ) + (tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ))) +
        (((tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ) + (tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ)) +
        ((tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ) + (tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ)))) +
        ((((tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ) + (tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ)) +
        ((tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ) + (tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ))) +
        (((tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ) + (tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ)) +
        ((tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ) + (tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ))))) +
        (((((tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ) + (tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ)) +
        ((tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ) + (tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ))) +
        (((tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ) + (tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ)) +
        ((tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ) + (tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ)))) +
        ((((tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ) + (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) +
        ((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ))) +
        (((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ)) +
        ((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ))))))) +
        ((((((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)) +
        ((tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) + (tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ))) +
        (((tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ) + (tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ)) +
        ((tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ) + (tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ)))) +
        ((((tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ) + (tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ)) +
        ((tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ) + (tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ))) +
        (((tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ) + (tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ)) +
        ((tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ) + (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ)))))
        + (((((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
        ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
        (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
        ((tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ) + (tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ)))) +
        ((((tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ) + (tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ)) +
        ((tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ) + (tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ))) +
        ((tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ) + tlTTwoP13c12 f ξ)))) := by
  linear_combination
    ((((tlTTwo_s0 hT) + (tlTTwo_s1 hT)) + ((tlTTwo_s2 hT) + (tlTTwo_s3 hT))) + (((tlTTwo_s4 hT) +
      (tlTTwo_s5 hT)) + ((tlTTwo_s6 hT) + (tlTTwo_s7 hT)))) + ((((tlTTwo_s8 hT) + (tlTTwo_s9 hT))
      + ((tlTTwo_s10 hT) + (tlTTwo_s11 hT))) + ((tlTTwo_s12 hT) + (tlTTwo_s13 hT)))


end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoXSteps0To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Second-weight identities 0 through 1

The first independent second-weight identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlWTwoX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
      tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ +
      tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + (((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ))
        + tlWTwoXP0c20 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1.1 hT


lemma tlWTwoX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ +
      tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ +
      tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
      tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ +
      tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ) + (tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ)) +
        ((tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ) + (tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ))) +
        (((tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ)) +
        ((tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ) + (tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ))))
        + (((tlWTwoXP1c16 f ξ + tlWTwoXP1c17 f ξ) + (tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ))
        + (tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1.2 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoXSteps2To4. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Second-weight identities 2 through 4

The remaining independent second-weight identities.
-/



section

namespace MazurTorsion.Kubert

lemma tlWTwoX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ +
      tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
      tlTTwoP7c12 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ +
      tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ +
      tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
      tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ +
      tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP9c14 f ξ +
      tlTTwoP9c15 f ξ + tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ) + (tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ)) +
        ((tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ) + (tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ))) +
        (((tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ) + (tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ)) +
        ((tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ) + (tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ))))
        + (((tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ) + (tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ))
        + ((tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ) + tlWTwoXP2c22 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3.1 hT


lemma tlWTwoX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ +
      tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ +
      tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP12c0 f ξ
      + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
      tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ + tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ +
      tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ + tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ + tlTTwoP13c6 f ξ +
      tlTTwoP13c7 f ξ + tlTTwoP13c8 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ) + (tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ)) +
        ((tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ) + (tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ))) +
        (((tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ) + (tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ)) +
        ((tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ) + (tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ))))
        + (((tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ) + (tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ))
        + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ)) := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3.2 hT


lemma tlWTwoX_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP13c9 f ξ + tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ + tlTTwoP13c12 f ξ) * tlMTwoV0 f =
      ((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ) := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s4 hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoX. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The second-weight value

The aggregate second-weight identity.
-/



section

namespace MazurTorsion.Kubert

lemma tlWTwoX_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((((((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) + ((tlTTwoP0c4 f
      ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) + (((tlTTwoP0c8 f ξ + tlTTwoP0c9 f
      ξ) + (tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ)) + ((tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ) + (tlTTwoP1c4 f
      ξ + tlTTwoP1c5 f ξ)))) + ((((tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ) + (tlTTwoP1c8 f ξ + tlTTwoP1c9
      f ξ)) + ((tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ) + (tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ))) +
      (((tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ) + (tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ)) + ((tlTTwoP2c5 f ξ
      + tlTTwoP2c6 f ξ) + (tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ))))) + (((((tlTTwoP2c9 f ξ +
      tlTTwoP2c10 f ξ) + (tlTTwoP2c11 f ξ + tlTTwoP2c12 f ξ)) + ((tlTTwoP2c13 f ξ + tlTTwoP2c14 f
      ξ) + (tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ))) + (((tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ) +
      (tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ)) + ((tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ) + (tlTTwoP3c7 f ξ +
      tlTTwoP3c8 f ξ)))) + ((((tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ) + (tlTTwoP3c11 f ξ + tlTTwoP4c0 f
      ξ)) + ((tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ) + (tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ))) +
      (((tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ) + (tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ)) + ((tlTTwoP4c9 f ξ
      + tlTTwoP4c10 f ξ) + (tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ)))))) + ((((((tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ) + (tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ)) + ((tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ) +
      (tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ))) + (((tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ) + (tlTTwoP5c9 f ξ
      + tlTTwoP5c10 f ξ)) + ((tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ) + (tlTTwoP5c13 f ξ + tlTTwoP6c0 f
      ξ)))) + ((((tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ) + (tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ)) +
      ((tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ) + (tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ))) + (((tlTTwoP6c9 f ξ
      + tlTTwoP7c0 f ξ) + (tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ)) + ((tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ)
      + (tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ))))) + (((((tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ) +
      (tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ)) + ((tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ) + (tlTTwoP8c0 f ξ
      + tlTTwoP8c1 f ξ))) + (((tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ) + (tlTTwoP8c4 f ξ + tlTTwoP8c5 f
      ξ)) + ((tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ) + (tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ)))) +
      ((((tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ) + (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) + ((tlTTwoP9c0
      f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ))) + (((tlTTwoP9c4 f ξ + tlTTwoP9c5
      f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ)) + ((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) +
      (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ))))))) + ((((((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) +
      (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)) + ((tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) + (tlTTwoP10c0 f
      ξ + tlTTwoP10c1 f ξ))) + (((tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ) + (tlTTwoP10c4 f ξ +
      tlTTwoP10c5 f ξ)) + ((tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ) + (tlTTwoP10c8 f ξ + tlTTwoP10c9 f
      ξ)))) + ((((tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ) + (tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ)) +
      ((tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ) + (tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ))) +
      (((tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ) + (tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ)) +
      ((tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ) + (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ))))) +
      (((((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
      ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
      (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
      ((tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ) + (tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ)))) +
      ((((tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ) + (tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ)) +
      ((tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ) + (tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ))) +
      ((tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ) + tlTTwoP13c12 f ξ))))) * tlMTwoV0 f =
      ((((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f
        ξ)) + ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f
        ξ))) + (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f
        ξ)) + ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f
        ξ))))) + (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ +
        tlWTwoXP1c14 f ξ)) + ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ +
        tlWTwoXP1c18 f ξ))) + (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ
        + tlWTwoXP2c0 f ξ)) + ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ +
        tlWTwoXP2c4 f ξ)))) + ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ +
        tlWTwoXP2c8 f ξ)) + ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ +
        tlWTwoXP2c12 f ξ))) + (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ
        + tlWTwoXP2c16 f ξ)) + ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ
        + tlWTwoXP2c20 f ξ)))))) + (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) +
        (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) + ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) +
        (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) + (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) +
        (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) + ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) +
        (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) + ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f
        ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) + ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f
        ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) + (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f
        ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) + ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) +
        tlWTwoXP4c6 f ξ)))) := by
  linear_combination
    (((tlWTwoX_s0 hT) + (tlWTwoX_s1 hT)) + ((tlWTwoX_s2 hT) + (tlWTwoX_s3 hT))) + (tlWTwoX_s4 hT)


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



lemma tl_brM2 (f : ℚ) :
    tlMTwoV0 f = -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) := by
  simp only [tlMTwoV0]
  ring1






end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumTwo. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The second kernel numerator term

The second independently elaborated numerator term.
-/



section

namespace MazurTorsion.Kubert

lemma tl_mnum₂ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2
      * (tlD0 f ξ + tlD1 f ξ) =
      ((((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ)))) +
        ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ)) +
        ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ))) +
        (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ)) +
        ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ))))) +
        (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ)) +
        ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ))) +
        (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ + tlWTwoXP2c0 f ξ)) +
        ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f ξ)))) +
        ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ)) +
        ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ))) +
        (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ)) +
        ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ)))))) +
        (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) + (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) +
        ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) + (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) +
        (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) + (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) +
        ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) + (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) +
        ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) +
        ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) +
        (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ)))) := by
  linear_combination
    -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * (tlD0 f ξ + tlD1 f ξ) * tlNSq_val hT + -(3 * f * (f
      - 1) ^ 2 * (f ^ 2 + f - 1)) * tlTTwo_val hT - ((((((((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) +
      (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) + ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ +
      tlTTwoP0c7 f ξ))) + (((tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) + (tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ))
      + ((tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ) + (tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ)))) + ((((tlTTwoP1c6
      f ξ + tlTTwoP1c7 f ξ) + (tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ)) + ((tlTTwoP1c10 f ξ + tlTTwoP1c11
      f ξ) + (tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ))) + (((tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ) +
      (tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ)) + ((tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ) + (tlTTwoP2c7 f ξ +
      tlTTwoP2c8 f ξ))))) + (((((tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ) + (tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ)) + ((tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ) + (tlTTwoP2c15 f ξ + tlTTwoP3c0 f
      ξ))) + (((tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ) + (tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ)) +
      ((tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ) + (tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ)))) + ((((tlTTwoP3c9 f
      ξ + tlTTwoP3c10 f ξ) + (tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ)) + ((tlTTwoP4c1 f ξ + tlTTwoP4c2 f
      ξ) + (tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ))) + (((tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ) + (tlTTwoP4c7
      f ξ + tlTTwoP4c8 f ξ)) + ((tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ) + (tlTTwoP4c11 f ξ +
      tlTTwoP4c12 f ξ)))))) + ((((((tlTTwoP4c13 f ξ + tlTTwoP5c0 f ξ) + (tlTTwoP5c1 f ξ +
      tlTTwoP5c2 f ξ)) + ((tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ) + (tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ)))
      + (((tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ) + (tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ)) + ((tlTTwoP5c11
      f ξ + tlTTwoP5c12 f ξ) + (tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ)))) + ((((tlTTwoP6c1 f ξ +
      tlTTwoP6c2 f ξ) + (tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ)) + ((tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ) +
      (tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ))) + (((tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ) + (tlTTwoP7c1 f ξ
      + tlTTwoP7c2 f ξ)) + ((tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ) + (tlTTwoP7c5 f ξ + tlTTwoP7c6 f
      ξ))))) + (((((tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ) + (tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ)) +
      ((tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ) + (tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ))) + (((tlTTwoP8c2 f
      ξ + tlTTwoP8c3 f ξ) + (tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ)) + ((tlTTwoP8c6 f ξ + tlTTwoP8c7 f
      ξ) + (tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ)))) + ((((tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ) +
      (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) + ((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ
      + tlTTwoP9c3 f ξ))) + (((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f
      ξ)) + ((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ))))))) +
      ((((((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)) +
      ((tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) + (tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ))) +
      (((tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ) + (tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ)) + ((tlTTwoP10c6
      f ξ + tlTTwoP10c7 f ξ) + (tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ)))) + ((((tlTTwoP10c10 f ξ +
      tlTTwoP10c11 f ξ) + (tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ)) + ((tlTTwoP11c2 f ξ + tlTTwoP11c3 f
      ξ) + (tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ))) + (((tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ) +
      (tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ)) + ((tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ) +
      (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ))))) + (((((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) +
      (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) + ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f
      ξ + tlTTwoP12c7 f ξ))) + (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ)) + ((tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ) + (tlTTwoP13c0 f ξ + tlTTwoP13c1
      f ξ)))) + ((((tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ) + (tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ)) +
      ((tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ) + (tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ))) +
      ((tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ) + tlTTwoP13c12 f ξ))))) * tl_brM2 f + tlWTwoX_val hT


end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2
      * (tlD0 f ξ + tlD1 f ξ) =
      ((((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ)))) +
        ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ)) +
        ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ))) +
        (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ)) +
        ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ))))) +
        (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ)) +
        ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ))) +
        (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ + tlWTwoXP2c0 f ξ)) +
        ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f ξ)))) +
        ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ)) +
        ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ))) +
        (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ)) +
        ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ)))))) +
        (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) + (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) +
        ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) + (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) +
        (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) + (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) +
        ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) + (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) +
        ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) +
        ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) +
        (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ)))))
 := by
  exact MazurTorsion.Kubert.tl_mnum₂

#print axioms solution

end
