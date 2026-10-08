-- Prove2me | solution 1 for MazurTransfer.order27_kernel_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:09:14.213453+00:00
-- url     : https://prove2.me/submissions/edf0b59e-ba9e-461f-9f76-d75026128e91

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_aggregate_numerator_one
import Theorems.Thm_MazurTransfer_order27_aggregate_numerator_two
import Theorems.Thm_MazurTransfer_order27_aggregate_numerator_three
import Theorems.Thm_MazurTransfer_order27_aggregate_numerator_four
import Theorems.Thm_MazurTransfer_order27_aggregate_numerator_zero

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumOne. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The first kernel numerator term

The first independently elaborated numerator term.
-/



section

namespace MazurTorsion.Kubert

lemma tl_mnum₁ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 3 =
      (((((((((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f ξ
        + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + (((tlNCbP0c8 f ξ + tlNCbP0c9 f ξ) +
        (tlNCbP0c10 f ξ + tlNCbP1c0 f ξ)) + ((tlNCbP1c1 f ξ + tlNCbP1c2 f ξ) + (tlNCbP1c3 f ξ +
        tlNCbP1c4 f ξ)))) + ((((tlNCbP1c5 f ξ + tlNCbP1c6 f ξ) + (tlNCbP1c7 f ξ + tlNCbP1c8 f ξ))
        + ((tlNCbP1c9 f ξ + tlNCbP1c10 f ξ) + (tlNCbP1c11 f ξ + tlNCbP1c12 f ξ))) + (((tlNCbP2c0 f
        ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f ξ + tlNCbP2c5 f ξ) +
        (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))))) + (((((tlNCbP2c8 f ξ + tlNCbP2c9 f ξ) + (tlNCbP2c10 f
        ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ + tlNCbP2c13 f ξ) + (tlNCbP2c14 f ξ + tlNCbP3c0 f
        ξ))) + (((tlNCbP3c1 f ξ + tlNCbP3c2 f ξ) + (tlNCbP3c3 f ξ + tlNCbP3c4 f ξ)) + ((tlNCbP3c5
        f ξ + tlNCbP3c6 f ξ) + (tlNCbP3c7 f ξ + tlNCbP3c8 f ξ)))) + ((((tlNCbP3c9 f ξ + tlNCbP3c10
        f ξ) + (tlNCbP3c11 f ξ + tlNCbP3c12 f ξ)) + ((tlNCbP3c13 f ξ + tlNCbP3c14 f ξ) +
        (tlNCbP3c15 f ξ + tlNCbP4c0 f ξ))) + (((tlNCbP4c1 f ξ + tlNCbP4c2 f ξ) + (tlNCbP4c3 f ξ +
        tlNCbP4c4 f ξ)) + ((tlNCbP4c5 f ξ + tlNCbP4c6 f ξ) + (tlNCbP4c7 f ξ + tlNCbP4c8 f ξ))))))
        + ((((((tlNCbP4c9 f ξ + tlNCbP4c10 f ξ) + (tlNCbP4c11 f ξ + tlNCbP4c12 f ξ)) +
        ((tlNCbP4c13 f ξ + tlNCbP4c14 f ξ) + (tlNCbP4c15 f ξ + tlNCbP4c16 f ξ))) + (((tlNCbP5c0 f
        ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4 f ξ + tlNCbP5c5 f ξ) +
        (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ)))) + ((((tlNCbP5c8 f ξ + tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ
        + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ + tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f
        ξ))) + (((tlNCbP5c16 f ξ + tlNCbP5c17 f ξ) + (tlNCbP6c0 f ξ + tlNCbP6c1 f ξ)) +
        ((tlNCbP6c2 f ξ + tlNCbP6c3 f ξ) + (tlNCbP6c4 f ξ + tlNCbP6c5 f ξ))))) + (((((tlNCbP6c6 f
        ξ + tlNCbP6c7 f ξ) + (tlNCbP6c8 f ξ + tlNCbP6c9 f ξ)) + ((tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)
        + (tlNCbP6c12 f ξ + tlNCbP6c13 f ξ))) + (((tlNCbP6c14 f ξ + tlNCbP6c15 f ξ) + (tlNCbP6c16
        f ξ + tlNCbP6c17 f ξ)) + ((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f
        ξ)))) + ((((tlNCbP7c4 f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ)) +
        ((tlNCbP7c8 f ξ + tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ))) + (((tlNCbP7c12 f ξ
        + tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)) + ((tlNCbP7c16 f ξ + tlNCbP7c17 f
        ξ) + (tlNCbP7c18 f ξ + tlNCbP8c0 f ξ))))))) + (((((((tlNCbP8c1 f ξ + tlNCbP8c2 f ξ) +
        (tlNCbP8c3 f ξ + tlNCbP8c4 f ξ)) + ((tlNCbP8c5 f ξ + tlNCbP8c6 f ξ) + (tlNCbP8c7 f ξ +
        tlNCbP8c8 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP8c10 f ξ) + (tlNCbP9c0 f ξ + tlNCbP9c1 f ξ)) +
        ((tlNCbP9c2 f ξ + tlNCbP9c3 f ξ) + (tlNCbP9c4 f ξ + tlNCbP9c5 f ξ)))) + ((((tlNCbP9c6 f ξ
        + tlNCbP9c7 f ξ) + (tlNCbP9c8 f ξ + tlNCbP9c9 f ξ)) + ((tlNCbP9c10 f ξ + tlNCbP9c11 f ξ) +
        (tlNCbP9c12 f ξ + tlNCbP10c0 f ξ))) + (((tlNCbP10c1 f ξ + tlNCbP10c2 f ξ) + (tlNCbP10c3 f
        ξ + tlNCbP10c4 f ξ)) + ((tlNCbP10c5 f ξ + tlNCbP10c6 f ξ) + (tlNCbP10c7 f ξ + tlNCbP10c8 f
        ξ))))) + (((((tlNCbP10c9 f ξ + tlNCbP10c10 f ξ) + (tlNCbP10c11 f ξ + tlNCbP10c12 f ξ)) +
        ((tlNCbP10c13 f ξ + tlNCbP11c0 f ξ) + (tlNCbP11c1 f ξ + tlNCbP11c2 f ξ))) + (((tlNCbP11c3
        f ξ + tlNCbP11c4 f ξ) + (tlNCbP11c5 f ξ + tlNCbP11c6 f ξ)) + ((tlNCbP11c7 f ξ + tlNCbP11c8
        f ξ) + (tlNCbP11c9 f ξ + tlNCbP11c10 f ξ)))) + ((((tlNCbP11c11 f ξ + tlNCbP11c12 f ξ) +
        (tlNCbP11c13 f ξ + tlNCbP11c14 f ξ)) + ((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f
        ξ + tlNCbP12c3 f ξ))) + (((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7
        f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)))))) +
        ((((((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ)) +
        ((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ))) + (((tlNCbP13c4 f
        ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ)) + ((tlNCbP13c8 f ξ + tlNCbP13c9 f
        ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)))) + ((((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) +
        (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)) + ((tlNCbP13c16 f ξ + tlNCbP13c17 f ξ) + (tlNCbP14c0
        f ξ + tlNCbP14c1 f ξ))) + (((tlNCbP14c2 f ξ + tlNCbP14c3 f ξ) + (tlNCbP14c4 f ξ +
        tlNCbP14c5 f ξ)) + ((tlNCbP14c6 f ξ + tlNCbP14c7 f ξ) + (tlNCbP14c8 f ξ + tlNCbP14c9 f
        ξ))))) + (((((tlNCbP14c10 f ξ + tlNCbP14c11 f ξ) + (tlNCbP14c12 f ξ + tlNCbP14c13 f ξ)) +
        ((tlNCbP14c14 f ξ + tlNCbP14c15 f ξ) + (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))) +
        (((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) + ((tlNCbP15c4 f ξ
        + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ)))) + ((((tlNCbP15c8 f ξ + tlNCbP15c9
        f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) + ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) +
        (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ))) + (((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) +
        (tlNCbP15c18 f ξ + tlNCbP16c0 f ξ)) + ((tlNCbP16c1 f ξ + tlNCbP16c2 f ξ) + (tlNCbP16c3 f ξ
        + tlNCbP16c4 f ξ)))))))) + ((((((((tlNCbP16c5 f ξ + tlNCbP16c6 f ξ) + (tlNCbP16c7 f ξ +
        tlNCbP16c8 f ξ)) + ((tlNCbP16c9 f ξ + tlNCbP16c10 f ξ) + (tlNCbP16c11 f ξ + tlNCbP16c12 f
        ξ))) + (((tlNCbP16c13 f ξ + tlNCbP16c14 f ξ) + (tlNCbP16c15 f ξ + tlNCbP16c16 f ξ)) +
        ((tlNCbP16c17 f ξ + tlNCbP16c18 f ξ) + (tlNCbP17c0 f ξ + tlNCbP17c1 f ξ)))) +
        ((((tlNCbP17c2 f ξ + tlNCbP17c3 f ξ) + (tlNCbP17c4 f ξ + tlNCbP17c5 f ξ)) + ((tlNCbP17c6 f
        ξ + tlNCbP17c7 f ξ) + (tlNCbP17c8 f ξ + tlNCbP17c9 f ξ))) + (((tlNCbP17c10 f ξ +
        tlNCbP17c11 f ξ) + (tlNCbP17c12 f ξ + tlNCbP17c13 f ξ)) + ((tlNCbP17c14 f ξ + tlNCbP17c15
        f ξ) + (tlNCbP17c16 f ξ + tlNCbP17c17 f ξ))))) + (((((tlNCbP17c18 f ξ + tlNCbP18c0 f ξ) +
        (tlNCbP18c1 f ξ + tlNCbP18c2 f ξ)) + ((tlNCbP18c3 f ξ + tlNCbP18c4 f ξ) + (tlNCbP18c5 f ξ
        + tlNCbP18c6 f ξ))) + (((tlNCbP18c7 f ξ + tlNCbP18c8 f ξ) + (tlNCbP18c9 f ξ + tlNCbP18c10
        f ξ)) + ((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)))) +
        ((((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ)) + ((tlNCbP19c8 f
        ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ))) + (((tlNCbP19c12 f ξ +
        tlNCbP20c0 f ξ) + (tlNCbP20c1 f ξ + tlNCbP20c2 f ξ)) + ((tlNCbP20c3 f ξ + tlNCbP20c4 f ξ)
        + (tlNCbP20c5 f ξ + tlNCbP20c6 f ξ)))))) + ((((((tlNCbP20c7 f ξ + tlNCbP20c8 f ξ) +
        (tlNCbP20c9 f ξ + tlNCbP20c10 f ξ)) + ((tlNCbP20c11 f ξ + tlNCbP20c12 f ξ) + (tlNCbP20c13
        f ξ + tlNCbP21c0 f ξ))) + (((tlNCbP21c1 f ξ + tlNCbP21c2 f ξ) + (tlNCbP21c3 f ξ +
        tlNCbP21c4 f ξ)) + ((tlNCbP21c5 f ξ + tlNCbP21c6 f ξ) + (tlNCbP21c7 f ξ + tlNCbP21c8 f
        ξ)))) + ((((tlNCbP21c9 f ξ + tlNCbP21c10 f ξ) + (tlNCbP21c11 f ξ + tlNCbP21c12 f ξ)) +
        ((tlNCbP21c13 f ξ + tlNCbP21c14 f ξ) + (tlNCbP22c0 f ξ + tlNCbP22c1 f ξ))) + (((tlNCbP22c2
        f ξ + tlNCbP22c3 f ξ) + (tlNCbP22c4 f ξ + tlNCbP22c5 f ξ)) + ((tlNCbP22c6 f ξ + tlNCbP22c7
        f ξ) + (tlNCbP22c8 f ξ + tlNCbP22c9 f ξ))))) + (((((tlNCbP22c10 f ξ + tlNCbP22c11 f ξ) +
        (tlNCbP22c12 f ξ + tlNCbP22c13 f ξ)) + ((tlNCbP22c14 f ξ + tlNCbP22c15 f ξ) + (tlNCbP23c0
        f ξ + tlNCbP23c1 f ξ))) + (((tlNCbP23c2 f ξ + tlNCbP23c3 f ξ) + (tlNCbP23c4 f ξ +
        tlNCbP23c5 f ξ)) + ((tlNCbP23c6 f ξ + tlNCbP23c7 f ξ) + (tlNCbP23c8 f ξ + tlNCbP23c9 f
        ξ)))) + ((((tlNCbP23c10 f ξ + tlNCbP23c11 f ξ) + (tlNCbP23c12 f ξ + tlNCbP23c13 f ξ)) +
        ((tlNCbP23c14 f ξ + tlNCbP23c15 f ξ) + (tlNCbP23c16 f ξ + tlNCbP24c0 f ξ))) +
        (((tlNCbP24c1 f ξ + tlNCbP24c2 f ξ) + (tlNCbP24c3 f ξ + tlNCbP24c4 f ξ)) + ((tlNCbP24c5 f
        ξ + tlNCbP24c6 f ξ) + (tlNCbP24c7 f ξ + tlNCbP24c8 f ξ))))))) + (((((((tlNCbP24c9 f ξ +
        tlNCbP24c10 f ξ) + (tlNCbP24c11 f ξ + tlNCbP24c12 f ξ)) + ((tlNCbP24c13 f ξ + tlNCbP24c14
        f ξ) + (tlNCbP24c15 f ξ + tlNCbP24c16 f ξ))) + (((tlNCbP24c17 f ξ + tlNCbP25c0 f) +
        (tlNCbP25c1 f ξ + tlNCbP25c2 f ξ)) + ((tlNCbP25c3 f ξ + tlNCbP25c4 f ξ) + (tlNCbP25c5 f ξ
        + tlNCbP25c6 f ξ)))) + ((((tlNCbP25c7 f ξ + tlNCbP25c8 f ξ) + (tlNCbP25c9 f ξ +
        tlNCbP25c10 f ξ)) + ((tlNCbP25c11 f ξ + tlNCbP25c12 f ξ) + (tlNCbP25c13 f ξ + tlNCbP25c14
        f ξ))) + (((tlNCbP25c15 f ξ + tlNCbP25c16 f ξ) + (tlNCbP25c17 f ξ + tlNCbP25c18 f ξ)) +
        ((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ))))) +
        (((((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ)) + ((tlNCbP26c8
        f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ))) + (((tlNCbP26c12 f ξ +
        tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)) + ((tlNCbP26c16 f ξ + tlNCbP26c17
        f ξ) + (tlNCbP26c18 f ξ + tlNCbP27c0 f ξ)))) + ((((tlNCbP27c1 f ξ + tlNCbP27c2 f ξ) +
        (tlNCbP27c3 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP27c5 f ξ + tlNCbP27c6 f ξ) + (tlNCbP27c7 f ξ
        + tlNCbP27c8 f ξ))) + (((tlNCbP27c9 f ξ + tlNCbP27c10 f ξ) + (tlNCbP27c11 f ξ +
        tlNCbP27c12 f ξ)) + ((tlNCbP27c13 f ξ + tlNCbP27c14 f ξ) + (tlNCbP27c15 f ξ + tlNCbP27c16
        f ξ)))))) + ((((((tlNCbP27c17 f ξ + tlNCbP27c18 f ξ) + (tlNCbP28c0 f ξ + tlNCbP28c1 f ξ))
        + ((tlNCbP28c2 f ξ + tlNCbP28c3 f ξ) + (tlNCbP28c4 f ξ + tlNCbP28c5 f ξ))) + (((tlNCbP28c6
        f ξ + tlNCbP28c7 f ξ) + (tlNCbP28c8 f ξ + tlNCbP28c9 f ξ)) + ((tlNCbP28c10 f ξ +
        tlNCbP28c11 f ξ) + (tlNCbP28c12 f ξ + tlNCbP28c13 f ξ)))) + ((((tlNCbP28c14 f ξ +
        tlNCbP28c15 f ξ) + (tlNCbP28c16 f ξ + tlNCbP28c17 f ξ)) + ((tlNCbP28c18 f ξ + tlNCbP29c0 f
        ξ) + (tlNCbP29c1 f ξ + tlNCbP29c2 f ξ))) + (((tlNCbP29c3 f ξ + tlNCbP29c4 f ξ) +
        (tlNCbP29c5 f ξ + tlNCbP29c6 f ξ)) + ((tlNCbP29c7 f ξ + tlNCbP29c8 f ξ) + (tlNCbP29c9 f ξ
        + tlNCbP29c10 f ξ))))) + (((((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ +
        tlNCbP30c3 f ξ)) + ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f
        ξ))) + (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        ((tlNCbP30c12 f ξ + tlNCbP31c0 f ξ) + (tlNCbP31c1 f ξ + tlNCbP31c2 f ξ)))) +
        ((((tlNCbP31c3 f ξ + tlNCbP31c4 f ξ) + (tlNCbP31c5 f ξ + tlNCbP31c6 f ξ)) + ((tlNCbP31c7 f
        ξ + tlNCbP31c8 f ξ) + (tlNCbP31c9 f ξ + tlNCbP31c10 f ξ))) + (((tlNCbP31c11 f ξ +
        tlNCbP31c12 f ξ) + (tlNCbP31c13 f ξ + tlNCbP32c0 f ξ)) + ((tlNCbP32c1 f ξ + tlNCbP32c2 f
        ξ) + (tlNCbP32c3 f ξ + tlNCbP32c4 f ξ))))))))) + ((((((((tlNCbP32c5 f ξ + tlNCbP32c6 f ξ)
        + (tlNCbP32c7 f ξ + tlNCbP32c8 f ξ)) + ((tlNCbP32c9 f ξ + tlNCbP32c10 f ξ) + (tlNCbP32c11
        f ξ + tlNCbP32c12 f ξ))) + (((tlNCbP32c13 f ξ + tlNCbP32c14 f ξ) + (tlNCbP32c15 f ξ +
        tlNCbP33c0 f ξ)) + ((tlNCbP33c1 f ξ + tlNCbP33c2 f ξ) + (tlNCbP33c3 f ξ + tlNCbP33c4 f
        ξ)))) + ((((tlNCbP33c5 f ξ + tlNCbP33c6 f ξ) + (tlNCbP33c7 f ξ + tlNCbP33c8 f ξ)) +
        ((tlNCbP33c9 f ξ + tlNCbP33c10 f ξ) + (tlNCbP33c11 f ξ + tlNCbP33c12 f ξ))) +
        (((tlNCbP33c13 f ξ + tlNCbP33c14 f ξ) + (tlNCbP33c15 f ξ + tlNCbP33c16 f ξ)) +
        ((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ))))) +
        (((((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ)) + ((tlNCbP34c8
        f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ))) + (((tlNCbP34c12 f ξ +
        tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)) + ((tlNCbP34c16 f ξ + tlNCbP34c17
        f ξ) + (tlNCbP35c0 f ξ + tlNCbP35c1 f ξ)))) + ((((tlNCbP35c2 f ξ + tlNCbP35c3 f ξ) +
        (tlNCbP35c4 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP35c6 f ξ + tlNCbP35c7 f ξ) + (tlNCbP35c8 f ξ
        + tlNCbP35c9 f ξ))) + (((tlNCbP35c10 f ξ + tlNCbP35c11 f ξ) + (tlNCbP35c12 f ξ +
        tlNCbP35c13 f ξ)) + ((tlNCbP35c14 f ξ + tlNCbP35c15 f ξ) + (tlNCbP35c16 f ξ + tlNCbP35c17
        f ξ)))))) + ((((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) + (((tlNCbP36c8 f
        ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) + ((tlNCbP36c12 f ξ +
        tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) + ((((tlNCbP36c16 f ξ +
        tlNCbP36c17 f ξ) + (tlNCbP36c18 f ξ + tlNCbP37c0 f)) + ((tlNCbP37c1 f ξ + tlNCbP37c2 f ξ)
        + (tlNCbP37c3 f ξ + tlNCbP37c4 f ξ))) + (((tlNCbP37c5 f ξ + tlNCbP37c6 f ξ) + (tlNCbP37c7
        f ξ + tlNCbP37c8 f ξ)) + ((tlNCbP37c9 f ξ + tlNCbP37c10 f ξ) + (tlNCbP37c11 f ξ +
        tlNCbP37c12 f ξ))))) + (((((tlNCbP37c13 f ξ + tlNCbP37c14 f ξ) + (tlNCbP37c15 f ξ +
        tlNCbP37c16 f ξ)) + ((tlNCbP37c17 f ξ + tlNCbP37c18 f ξ) + (tlNCbP38c0 f + tlNCbP38c1 f
        ξ))) + (((tlNCbP38c2 f ξ + tlNCbP38c3 f ξ) + (tlNCbP38c4 f ξ + tlNCbP38c5 f ξ)) +
        ((tlNCbP38c6 f ξ + tlNCbP38c7 f ξ) + (tlNCbP38c8 f ξ + tlNCbP38c9 f ξ)))) +
        ((((tlNCbP38c10 f ξ + tlNCbP38c11 f ξ) + (tlNCbP38c12 f ξ + tlNCbP38c13 f ξ)) +
        ((tlNCbP38c14 f ξ + tlNCbP38c15 f ξ) + (tlNCbP38c16 f ξ + tlNCbP38c17 f ξ))) +
        (((tlNCbP38c18 f ξ + tlNCbP39c0 f) + (tlNCbP39c1 f ξ + tlNCbP39c2 f ξ)) + ((tlNCbP39c3 f ξ
        + tlNCbP39c4 f ξ) + (tlNCbP39c5 f ξ + tlNCbP39c6 f ξ))))))) + (((((tlNCbP39c7 f ξ +
        tlNCbP39c8 f ξ) + (tlNCbP39c9 f ξ + tlNCbP39c10 f ξ)) + ((tlNCbP39c11 f ξ + tlNCbP39c12 f
        ξ) + (tlNCbP39c13 f ξ + tlNCbP39c14 f ξ))) + (((tlNCbP39c15 f ξ + tlNCbP39c16 f ξ) +
        (tlNCbP39c17 f ξ + tlNCbP39c18 f ξ)) + ((tlNCbP40c0 f + tlNCbP40c1 f ξ) + (tlNCbP40c2 f ξ
        + tlNCbP40c3 f ξ)))) + ((((tlNCbP40c4 f ξ + tlNCbP40c5 f ξ) + (tlNCbP40c6 f ξ + tlNCbP40c7
        f ξ)) + ((tlNCbP40c8 f ξ + tlNCbP40c9 f ξ) + (tlNCbP40c10 f ξ + tlNCbP40c11 f ξ))) +
        (((tlNCbP40c12 f ξ + tlNCbP40c13 f ξ) + (tlNCbP40c14 f ξ + tlNCbP40c15 f ξ)) +
        ((tlNCbP40c16 f ξ + tlNCbP40c17 f ξ) + tlNCbP40c18 f ξ))))) := by
  exact MazurTransfer.order27_aggregate_numerator_one hT



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
  exact MazurTransfer.order27_aggregate_numerator_two hT



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
  exact MazurTransfer.order27_aggregate_numerator_three hT



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
  exact MazurTransfer.order27_aggregate_numerator_four hT



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Zero. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The aggregate zero identity

The band identities assembled into the aggregate zero relation.
-/



section

namespace MazurTorsion.Kubert































































































































lemma tl_zero (f ξ : ℚ) :
    ((((((((((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f ξ
      + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + (((tlNCbP0c8 f ξ + tlNCbP0c9 f ξ) +
      (tlNCbP0c10 f ξ + tlNCbP1c0 f ξ)) + ((tlNCbP1c1 f ξ + tlNCbP1c2 f ξ) + (tlNCbP1c3 f ξ +
      tlNCbP1c4 f ξ)))) + ((((tlNCbP1c5 f ξ + tlNCbP1c6 f ξ) + (tlNCbP1c7 f ξ + tlNCbP1c8 f ξ)) +
      ((tlNCbP1c9 f ξ + tlNCbP1c10 f ξ) + (tlNCbP1c11 f ξ + tlNCbP1c12 f ξ))) + (((tlNCbP2c0 f ξ +
      tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f ξ + tlNCbP2c5 f ξ) +
      (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))))) + (((((tlNCbP2c8 f ξ + tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ
      + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ + tlNCbP2c13 f ξ) + (tlNCbP2c14 f ξ + tlNCbP3c0 f ξ)))
      + (((tlNCbP3c1 f ξ + tlNCbP3c2 f ξ) + (tlNCbP3c3 f ξ + tlNCbP3c4 f ξ)) + ((tlNCbP3c5 f ξ +
      tlNCbP3c6 f ξ) + (tlNCbP3c7 f ξ + tlNCbP3c8 f ξ)))) + ((((tlNCbP3c9 f ξ + tlNCbP3c10 f ξ) +
      (tlNCbP3c11 f ξ + tlNCbP3c12 f ξ)) + ((tlNCbP3c13 f ξ + tlNCbP3c14 f ξ) + (tlNCbP3c15 f ξ +
      tlNCbP4c0 f ξ))) + (((tlNCbP4c1 f ξ + tlNCbP4c2 f ξ) + (tlNCbP4c3 f ξ + tlNCbP4c4 f ξ)) +
      ((tlNCbP4c5 f ξ + tlNCbP4c6 f ξ) + (tlNCbP4c7 f ξ + tlNCbP4c8 f ξ)))))) + ((((((tlNCbP4c9 f
      ξ + tlNCbP4c10 f ξ) + (tlNCbP4c11 f ξ + tlNCbP4c12 f ξ)) + ((tlNCbP4c13 f ξ + tlNCbP4c14 f
      ξ) + (tlNCbP4c15 f ξ + tlNCbP4c16 f ξ))) + (((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f
      ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4 f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))))
      + ((((tlNCbP5c8 f ξ + tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ
      + tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ))) + (((tlNCbP5c16 f ξ + tlNCbP5c17 f
      ξ) + (tlNCbP6c0 f ξ + tlNCbP6c1 f ξ)) + ((tlNCbP6c2 f ξ + tlNCbP6c3 f ξ) + (tlNCbP6c4 f ξ +
      tlNCbP6c5 f ξ))))) + (((((tlNCbP6c6 f ξ + tlNCbP6c7 f ξ) + (tlNCbP6c8 f ξ + tlNCbP6c9 f ξ))
      + ((tlNCbP6c10 f ξ + tlNCbP6c11 f ξ) + (tlNCbP6c12 f ξ + tlNCbP6c13 f ξ))) + (((tlNCbP6c14 f
      ξ + tlNCbP6c15 f ξ) + (tlNCbP6c16 f ξ + tlNCbP6c17 f ξ)) + ((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ)
      + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)))) + ((((tlNCbP7c4 f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ +
      tlNCbP7c7 f ξ)) + ((tlNCbP7c8 f ξ + tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ))) +
      (((tlNCbP7c12 f ξ + tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)) + ((tlNCbP7c16 f ξ
      + tlNCbP7c17 f ξ) + (tlNCbP7c18 f ξ + tlNCbP8c0 f ξ))))))) + (((((((tlNCbP8c1 f ξ +
      tlNCbP8c2 f ξ) + (tlNCbP8c3 f ξ + tlNCbP8c4 f ξ)) + ((tlNCbP8c5 f ξ + tlNCbP8c6 f ξ) +
      (tlNCbP8c7 f ξ + tlNCbP8c8 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP8c10 f ξ) + (tlNCbP9c0 f ξ +
      tlNCbP9c1 f ξ)) + ((tlNCbP9c2 f ξ + tlNCbP9c3 f ξ) + (tlNCbP9c4 f ξ + tlNCbP9c5 f ξ)))) +
      ((((tlNCbP9c6 f ξ + tlNCbP9c7 f ξ) + (tlNCbP9c8 f ξ + tlNCbP9c9 f ξ)) + ((tlNCbP9c10 f ξ +
      tlNCbP9c11 f ξ) + (tlNCbP9c12 f ξ + tlNCbP10c0 f ξ))) + (((tlNCbP10c1 f ξ + tlNCbP10c2 f ξ)
      + (tlNCbP10c3 f ξ + tlNCbP10c4 f ξ)) + ((tlNCbP10c5 f ξ + tlNCbP10c6 f ξ) + (tlNCbP10c7 f ξ
      + tlNCbP10c8 f ξ))))) + (((((tlNCbP10c9 f ξ + tlNCbP10c10 f ξ) + (tlNCbP10c11 f ξ +
      tlNCbP10c12 f ξ)) + ((tlNCbP10c13 f ξ + tlNCbP11c0 f ξ) + (tlNCbP11c1 f ξ + tlNCbP11c2 f
      ξ))) + (((tlNCbP11c3 f ξ + tlNCbP11c4 f ξ) + (tlNCbP11c5 f ξ + tlNCbP11c6 f ξ)) +
      ((tlNCbP11c7 f ξ + tlNCbP11c8 f ξ) + (tlNCbP11c9 f ξ + tlNCbP11c10 f ξ)))) + ((((tlNCbP11c11
      f ξ + tlNCbP11c12 f ξ) + (tlNCbP11c13 f ξ + tlNCbP11c14 f ξ)) + ((tlNCbP12c0 f ξ +
      tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ))) + (((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ)
      + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ
      + tlNCbP12c11 f ξ)))))) + ((((((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ +
      tlNCbP12c15 f ξ)) + ((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ)))
      + (((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ)) + ((tlNCbP13c8 f
      ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)))) + ((((tlNCbP13c12 f ξ +
      tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)) + ((tlNCbP13c16 f ξ + tlNCbP13c17 f
      ξ) + (tlNCbP14c0 f ξ + tlNCbP14c1 f ξ))) + (((tlNCbP14c2 f ξ + tlNCbP14c3 f ξ) + (tlNCbP14c4
      f ξ + tlNCbP14c5 f ξ)) + ((tlNCbP14c6 f ξ + tlNCbP14c7 f ξ) + (tlNCbP14c8 f ξ + tlNCbP14c9 f
      ξ))))) + (((((tlNCbP14c10 f ξ + tlNCbP14c11 f ξ) + (tlNCbP14c12 f ξ + tlNCbP14c13 f ξ)) +
      ((tlNCbP14c14 f ξ + tlNCbP14c15 f ξ) + (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))) + (((tlNCbP15c0
      f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) + ((tlNCbP15c4 f ξ + tlNCbP15c5 f
      ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ)))) + ((((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) +
      (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) + ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f
      ξ + tlNCbP15c15 f ξ))) + (((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + (tlNCbP15c18 f ξ +
      tlNCbP16c0 f ξ)) + ((tlNCbP16c1 f ξ + tlNCbP16c2 f ξ) + (tlNCbP16c3 f ξ + tlNCbP16c4 f
      ξ)))))))) + ((((((((tlNCbP16c5 f ξ + tlNCbP16c6 f ξ) + (tlNCbP16c7 f ξ + tlNCbP16c8 f ξ)) +
      ((tlNCbP16c9 f ξ + tlNCbP16c10 f ξ) + (tlNCbP16c11 f ξ + tlNCbP16c12 f ξ))) + (((tlNCbP16c13
      f ξ + tlNCbP16c14 f ξ) + (tlNCbP16c15 f ξ + tlNCbP16c16 f ξ)) + ((tlNCbP16c17 f ξ +
      tlNCbP16c18 f ξ) + (tlNCbP17c0 f ξ + tlNCbP17c1 f ξ)))) + ((((tlNCbP17c2 f ξ + tlNCbP17c3 f
      ξ) + (tlNCbP17c4 f ξ + tlNCbP17c5 f ξ)) + ((tlNCbP17c6 f ξ + tlNCbP17c7 f ξ) + (tlNCbP17c8 f
      ξ + tlNCbP17c9 f ξ))) + (((tlNCbP17c10 f ξ + tlNCbP17c11 f ξ) + (tlNCbP17c12 f ξ +
      tlNCbP17c13 f ξ)) + ((tlNCbP17c14 f ξ + tlNCbP17c15 f ξ) + (tlNCbP17c16 f ξ + tlNCbP17c17 f
      ξ))))) + (((((tlNCbP17c18 f ξ + tlNCbP18c0 f ξ) + (tlNCbP18c1 f ξ + tlNCbP18c2 f ξ)) +
      ((tlNCbP18c3 f ξ + tlNCbP18c4 f ξ) + (tlNCbP18c5 f ξ + tlNCbP18c6 f ξ))) + (((tlNCbP18c7 f ξ
      + tlNCbP18c8 f ξ) + (tlNCbP18c9 f ξ + tlNCbP18c10 f ξ)) + ((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ)
      + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)))) + ((((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6
      f ξ + tlNCbP19c7 f ξ)) + ((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11
      f ξ))) + (((tlNCbP19c12 f ξ + tlNCbP20c0 f ξ) + (tlNCbP20c1 f ξ + tlNCbP20c2 f ξ)) +
      ((tlNCbP20c3 f ξ + tlNCbP20c4 f ξ) + (tlNCbP20c5 f ξ + tlNCbP20c6 f ξ)))))) +
      ((((((tlNCbP20c7 f ξ + tlNCbP20c8 f ξ) + (tlNCbP20c9 f ξ + tlNCbP20c10 f ξ)) + ((tlNCbP20c11
      f ξ + tlNCbP20c12 f ξ) + (tlNCbP20c13 f ξ + tlNCbP21c0 f ξ))) + (((tlNCbP21c1 f ξ +
      tlNCbP21c2 f ξ) + (tlNCbP21c3 f ξ + tlNCbP21c4 f ξ)) + ((tlNCbP21c5 f ξ + tlNCbP21c6 f ξ) +
      (tlNCbP21c7 f ξ + tlNCbP21c8 f ξ)))) + ((((tlNCbP21c9 f ξ + tlNCbP21c10 f ξ) + (tlNCbP21c11
      f ξ + tlNCbP21c12 f ξ)) + ((tlNCbP21c13 f ξ + tlNCbP21c14 f ξ) + (tlNCbP22c0 f ξ +
      tlNCbP22c1 f ξ))) + (((tlNCbP22c2 f ξ + tlNCbP22c3 f ξ) + (tlNCbP22c4 f ξ + tlNCbP22c5 f ξ))
      + ((tlNCbP22c6 f ξ + tlNCbP22c7 f ξ) + (tlNCbP22c8 f ξ + tlNCbP22c9 f ξ))))) +
      (((((tlNCbP22c10 f ξ + tlNCbP22c11 f ξ) + (tlNCbP22c12 f ξ + tlNCbP22c13 f ξ)) +
      ((tlNCbP22c14 f ξ + tlNCbP22c15 f ξ) + (tlNCbP23c0 f ξ + tlNCbP23c1 f ξ))) + (((tlNCbP23c2 f
      ξ + tlNCbP23c3 f ξ) + (tlNCbP23c4 f ξ + tlNCbP23c5 f ξ)) + ((tlNCbP23c6 f ξ + tlNCbP23c7 f
      ξ) + (tlNCbP23c8 f ξ + tlNCbP23c9 f ξ)))) + ((((tlNCbP23c10 f ξ + tlNCbP23c11 f ξ) +
      (tlNCbP23c12 f ξ + tlNCbP23c13 f ξ)) + ((tlNCbP23c14 f ξ + tlNCbP23c15 f ξ) + (tlNCbP23c16 f
      ξ + tlNCbP24c0 f ξ))) + (((tlNCbP24c1 f ξ + tlNCbP24c2 f ξ) + (tlNCbP24c3 f ξ + tlNCbP24c4 f
      ξ)) + ((tlNCbP24c5 f ξ + tlNCbP24c6 f ξ) + (tlNCbP24c7 f ξ + tlNCbP24c8 f ξ))))))) +
      (((((((tlNCbP24c9 f ξ + tlNCbP24c10 f ξ) + (tlNCbP24c11 f ξ + tlNCbP24c12 f ξ)) +
      ((tlNCbP24c13 f ξ + tlNCbP24c14 f ξ) + (tlNCbP24c15 f ξ + tlNCbP24c16 f ξ))) +
      (((tlNCbP24c17 f ξ + tlNCbP25c0 f) + (tlNCbP25c1 f ξ + tlNCbP25c2 f ξ)) + ((tlNCbP25c3 f ξ +
      tlNCbP25c4 f ξ) + (tlNCbP25c5 f ξ + tlNCbP25c6 f ξ)))) + ((((tlNCbP25c7 f ξ + tlNCbP25c8 f
      ξ) + (tlNCbP25c9 f ξ + tlNCbP25c10 f ξ)) + ((tlNCbP25c11 f ξ + tlNCbP25c12 f ξ) +
      (tlNCbP25c13 f ξ + tlNCbP25c14 f ξ))) + (((tlNCbP25c15 f ξ + tlNCbP25c16 f ξ) + (tlNCbP25c17
      f ξ + tlNCbP25c18 f ξ)) + ((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3
      f ξ))))) + (((((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ)) +
      ((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ))) + (((tlNCbP26c12
      f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)) + ((tlNCbP26c16 f ξ +
      tlNCbP26c17 f ξ) + (tlNCbP26c18 f ξ + tlNCbP27c0 f ξ)))) + ((((tlNCbP27c1 f ξ + tlNCbP27c2 f
      ξ) + (tlNCbP27c3 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP27c5 f ξ + tlNCbP27c6 f ξ) + (tlNCbP27c7 f
      ξ + tlNCbP27c8 f ξ))) + (((tlNCbP27c9 f ξ + tlNCbP27c10 f ξ) + (tlNCbP27c11 f ξ +
      tlNCbP27c12 f ξ)) + ((tlNCbP27c13 f ξ + tlNCbP27c14 f ξ) + (tlNCbP27c15 f ξ + tlNCbP27c16 f
      ξ)))))) + ((((((tlNCbP27c17 f ξ + tlNCbP27c18 f ξ) + (tlNCbP28c0 f ξ + tlNCbP28c1 f ξ)) +
      ((tlNCbP28c2 f ξ + tlNCbP28c3 f ξ) + (tlNCbP28c4 f ξ + tlNCbP28c5 f ξ))) + (((tlNCbP28c6 f ξ
      + tlNCbP28c7 f ξ) + (tlNCbP28c8 f ξ + tlNCbP28c9 f ξ)) + ((tlNCbP28c10 f ξ + tlNCbP28c11 f
      ξ) + (tlNCbP28c12 f ξ + tlNCbP28c13 f ξ)))) + ((((tlNCbP28c14 f ξ + tlNCbP28c15 f ξ) +
      (tlNCbP28c16 f ξ + tlNCbP28c17 f ξ)) + ((tlNCbP28c18 f ξ + tlNCbP29c0 f ξ) + (tlNCbP29c1 f ξ
      + tlNCbP29c2 f ξ))) + (((tlNCbP29c3 f ξ + tlNCbP29c4 f ξ) + (tlNCbP29c5 f ξ + tlNCbP29c6 f
      ξ)) + ((tlNCbP29c7 f ξ + tlNCbP29c8 f ξ) + (tlNCbP29c9 f ξ + tlNCbP29c10 f ξ))))) +
      (((((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) + ((tlNCbP30c4 f
      ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) + (((tlNCbP30c8 f ξ + tlNCbP30c9 f
      ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) + ((tlNCbP30c12 f ξ + tlNCbP31c0 f ξ) +
      (tlNCbP31c1 f ξ + tlNCbP31c2 f ξ)))) + ((((tlNCbP31c3 f ξ + tlNCbP31c4 f ξ) + (tlNCbP31c5 f
      ξ + tlNCbP31c6 f ξ)) + ((tlNCbP31c7 f ξ + tlNCbP31c8 f ξ) + (tlNCbP31c9 f ξ + tlNCbP31c10 f
      ξ))) + (((tlNCbP31c11 f ξ + tlNCbP31c12 f ξ) + (tlNCbP31c13 f ξ + tlNCbP32c0 f ξ)) +
      ((tlNCbP32c1 f ξ + tlNCbP32c2 f ξ) + (tlNCbP32c3 f ξ + tlNCbP32c4 f ξ))))))))) +
      ((((((((tlNCbP32c5 f ξ + tlNCbP32c6 f ξ) + (tlNCbP32c7 f ξ + tlNCbP32c8 f ξ)) + ((tlNCbP32c9
      f ξ + tlNCbP32c10 f ξ) + (tlNCbP32c11 f ξ + tlNCbP32c12 f ξ))) + (((tlNCbP32c13 f ξ +
      tlNCbP32c14 f ξ) + (tlNCbP32c15 f ξ + tlNCbP33c0 f ξ)) + ((tlNCbP33c1 f ξ + tlNCbP33c2 f ξ)
      + (tlNCbP33c3 f ξ + tlNCbP33c4 f ξ)))) + ((((tlNCbP33c5 f ξ + tlNCbP33c6 f ξ) + (tlNCbP33c7
      f ξ + tlNCbP33c8 f ξ)) + ((tlNCbP33c9 f ξ + tlNCbP33c10 f ξ) + (tlNCbP33c11 f ξ +
      tlNCbP33c12 f ξ))) + (((tlNCbP33c13 f ξ + tlNCbP33c14 f ξ) + (tlNCbP33c15 f ξ + tlNCbP33c16
      f ξ)) + ((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ))))) +
      (((((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ)) + ((tlNCbP34c8 f
      ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ))) + (((tlNCbP34c12 f ξ +
      tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)) + ((tlNCbP34c16 f ξ + tlNCbP34c17 f
      ξ) + (tlNCbP35c0 f ξ + tlNCbP35c1 f ξ)))) + ((((tlNCbP35c2 f ξ + tlNCbP35c3 f ξ) +
      (tlNCbP35c4 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP35c6 f ξ + tlNCbP35c7 f ξ) + (tlNCbP35c8 f ξ +
      tlNCbP35c9 f ξ))) + (((tlNCbP35c10 f ξ + tlNCbP35c11 f ξ) + (tlNCbP35c12 f ξ + tlNCbP35c13 f
      ξ)) + ((tlNCbP35c14 f ξ + tlNCbP35c15 f ξ) + (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ)))))) +
      ((((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) + ((tlNCbP36c4 f ξ
      + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) + (((tlNCbP36c8 f ξ + tlNCbP36c9 f
      ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) + ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) +
      (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) + ((((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) +
      (tlNCbP36c18 f ξ + tlNCbP37c0 f)) + ((tlNCbP37c1 f ξ + tlNCbP37c2 f ξ) + (tlNCbP37c3 f ξ +
      tlNCbP37c4 f ξ))) + (((tlNCbP37c5 f ξ + tlNCbP37c6 f ξ) + (tlNCbP37c7 f ξ + tlNCbP37c8 f ξ))
      + ((tlNCbP37c9 f ξ + tlNCbP37c10 f ξ) + (tlNCbP37c11 f ξ + tlNCbP37c12 f ξ))))) +
      (((((tlNCbP37c13 f ξ + tlNCbP37c14 f ξ) + (tlNCbP37c15 f ξ + tlNCbP37c16 f ξ)) +
      ((tlNCbP37c17 f ξ + tlNCbP37c18 f ξ) + (tlNCbP38c0 f + tlNCbP38c1 f ξ))) + (((tlNCbP38c2 f ξ
      + tlNCbP38c3 f ξ) + (tlNCbP38c4 f ξ + tlNCbP38c5 f ξ)) + ((tlNCbP38c6 f ξ + tlNCbP38c7 f ξ)
      + (tlNCbP38c8 f ξ + tlNCbP38c9 f ξ)))) + ((((tlNCbP38c10 f ξ + tlNCbP38c11 f ξ) +
      (tlNCbP38c12 f ξ + tlNCbP38c13 f ξ)) + ((tlNCbP38c14 f ξ + tlNCbP38c15 f ξ) + (tlNCbP38c16 f
      ξ + tlNCbP38c17 f ξ))) + (((tlNCbP38c18 f ξ + tlNCbP39c0 f) + (tlNCbP39c1 f ξ + tlNCbP39c2 f
      ξ)) + ((tlNCbP39c3 f ξ + tlNCbP39c4 f ξ) + (tlNCbP39c5 f ξ + tlNCbP39c6 f ξ))))))) +
      (((((tlNCbP39c7 f ξ + tlNCbP39c8 f ξ) + (tlNCbP39c9 f ξ + tlNCbP39c10 f ξ)) + ((tlNCbP39c11
      f ξ + tlNCbP39c12 f ξ) + (tlNCbP39c13 f ξ + tlNCbP39c14 f ξ))) + (((tlNCbP39c15 f ξ +
      tlNCbP39c16 f ξ) + (tlNCbP39c17 f ξ + tlNCbP39c18 f ξ)) + ((tlNCbP40c0 f + tlNCbP40c1 f ξ) +
      (tlNCbP40c2 f ξ + tlNCbP40c3 f ξ)))) + ((((tlNCbP40c4 f ξ + tlNCbP40c5 f ξ) + (tlNCbP40c6 f
      ξ + tlNCbP40c7 f ξ)) + ((tlNCbP40c8 f ξ + tlNCbP40c9 f ξ) + (tlNCbP40c10 f ξ + tlNCbP40c11 f
      ξ))) + (((tlNCbP40c12 f ξ + tlNCbP40c13 f ξ) + (tlNCbP40c14 f ξ + tlNCbP40c15 f ξ)) +
      ((tlNCbP40c16 f ξ + tlNCbP40c17 f ξ) + tlNCbP40c18 f ξ)))))) + (((((((tlWTwoXP0c0 f ξ +
      tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) + ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f
      ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) + (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) +
      (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) + ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) +
      (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ)))) + ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) +
      (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ)) + ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) +
      (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ))) + (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5
      f ξ + tlWTwoXP1c6 f ξ)) + ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ +
      tlWTwoXP1c10 f ξ))))) + (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ +
      tlWTwoXP1c14 f ξ)) + ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ +
      tlWTwoXP1c18 f ξ))) + (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ +
      tlWTwoXP2c0 f ξ)) + ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f
      ξ)))) + ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ)) +
      ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ))) +
      (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ)) +
      ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ)))))) +
      (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) + (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) +
      ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) + (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) +
      (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) + (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) +
      ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) + (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) +
      ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) +
      ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) +
      (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) + ((tlWTwoXP4c4
      f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ))))) + (((((((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) +
      (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) + ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f
      ξ + tlWOneXP0c7 f ξ))) + (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ +
      tlWOneXP0c11 f ξ)) + ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP0c14 f ξ +
      tlWOneXP1c0 f ξ)))) + ((((tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ) + (tlWOneXP1c3 f ξ +
      tlWOneXP1c4 f ξ)) + ((tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP1c8 f
      ξ))) + (((tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ)) +
      ((tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ) + (tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ))))) +
      (((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
      ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
      (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
      ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ)))) +
      ((((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + (tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ)) +
      ((tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ))) +
      (((tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ) + (tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ)) + ((tlWOneXP3c9
      f ξ + tlWOneXP3c10 f ξ) + (tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ)))))) + ((((((tlWOneXP3c13 f
      ξ + tlWOneXP3c14 f ξ) + (tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ)) + ((tlWOneXP3c17 f ξ +
      tlWOneXP3c18 f ξ) + (tlWOneXP3c19 f ξ + tlWOneXP4c0 f))) + (((tlWOneXP4c1 f ξ + tlWOneXP4c2
      f ξ) + (tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ)) + ((tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ) +
      (tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ)))) + ((((tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ) +
      (tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ)) + ((tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ) +
      (tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ))) + (((tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ) +
      (tlWOneXP4c19 f ξ + tlWOneXP4c20 f ξ)) + ((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2
      f ξ + tlWOneXP5c3 f ξ))))) + (((((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ +
      tlWOneXP5c7 f ξ)) + ((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11
      f ξ))) + (((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ)) +
      ((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ)))) +
      tlWOneXP5c20 f ξ))) + (((((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ +
      tlWZeroXP0c3 f ξ)) + ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ +
      tlWZeroXP0c7 f ξ))) + (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ +
      tlWZeroXP0c11 f ξ)) + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ +
      tlWZeroXP0c15 f ξ)))) + ((((tlWZeroXP0c16 f ξ + tlWZeroXP1c0 f ξ) + (tlWZeroXP1c1 f ξ +
      tlWZeroXP1c2 f ξ)) + ((tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ) + (tlWZeroXP1c5 f ξ +
      tlWZeroXP1c6 f ξ))) + (((tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ) + (tlWZeroXP1c9 f ξ +
      tlWZeroXP1c10 f ξ)) + ((tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ) + (tlWZeroXP1c13 f ξ +
      tlWZeroXP1c14 f ξ))))) + (((((tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ) + (tlWZeroXP1c17 f ξ +
      tlWZeroXP1c18 f ξ)) + ((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ +
      tlWZeroXP2c3 f ξ))) + (((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ +
      tlWZeroXP2c7 f ξ)) + ((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ +
      tlWZeroXP2c11 f ξ)))) + ((((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ +
      tlWZeroXP2c15 f ξ)) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
      tlWZeroXP2c19 f ξ))) + (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ +
      tlWZeroXP3c3 f ξ)) + ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ +
      tlWZeroXP3c7 f ξ)))))) + (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ +
      tlWZeroXP3c11 f ξ)) + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ +
      tlWZeroXP3c15 f ξ)))) = 0 := by
  exact MazurTransfer.order27_aggregate_numerator_zero f ξ



end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNum. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The combined kernel numerator

The four numerator terms combined using the aggregate zero identity.
-/



section

namespace MazurTorsion.Kubert

lemma tl_mnum {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 3 + -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1))
      * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2 * (tlD0 f ξ + tlD1 f ξ) + -(3 * f * (f
      - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 - 145 * f ^
      3 + 76 * f ^ 2 - 26 * f + 3)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) * (tlD0 f ξ
      + tlD1 f ξ) ^ 2 + -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105
      * f ^ 11 + 4341 * f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312
      * f ^ 5 + 2713 * f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * (tlD0 f ξ + tlD1 f ξ) ^
      3 = 0 := by
  rw [tl_mnum₁ hT, tl_mnum₂ hT, tl_mnum₃ hT, tl_mnum₄ hT]
  exact tl_zero f ξ


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
  have h := tl_mnum hT
  generalize hN : ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) = N at h ⊢
  generalize hDen : (tlD0 f ξ + tlD1 f ξ) = D at h ⊢ hD
  simp only [kernelCubicM]
  field_simp [hD]
  linear_combination h



end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0)
    (hD : tlD0 f ξ + tlD1 f ξ ≠ 0) :
    kernelCubicM f (((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) / (tlD0 f ξ + tlD1 f ξ)) = 0
       := by
  exact MazurTorsion.Kubert.kernel_cubic_at hT hD

#print axioms solution

end
