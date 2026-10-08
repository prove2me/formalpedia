-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_0_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:24:06.692262+00:00
-- url     : https://prove2.me/submissions/569f3eb2-31a9-4e7a-9b35-aff5eb711053

import Definitions.Def_MazurTransfer_Order27ZeroRowData

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Band identities 0 through 5

The first independent band identities for the trisection certificate.
-/



section

namespace MazurTorsion.Kubert

lemma tl_band0 (f ξ : ℚ) :
    ((((tlNCbP0c0 f ξ + tlNCbP1c0 f ξ) + (tlNCbP2c0 f ξ + tlNCbP3c0 f ξ)) + ((tlNCbP4c0 f ξ +
      tlNCbP5c0 f ξ) + (tlNCbP8c0 f ξ + tlNCbP9c0 f ξ))) + (((tlNCbP10c0 f ξ + tlNCbP11c0 f ξ) +
      (tlNCbP12c0 f ξ + tlNCbP13c0 f ξ)) + ((tlNCbP18c0 f ξ + tlNCbP19c0 f ξ) + (tlNCbP20c0 f ξ +
      tlNCbP21c0 f ξ)))) + ((((tlNCbP22c0 f ξ + tlNCbP23c0 f ξ) + (tlNCbP29c0 f ξ + tlNCbP30c0 f
      ξ)) + ((tlNCbP31c0 f ξ + tlNCbP32c0 f ξ) + (tlNCbP33c0 f ξ + tlNCbP34c0 f ξ))) +
      (((tlWTwoXP0c0 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP2c0 f ξ + tlWTwoXP3c0 f ξ)) + ((tlWOneXP0c0
      f ξ + tlWOneXP1c0 f ξ) + (tlWOneXP2c0 f ξ + tlWZeroXP0c0 f ξ)))) = 0 := by
  simp only [tlNCbP0c0, tlNCbP1c0, tlNCbP2c0, tlNCbP3c0, tlNCbP4c0, tlNCbP5c0, tlNCbP8c0,
      tlNCbP9c0, tlNCbP10c0, tlNCbP11c0, tlNCbP12c0, tlNCbP13c0, tlNCbP18c0,
      tlNCbP19c0, tlNCbP20c0, tlNCbP21c0, tlNCbP22c0, tlNCbP23c0, tlNCbP29c0,
      tlNCbP30c0, tlNCbP31c0, tlNCbP32c0, tlNCbP33c0, tlNCbP34c0, tlWTwoXP0c0,
      tlWTwoXP1c0, tlWTwoXP2c0, tlWTwoXP3c0, tlWOneXP0c0, tlWOneXP1c0, tlWOneXP2c0,
      tlWZeroXP0c0]
  ring1

lemma tl_band1 (f ξ : ℚ) :
    (((((tlNCbP0c1 f ξ + tlNCbP1c1 f ξ) + (tlNCbP2c1 f ξ + tlNCbP3c1 f ξ)) + ((tlNCbP4c1 f ξ +
      tlNCbP5c1 f ξ) + (tlNCbP6c0 f ξ + tlNCbP8c1 f ξ))) + (((tlNCbP9c1 f ξ + tlNCbP10c1 f ξ) +
      (tlNCbP11c1 f ξ + tlNCbP12c1 f ξ)) + ((tlNCbP13c1 f ξ + tlNCbP14c0 f ξ) + (tlNCbP15c0 f +
      tlNCbP18c1 f ξ)))) + ((((tlNCbP19c1 f ξ + tlNCbP20c1 f ξ) + (tlNCbP21c1 f ξ + tlNCbP22c1 f
      ξ)) + ((tlNCbP23c1 f ξ + tlNCbP24c0 f ξ) + (tlNCbP25c0 f + tlNCbP29c1 f ξ))) + (((tlNCbP30c1
      f ξ + tlNCbP31c1 f ξ) + (tlNCbP32c1 f ξ + tlNCbP33c1 f ξ)) + ((tlNCbP34c1 f ξ + tlNCbP35c0 f
      ξ) + (tlNCbP36c0 f + tlWTwoXP0c1 f ξ))))) + ((((tlWTwoXP1c1 f ξ + tlWTwoXP2c1 f ξ) +
      (tlWTwoXP3c1 f ξ + tlWOneXP0c1 f ξ)) + ((tlWOneXP1c1 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP3c0 f
      ξ + tlWOneXP4c0 f))) + (tlWZeroXP0c1 f ξ + tlWZeroXP1c0 f ξ)) = 0 := by
  simp only [tlNCbP0c1, tlNCbP1c1, tlNCbP2c1, tlNCbP3c1, tlNCbP4c1, tlNCbP5c1, tlNCbP6c0,
      tlNCbP8c1, tlNCbP9c1, tlNCbP10c1, tlNCbP11c1, tlNCbP12c1, tlNCbP13c1,
      tlNCbP14c0, tlNCbP15c0, tlNCbP18c1, tlNCbP19c1, tlNCbP20c1, tlNCbP21c1,
      tlNCbP22c1, tlNCbP23c1, tlNCbP24c0, tlNCbP25c0, tlNCbP29c1, tlNCbP30c1,
      tlNCbP31c1, tlNCbP32c1, tlNCbP33c1, tlNCbP34c1, tlNCbP35c0, tlNCbP36c0,
      tlWTwoXP0c1, tlWTwoXP1c1, tlWTwoXP2c1, tlWTwoXP3c1, tlWOneXP0c1, tlWOneXP1c1,
      tlWOneXP2c1, tlWOneXP3c0, tlWOneXP4c0, tlWZeroXP0c1, tlWZeroXP1c0]
  ring1

lemma tl_band2 (f ξ : ℚ) :
    (((((tlNCbP0c2 f ξ + tlNCbP1c2 f ξ) + (tlNCbP2c2 f ξ + tlNCbP3c2 f ξ)) + ((tlNCbP4c2 f ξ +
      tlNCbP5c2 f ξ) + (tlNCbP6c1 f ξ + tlNCbP7c0 f ξ))) + (((tlNCbP8c2 f ξ + tlNCbP9c2 f ξ) +
      (tlNCbP10c2 f ξ + tlNCbP11c2 f ξ)) + ((tlNCbP12c2 f ξ + tlNCbP13c2 f ξ) + (tlNCbP14c1 f ξ +
      tlNCbP15c1 f ξ)))) + ((((tlNCbP16c0 f ξ + tlNCbP18c2 f ξ) + (tlNCbP19c2 f ξ + tlNCbP20c2 f
      ξ)) + ((tlNCbP21c2 f ξ + tlNCbP22c2 f ξ) + (tlNCbP23c2 f ξ + tlNCbP24c1 f ξ))) +
      (((tlNCbP25c1 f ξ + tlNCbP26c0 f ξ) + (tlNCbP29c2 f ξ + tlNCbP30c2 f ξ)) + ((tlNCbP31c2 f ξ
      + tlNCbP32c2 f ξ) + (tlNCbP33c2 f ξ + tlNCbP34c2 f ξ))))) + ((((tlNCbP35c1 f ξ + tlNCbP36c1
      f ξ) + (tlNCbP37c0 f + tlWTwoXP0c2 f ξ)) + ((tlWTwoXP1c2 f ξ + tlWTwoXP2c2 f ξ) +
      (tlWTwoXP3c2 f ξ + tlWOneXP0c2 f ξ))) + (((tlWOneXP1c2 f ξ + tlWOneXP2c2 f ξ) + (tlWOneXP3c1
      f ξ + tlWOneXP4c1 f ξ)) + (tlWZeroXP0c2 f ξ + tlWZeroXP1c1 f ξ))) = 0 := by
  simp only [tlNCbP0c2, tlNCbP1c2, tlNCbP2c2, tlNCbP3c2, tlNCbP4c2, tlNCbP5c2, tlNCbP6c1,
      tlNCbP7c0, tlNCbP8c2, tlNCbP9c2, tlNCbP10c2, tlNCbP11c2, tlNCbP12c2,
      tlNCbP13c2, tlNCbP14c1, tlNCbP15c1, tlNCbP16c0, tlNCbP18c2, tlNCbP19c2,
      tlNCbP20c2, tlNCbP21c2, tlNCbP22c2, tlNCbP23c2, tlNCbP24c1, tlNCbP25c1,
      tlNCbP26c0, tlNCbP29c2, tlNCbP30c2, tlNCbP31c2, tlNCbP32c2, tlNCbP33c2,
      tlNCbP34c2, tlNCbP35c1, tlNCbP36c1, tlNCbP37c0, tlWTwoXP0c2, tlWTwoXP1c2,
      tlWTwoXP2c2, tlWTwoXP3c2, tlWOneXP0c2, tlWOneXP1c2, tlWOneXP2c2, tlWOneXP3c1,
      tlWOneXP4c1, tlWZeroXP0c2, tlWZeroXP1c1]
  ring1

lemma tl_band3 (f ξ : ℚ) :
    (((((tlNCbP0c3 f ξ + tlNCbP1c3 f ξ) + (tlNCbP2c3 f ξ + tlNCbP3c3 f ξ)) + ((tlNCbP4c3 f ξ +
      tlNCbP5c3 f ξ) + (tlNCbP6c2 f ξ + tlNCbP7c1 f ξ))) + (((tlNCbP8c3 f ξ + tlNCbP9c3 f ξ) +
      (tlNCbP10c3 f ξ + tlNCbP11c3 f ξ)) + ((tlNCbP12c3 f ξ + tlNCbP13c3 f ξ) + (tlNCbP14c2 f ξ +
      tlNCbP15c2 f ξ)))) + ((((tlNCbP16c1 f ξ + tlNCbP17c0 f ξ) + (tlNCbP18c3 f ξ + tlNCbP19c3 f
      ξ)) + ((tlNCbP20c3 f ξ + tlNCbP21c3 f ξ) + (tlNCbP22c3 f ξ + tlNCbP23c3 f ξ))) +
      (((tlNCbP24c2 f ξ + tlNCbP25c2 f ξ) + (tlNCbP26c1 f ξ + tlNCbP27c0 f ξ)) + ((tlNCbP29c3 f ξ
      + tlNCbP30c3 f ξ) + (tlNCbP31c3 f ξ + tlNCbP32c3 f ξ))))) + (((((tlNCbP33c3 f ξ + tlNCbP34c3
      f ξ) + (tlNCbP35c2 f ξ + tlNCbP36c2 f ξ)) + ((tlNCbP37c1 f ξ + tlNCbP38c0 f) + (tlWTwoXP0c3
      f ξ + tlWTwoXP1c3 f ξ))) + (((tlWTwoXP2c3 f ξ + tlWTwoXP3c3 f ξ) + (tlWOneXP0c3 f ξ +
      tlWOneXP1c3 f ξ)) + ((tlWOneXP2c3 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP5c0 f
      ξ)))) + ((tlWZeroXP0c3 f ξ + tlWZeroXP1c2 f ξ) + tlWZeroXP2c0 f ξ)) = 0 := by
  simp only [tlNCbP0c3, tlNCbP1c3, tlNCbP2c3, tlNCbP3c3, tlNCbP4c3, tlNCbP5c3, tlNCbP6c2,
      tlNCbP7c1, tlNCbP8c3, tlNCbP9c3, tlNCbP10c3, tlNCbP11c3, tlNCbP12c3,
      tlNCbP13c3, tlNCbP14c2, tlNCbP15c2, tlNCbP16c1, tlNCbP17c0, tlNCbP18c3,
      tlNCbP19c3, tlNCbP20c3, tlNCbP21c3, tlNCbP22c3, tlNCbP23c3, tlNCbP24c2,
      tlNCbP25c2, tlNCbP26c1, tlNCbP27c0, tlNCbP29c3, tlNCbP30c3, tlNCbP31c3,
      tlNCbP32c3, tlNCbP33c3, tlNCbP34c3, tlNCbP35c2, tlNCbP36c2, tlNCbP37c1,
      tlNCbP38c0, tlWTwoXP0c3, tlWTwoXP1c3, tlWTwoXP2c3, tlWTwoXP3c3, tlWOneXP0c3,
      tlWOneXP1c3, tlWOneXP2c3, tlWOneXP3c2, tlWOneXP4c2, tlWOneXP5c0, tlWZeroXP0c3,
      tlWZeroXP1c2, tlWZeroXP2c0]
  ring1

lemma tl_band4 (f ξ : ℚ) :
    (((((tlNCbP0c4 f ξ + tlNCbP1c4 f ξ) + (tlNCbP2c4 f ξ + tlNCbP3c4 f ξ)) + ((tlNCbP4c4 f ξ +
      tlNCbP5c4 f ξ) + (tlNCbP6c3 f ξ + tlNCbP7c2 f ξ))) + (((tlNCbP8c4 f ξ + tlNCbP9c4 f ξ) +
      (tlNCbP10c4 f ξ + tlNCbP11c4 f ξ)) + ((tlNCbP12c4 f ξ + tlNCbP13c4 f ξ) + (tlNCbP14c3 f ξ +
      tlNCbP15c3 f ξ)))) + ((((tlNCbP16c2 f ξ + tlNCbP17c1 f ξ) + (tlNCbP18c4 f ξ + tlNCbP19c4 f
      ξ)) + ((tlNCbP20c4 f ξ + tlNCbP21c4 f ξ) + (tlNCbP22c4 f ξ + tlNCbP23c4 f ξ))) +
      (((tlNCbP24c3 f ξ + tlNCbP25c3 f ξ) + (tlNCbP26c2 f ξ + tlNCbP27c1 f ξ)) + ((tlNCbP28c0 f ξ
      + tlNCbP29c4 f ξ) + (tlNCbP30c4 f ξ + tlNCbP31c4 f ξ))))) + (((((tlNCbP32c4 f ξ + tlNCbP33c4
      f ξ) + (tlNCbP34c4 f ξ + tlNCbP35c3 f ξ)) + ((tlNCbP36c3 f ξ + tlNCbP37c2 f ξ) + (tlNCbP38c1
      f ξ + tlNCbP39c0 f))) + (((tlWTwoXP0c4 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP2c4 f ξ +
      tlWTwoXP3c4 f ξ)) + ((tlWOneXP0c4 f ξ + tlWOneXP1c4 f ξ) + (tlWOneXP2c4 f ξ + tlWOneXP3c3 f
      ξ)))) + (((tlWOneXP4c3 f ξ + tlWOneXP5c1 f ξ) + (tlWZeroXP0c4 f ξ + tlWZeroXP1c3 f ξ)) +
      tlWZeroXP2c1 f ξ)) = 0 := by
  simp only [tlNCbP0c4, tlNCbP1c4, tlNCbP2c4, tlNCbP3c4, tlNCbP4c4, tlNCbP5c4, tlNCbP6c3,
      tlNCbP7c2, tlNCbP8c4, tlNCbP9c4, tlNCbP10c4, tlNCbP11c4, tlNCbP12c4,
      tlNCbP13c4, tlNCbP14c3, tlNCbP15c3, tlNCbP16c2, tlNCbP17c1, tlNCbP18c4,
      tlNCbP19c4, tlNCbP20c4, tlNCbP21c4, tlNCbP22c4, tlNCbP23c4, tlNCbP24c3,
      tlNCbP25c3, tlNCbP26c2, tlNCbP27c1, tlNCbP28c0, tlNCbP29c4, tlNCbP30c4,
      tlNCbP31c4, tlNCbP32c4, tlNCbP33c4, tlNCbP34c4, tlNCbP35c3, tlNCbP36c3,
      tlNCbP37c2, tlNCbP38c1, tlNCbP39c0, tlWTwoXP0c4, tlWTwoXP1c4, tlWTwoXP2c4,
      tlWTwoXP3c4, tlWOneXP0c4, tlWOneXP1c4, tlWOneXP2c4, tlWOneXP3c3, tlWOneXP4c3,
      tlWOneXP5c1, tlWZeroXP0c4, tlWZeroXP1c3, tlWZeroXP2c1]
  ring1

lemma tl_band5 (f ξ : ℚ) :
    (((((tlNCbP0c5 f ξ + tlNCbP1c5 f ξ) + (tlNCbP2c5 f ξ + tlNCbP3c5 f ξ)) + ((tlNCbP4c5 f ξ +
      tlNCbP5c5 f ξ) + (tlNCbP6c4 f ξ + tlNCbP7c3 f ξ))) + (((tlNCbP8c5 f ξ + tlNCbP9c5 f ξ) +
      (tlNCbP10c5 f ξ + tlNCbP11c5 f ξ)) + ((tlNCbP12c5 f ξ + tlNCbP13c5 f ξ) + (tlNCbP14c4 f ξ +
      tlNCbP15c4 f ξ)))) + ((((tlNCbP16c3 f ξ + tlNCbP17c2 f ξ) + (tlNCbP18c5 f ξ + tlNCbP19c5 f
      ξ)) + ((tlNCbP20c5 f ξ + tlNCbP21c5 f ξ) + (tlNCbP22c5 f ξ + tlNCbP23c5 f ξ))) +
      (((tlNCbP24c4 f ξ + tlNCbP25c4 f ξ) + (tlNCbP26c3 f ξ + tlNCbP27c2 f ξ)) + ((tlNCbP28c1 f ξ
      + tlNCbP29c5 f ξ) + (tlNCbP30c5 f ξ + tlNCbP31c5 f ξ))))) + (((((tlNCbP32c5 f ξ + tlNCbP33c5
      f ξ) + (tlNCbP34c5 f ξ + tlNCbP35c4 f ξ)) + ((tlNCbP36c4 f ξ + tlNCbP37c3 f ξ) + (tlNCbP38c2
      f ξ + tlNCbP39c1 f ξ))) + (((tlNCbP40c0 f + tlWTwoXP0c5 f ξ) + (tlWTwoXP1c5 f ξ +
      tlWTwoXP2c5 f ξ)) + ((tlWTwoXP3c5 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP1c5 f ξ + tlWOneXP2c5 f
      ξ)))) + (((tlWOneXP3c4 f ξ + tlWOneXP4c4 f ξ) + (tlWOneXP5c2 f ξ + tlWZeroXP0c5 f ξ)) +
      (tlWZeroXP1c4 f ξ + tlWZeroXP2c2 f ξ))) = 0 := by
  simp only [tlNCbP0c5, tlNCbP1c5, tlNCbP2c5, tlNCbP3c5, tlNCbP4c5, tlNCbP5c5, tlNCbP6c4,
      tlNCbP7c3, tlNCbP8c5, tlNCbP9c5, tlNCbP10c5, tlNCbP11c5, tlNCbP12c5,
      tlNCbP13c5, tlNCbP14c4, tlNCbP15c4, tlNCbP16c3, tlNCbP17c2, tlNCbP18c5,
      tlNCbP19c5, tlNCbP20c5, tlNCbP21c5, tlNCbP22c5, tlNCbP23c5, tlNCbP24c4,
      tlNCbP25c4, tlNCbP26c3, tlNCbP27c2, tlNCbP28c1, tlNCbP29c5, tlNCbP30c5,
      tlNCbP31c5, tlNCbP32c5, tlNCbP33c5, tlNCbP34c5, tlNCbP35c4, tlNCbP36c4,
      tlNCbP37c3, tlNCbP38c2, tlNCbP39c1, tlNCbP40c0, tlWTwoXP0c5, tlWTwoXP1c5,
      tlWTwoXP2c5, tlWTwoXP3c5, tlWOneXP0c5, tlWOneXP1c5, tlWOneXP2c5, tlWOneXP3c4,
      tlWOneXP4c4, tlWOneXP5c2, tlWZeroXP0c5, tlWZeroXP1c4, tlWZeroXP2c2]
  ring1


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













































































private lemma tl_col0 (f ξ : ℚ) :
    tlColumn f ξ 0 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band0 f ξ

private lemma tl_col1 (f ξ : ℚ) :
    tlColumn f ξ 1 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band1 f ξ

private lemma tl_col2 (f ξ : ℚ) :
    tlColumn f ξ 2 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band2 f ξ

private lemma tl_col3 (f ξ : ℚ) :
    tlColumn f ξ 3 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band3 f ξ

private lemma tl_col4 (f ξ : ℚ) :
    tlColumn f ξ 4 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band4 f ξ

private lemma tl_col5 (f ξ : ℚ) :
    tlColumn f ξ 5 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band5 f ξ










































end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
tlColumn f ξ (0 : Fin 24) = 0 ∧
tlColumn f ξ (1 : Fin 24) = 0 ∧
tlColumn f ξ (2 : Fin 24) = 0 ∧
tlColumn f ξ (3 : Fin 24) = 0 ∧
tlColumn f ξ (4 : Fin 24) = 0 ∧
tlColumn f ξ (5 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col0 f ξ, ⟨tl_col1 f ξ, ⟨tl_col2 f ξ, ⟨tl_col3 f ξ, ⟨tl_col4 f ξ, tl_col5 f ξ⟩⟩⟩⟩⟩

#print axioms solution

end
