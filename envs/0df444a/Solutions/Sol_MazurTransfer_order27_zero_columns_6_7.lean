-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_6_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:54:57.089975+00:00
-- url     : https://prove2.me/submissions/e5158b80-ac11-42ad-9b8e-75b6894510c0

import Definitions.Def_MazurTransfer_Order27ZeroRowData

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Band identities 6 through 11

The second independent band identities for the trisection certificate.
-/



section

namespace MazurTorsion.Kubert

lemma tl_band6 (f ξ : ℚ) :
    (((((tlNCbP0c6 f ξ + tlNCbP1c6 f ξ) + (tlNCbP2c6 f ξ + tlNCbP3c6 f ξ)) + ((tlNCbP4c6 f ξ +
      tlNCbP5c6 f ξ) + (tlNCbP6c5 f ξ + tlNCbP7c4 f ξ))) + (((tlNCbP8c6 f ξ + tlNCbP9c6 f ξ) +
      (tlNCbP10c6 f ξ + tlNCbP11c6 f ξ)) + ((tlNCbP12c6 f ξ + tlNCbP13c6 f ξ) + (tlNCbP14c5 f ξ +
      tlNCbP15c5 f ξ)))) + ((((tlNCbP16c4 f ξ + tlNCbP17c3 f ξ) + (tlNCbP18c6 f ξ + tlNCbP19c6 f
      ξ)) + ((tlNCbP20c6 f ξ + tlNCbP21c6 f ξ) + (tlNCbP22c6 f ξ + tlNCbP23c6 f ξ))) +
      (((tlNCbP24c5 f ξ + tlNCbP25c5 f ξ) + (tlNCbP26c4 f ξ + tlNCbP27c3 f ξ)) + ((tlNCbP28c2 f ξ
      + tlNCbP29c6 f ξ) + (tlNCbP30c6 f ξ + tlNCbP31c6 f ξ))))) + (((((tlNCbP32c6 f ξ + tlNCbP33c6
      f ξ) + (tlNCbP34c6 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP36c5 f ξ + tlNCbP37c4 f ξ) + (tlNCbP38c3
      f ξ + tlNCbP39c2 f ξ))) + (((tlNCbP40c1 f ξ + tlWTwoXP0c6 f ξ) + (tlWTwoXP1c6 f ξ +
      tlWTwoXP2c6 f ξ)) + ((tlWTwoXP3c6 f ξ + tlWOneXP0c6 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP2c6 f
      ξ)))) + (((tlWOneXP3c5 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP5c3 f ξ + tlWZeroXP0c6 f ξ)) +
      (tlWZeroXP1c5 f ξ + tlWZeroXP2c3 f ξ))) = 0 := by
  simp only [tlNCbP0c6, tlNCbP1c6, tlNCbP2c6, tlNCbP3c6, tlNCbP4c6, tlNCbP5c6, tlNCbP6c5,
      tlNCbP7c4, tlNCbP8c6, tlNCbP9c6, tlNCbP10c6, tlNCbP11c6, tlNCbP12c6,
      tlNCbP13c6, tlNCbP14c5, tlNCbP15c5, tlNCbP16c4, tlNCbP17c3, tlNCbP18c6,
      tlNCbP19c6, tlNCbP20c6, tlNCbP21c6, tlNCbP22c6, tlNCbP23c6, tlNCbP24c5,
      tlNCbP25c5, tlNCbP26c4, tlNCbP27c3, tlNCbP28c2, tlNCbP29c6, tlNCbP30c6,
      tlNCbP31c6, tlNCbP32c6, tlNCbP33c6, tlNCbP34c6, tlNCbP35c5, tlNCbP36c5,
      tlNCbP37c4, tlNCbP38c3, tlNCbP39c2, tlNCbP40c1, tlWTwoXP0c6, tlWTwoXP1c6,
      tlWTwoXP2c6, tlWTwoXP3c6, tlWOneXP0c6, tlWOneXP1c6, tlWOneXP2c6, tlWOneXP3c5,
      tlWOneXP4c5, tlWOneXP5c3, tlWZeroXP0c6, tlWZeroXP1c5, tlWZeroXP2c3]
  ring1

lemma tl_band7 (f ξ : ℚ) :
    (((((tlNCbP0c7 f ξ + tlNCbP1c7 f ξ) + (tlNCbP2c7 f ξ + tlNCbP3c7 f ξ)) + ((tlNCbP4c7 f ξ +
      tlNCbP5c7 f ξ) + (tlNCbP6c6 f ξ + tlNCbP7c5 f ξ))) + (((tlNCbP8c7 f ξ + tlNCbP9c7 f ξ) +
      (tlNCbP10c7 f ξ + tlNCbP11c7 f ξ)) + ((tlNCbP12c7 f ξ + tlNCbP13c7 f ξ) + (tlNCbP14c6 f ξ +
      tlNCbP15c6 f ξ)))) + ((((tlNCbP16c5 f ξ + tlNCbP17c4 f ξ) + (tlNCbP18c7 f ξ + tlNCbP19c7 f
      ξ)) + ((tlNCbP20c7 f ξ + tlNCbP21c7 f ξ) + (tlNCbP22c7 f ξ + tlNCbP23c7 f ξ))) +
      (((tlNCbP24c6 f ξ + tlNCbP25c6 f ξ) + (tlNCbP26c5 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP28c3 f ξ
      + tlNCbP29c7 f ξ) + (tlNCbP30c7 f ξ + tlNCbP31c7 f ξ))))) + (((((tlNCbP32c7 f ξ + tlNCbP33c7
      f ξ) + (tlNCbP34c7 f ξ + tlNCbP35c6 f ξ)) + ((tlNCbP36c6 f ξ + tlNCbP37c5 f ξ) + (tlNCbP38c4
      f ξ + tlNCbP39c3 f ξ))) + (((tlNCbP40c2 f ξ + tlWTwoXP0c7 f ξ) + (tlWTwoXP1c7 f ξ +
      tlWTwoXP2c7 f ξ)) + ((tlWTwoXP3c7 f ξ + tlWOneXP0c7 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP2c7 f
      ξ)))) + (((tlWOneXP3c6 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP5c4 f ξ + tlWZeroXP0c7 f ξ)) +
      (tlWZeroXP1c6 f ξ + tlWZeroXP2c4 f ξ))) = 0 := by
  simp only [tlNCbP0c7, tlNCbP1c7, tlNCbP2c7, tlNCbP3c7, tlNCbP4c7, tlNCbP5c7, tlNCbP6c6,
      tlNCbP7c5, tlNCbP8c7, tlNCbP9c7, tlNCbP10c7, tlNCbP11c7, tlNCbP12c7,
      tlNCbP13c7, tlNCbP14c6, tlNCbP15c6, tlNCbP16c5, tlNCbP17c4, tlNCbP18c7,
      tlNCbP19c7, tlNCbP20c7, tlNCbP21c7, tlNCbP22c7, tlNCbP23c7, tlNCbP24c6,
      tlNCbP25c6, tlNCbP26c5, tlNCbP27c4, tlNCbP28c3, tlNCbP29c7, tlNCbP30c7,
      tlNCbP31c7, tlNCbP32c7, tlNCbP33c7, tlNCbP34c7, tlNCbP35c6, tlNCbP36c6,
      tlNCbP37c5, tlNCbP38c4, tlNCbP39c3, tlNCbP40c2, tlWTwoXP0c7, tlWTwoXP1c7,
      tlWTwoXP2c7, tlWTwoXP3c7, tlWOneXP0c7, tlWOneXP1c7, tlWOneXP2c7, tlWOneXP3c6,
      tlWOneXP4c6, tlWOneXP5c4, tlWZeroXP0c7, tlWZeroXP1c6, tlWZeroXP2c4]
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

























































































private lemma tl_col6 (f ξ : ℚ) :
    tlColumn f ξ 6 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band6 f ξ

private lemma tl_col7 (f ξ : ℚ) :
    tlColumn f ξ 7 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band7 f ξ






































end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
  tlColumn f ξ (6 : Fin 24) = 0 ∧
  tlColumn f ξ (7 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col6 f ξ, tl_col7 f ξ⟩

#print axioms solution
end
