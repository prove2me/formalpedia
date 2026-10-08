-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_8_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:01:25.264368+00:00
-- url     : https://prove2.me/submissions/e7221695-e586-4bfb-bbd5-1e797a254c2b

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





lemma tl_band8 (f ξ : ℚ) :
    (((((tlNCbP0c8 f ξ + tlNCbP1c8 f ξ) + (tlNCbP2c8 f ξ + tlNCbP3c8 f ξ)) + ((tlNCbP4c8 f ξ +
      tlNCbP5c8 f ξ) + (tlNCbP6c7 f ξ + tlNCbP7c6 f ξ))) + (((tlNCbP8c8 f ξ + tlNCbP9c8 f ξ) +
      (tlNCbP10c8 f ξ + tlNCbP11c8 f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP13c8 f ξ) + (tlNCbP14c7 f ξ +
      tlNCbP15c7 f ξ)))) + ((((tlNCbP16c6 f ξ + tlNCbP17c5 f ξ) + (tlNCbP18c8 f ξ + tlNCbP19c8 f
      ξ)) + ((tlNCbP20c8 f ξ + tlNCbP21c8 f ξ) + (tlNCbP22c8 f ξ + tlNCbP23c8 f ξ))) +
      (((tlNCbP24c7 f ξ + tlNCbP25c7 f ξ) + (tlNCbP26c6 f ξ + tlNCbP27c5 f ξ)) + ((tlNCbP28c4 f ξ
      + tlNCbP29c8 f ξ) + (tlNCbP30c8 f ξ + tlNCbP31c8 f ξ))))) + (((((tlNCbP32c8 f ξ + tlNCbP33c8
      f ξ) + (tlNCbP34c8 f ξ + tlNCbP35c7 f ξ)) + ((tlNCbP36c7 f ξ + tlNCbP37c6 f ξ) + (tlNCbP38c5
      f ξ + tlNCbP39c4 f ξ))) + (((tlNCbP40c3 f ξ + tlWTwoXP0c8 f ξ) + (tlWTwoXP1c8 f ξ +
      tlWTwoXP2c8 f ξ)) + ((tlWTwoXP3c8 f ξ + tlWOneXP0c8 f ξ) + (tlWOneXP1c8 f ξ + tlWOneXP2c8 f
      ξ)))) + (((tlWOneXP3c7 f ξ + tlWOneXP4c7 f ξ) + (tlWOneXP5c5 f ξ + tlWZeroXP0c8 f ξ)) +
      ((tlWZeroXP1c7 f ξ + tlWZeroXP2c5 f ξ) + tlWZeroXP3c0 f ξ))) = 0 := by
  simp only [tlNCbP0c8, tlNCbP1c8, tlNCbP2c8, tlNCbP3c8, tlNCbP4c8, tlNCbP5c8, tlNCbP6c7,
      tlNCbP7c6, tlNCbP8c8, tlNCbP9c8, tlNCbP10c8, tlNCbP11c8, tlNCbP12c8,
      tlNCbP13c8, tlNCbP14c7, tlNCbP15c7, tlNCbP16c6, tlNCbP17c5, tlNCbP18c8,
      tlNCbP19c8, tlNCbP20c8, tlNCbP21c8, tlNCbP22c8, tlNCbP23c8, tlNCbP24c7,
      tlNCbP25c7, tlNCbP26c6, tlNCbP27c5, tlNCbP28c4, tlNCbP29c8, tlNCbP30c8,
      tlNCbP31c8, tlNCbP32c8, tlNCbP33c8, tlNCbP34c8, tlNCbP35c7, tlNCbP36c7,
      tlNCbP37c6, tlNCbP38c5, tlNCbP39c4, tlNCbP40c3, tlWTwoXP0c8, tlWTwoXP1c8,
      tlWTwoXP2c8, tlWTwoXP3c8, tlWOneXP0c8, tlWOneXP1c8, tlWOneXP2c8, tlWOneXP3c7,
      tlWOneXP4c7, tlWOneXP5c5, tlWZeroXP0c8, tlWZeroXP1c7, tlWZeroXP2c5,
      tlWZeroXP3c0]
  ring1

lemma tl_band9 (f ξ : ℚ) :
    (((((tlNCbP0c9 f ξ + tlNCbP1c9 f ξ) + (tlNCbP2c9 f ξ + tlNCbP3c9 f ξ)) + ((tlNCbP4c9 f ξ +
      tlNCbP5c9 f ξ) + (tlNCbP6c8 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP9c9 f ξ) +
      (tlNCbP10c9 f ξ + tlNCbP11c9 f ξ)) + ((tlNCbP12c9 f ξ + tlNCbP13c9 f ξ) + (tlNCbP14c8 f ξ +
      tlNCbP15c8 f ξ)))) + ((((tlNCbP16c7 f ξ + tlNCbP17c6 f ξ) + (tlNCbP18c9 f ξ + tlNCbP19c9 f
      ξ)) + ((tlNCbP20c9 f ξ + tlNCbP21c9 f ξ) + (tlNCbP22c9 f ξ + tlNCbP23c9 f ξ))) +
      (((tlNCbP24c8 f ξ + tlNCbP25c8 f ξ) + (tlNCbP26c7 f ξ + tlNCbP27c6 f ξ)) + ((tlNCbP28c5 f ξ
      + tlNCbP29c9 f ξ) + (tlNCbP30c9 f ξ + tlNCbP31c9 f ξ))))) + (((((tlNCbP32c9 f ξ + tlNCbP33c9
      f ξ) + (tlNCbP34c9 f ξ + tlNCbP35c8 f ξ)) + ((tlNCbP36c8 f ξ + tlNCbP37c7 f ξ) + (tlNCbP38c6
      f ξ + tlNCbP39c5 f ξ))) + (((tlNCbP40c4 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP1c9 f ξ +
      tlWTwoXP2c9 f ξ)) + ((tlWTwoXP3c9 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP1c9 f ξ + tlWOneXP2c9 f
      ξ)))) + (((tlWOneXP3c8 f ξ + tlWOneXP4c8 f ξ) + (tlWOneXP5c6 f ξ + tlWZeroXP0c9 f ξ)) +
      ((tlWZeroXP1c8 f ξ + tlWZeroXP2c6 f ξ) + tlWZeroXP3c1 f ξ))) = 0 := by
  simp only [tlNCbP0c9, tlNCbP1c9, tlNCbP2c9, tlNCbP3c9, tlNCbP4c9, tlNCbP5c9, tlNCbP6c8,
      tlNCbP7c7, tlNCbP8c9, tlNCbP9c9, tlNCbP10c9, tlNCbP11c9, tlNCbP12c9,
      tlNCbP13c9, tlNCbP14c8, tlNCbP15c8, tlNCbP16c7, tlNCbP17c6, tlNCbP18c9,
      tlNCbP19c9, tlNCbP20c9, tlNCbP21c9, tlNCbP22c9, tlNCbP23c9, tlNCbP24c8,
      tlNCbP25c8, tlNCbP26c7, tlNCbP27c6, tlNCbP28c5, tlNCbP29c9, tlNCbP30c9,
      tlNCbP31c9, tlNCbP32c9, tlNCbP33c9, tlNCbP34c9, tlNCbP35c8, tlNCbP36c8,
      tlNCbP37c7, tlNCbP38c6, tlNCbP39c5, tlNCbP40c4, tlWTwoXP0c9, tlWTwoXP1c9,
      tlWTwoXP2c9, tlWTwoXP3c9, tlWOneXP0c9, tlWOneXP1c9, tlWOneXP2c9, tlWOneXP3c8,
      tlWOneXP4c8, tlWOneXP5c6, tlWZeroXP0c9, tlWZeroXP1c8, tlWZeroXP2c6,
      tlWZeroXP3c1]
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





























































































private lemma tl_col8 (f ξ : ℚ) :
    tlColumn f ξ 8 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band8 f ξ

private lemma tl_col9 (f ξ : ℚ) :
    tlColumn f ξ 9 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band9 f ξ


































end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
  tlColumn f ξ (8 : Fin 24) = 0 ∧
  tlColumn f ξ (9 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col8 f ξ, tl_col9 f ξ⟩

#print axioms solution
end
