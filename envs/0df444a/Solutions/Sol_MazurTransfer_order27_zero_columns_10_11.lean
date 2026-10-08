-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_10_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:04:51.058648+00:00
-- url     : https://prove2.me/submissions/df29ae93-d590-4173-96d9-80696044885f

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









lemma tl_band10 (f ξ : ℚ) :
    (((((tlNCbP0c10 f ξ + tlNCbP1c10 f ξ) + (tlNCbP2c10 f ξ + tlNCbP3c10 f ξ)) + ((tlNCbP4c10 f ξ
      + tlNCbP5c10 f ξ) + (tlNCbP6c9 f ξ + tlNCbP7c8 f ξ))) + (((tlNCbP8c10 f ξ + tlNCbP9c10 f ξ)
      + (tlNCbP10c10 f ξ + tlNCbP11c10 f ξ)) + ((tlNCbP12c10 f ξ + tlNCbP13c10 f ξ) + (tlNCbP14c9
      f ξ + tlNCbP15c9 f ξ)))) + ((((tlNCbP16c8 f ξ + tlNCbP17c7 f ξ) + (tlNCbP18c10 f ξ +
      tlNCbP19c10 f ξ)) + ((tlNCbP20c10 f ξ + tlNCbP21c10 f ξ) + (tlNCbP22c10 f ξ + tlNCbP23c10 f
      ξ))) + (((tlNCbP24c9 f ξ + tlNCbP25c9 f ξ) + (tlNCbP26c8 f ξ + tlNCbP27c7 f ξ)) +
      ((tlNCbP28c6 f ξ + tlNCbP29c10 f ξ) + (tlNCbP30c10 f ξ + tlNCbP31c10 f ξ))))) +
      (((((tlNCbP32c10 f ξ + tlNCbP33c10 f ξ) + (tlNCbP34c10 f ξ + tlNCbP35c9 f ξ)) + ((tlNCbP36c9
      f ξ + tlNCbP37c8 f ξ) + (tlNCbP38c7 f ξ + tlNCbP39c6 f ξ))) + (((tlNCbP40c5 f ξ +
      tlWTwoXP0c10 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP2c10 f ξ)) + ((tlWTwoXP3c10 f ξ +
      tlWOneXP0c10 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP2c10 f ξ)))) + (((tlWOneXP3c9 f ξ +
      tlWOneXP4c9 f ξ) + (tlWOneXP5c7 f ξ + tlWZeroXP0c10 f ξ)) + ((tlWZeroXP1c9 f ξ +
      tlWZeroXP2c7 f ξ) + tlWZeroXP3c2 f ξ))) = 0 := by
  simp only [tlNCbP0c10, tlNCbP1c10, tlNCbP2c10, tlNCbP3c10, tlNCbP4c10, tlNCbP5c10,
      tlNCbP6c9, tlNCbP7c8, tlNCbP8c10, tlNCbP9c10, tlNCbP10c10, tlNCbP11c10,
      tlNCbP12c10, tlNCbP13c10, tlNCbP14c9, tlNCbP15c9, tlNCbP16c8, tlNCbP17c7,
      tlNCbP18c10, tlNCbP19c10, tlNCbP20c10, tlNCbP21c10, tlNCbP22c10, tlNCbP23c10,
      tlNCbP24c9, tlNCbP25c9, tlNCbP26c8, tlNCbP27c7, tlNCbP28c6, tlNCbP29c10,
      tlNCbP30c10, tlNCbP31c10, tlNCbP32c10, tlNCbP33c10, tlNCbP34c10, tlNCbP35c9,
      tlNCbP36c9, tlNCbP37c8, tlNCbP38c7, tlNCbP39c6, tlNCbP40c5, tlWTwoXP0c10,
      tlWTwoXP1c10, tlWTwoXP2c10, tlWTwoXP3c10, tlWOneXP0c10, tlWOneXP1c10,
      tlWOneXP2c10, tlWOneXP3c9, tlWOneXP4c9, tlWOneXP5c7, tlWZeroXP0c10,
      tlWZeroXP1c9, tlWZeroXP2c7, tlWZeroXP3c2]
  ring1

lemma tl_band11 (f ξ : ℚ) :
    (((((tlNCbP1c11 f ξ + tlNCbP2c11 f ξ) + (tlNCbP3c11 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP5c11 f ξ
      + tlNCbP6c10 f ξ) + (tlNCbP7c9 f ξ + tlNCbP9c11 f ξ))) + (((tlNCbP10c11 f ξ + tlNCbP11c11 f
      ξ) + (tlNCbP12c11 f ξ + tlNCbP13c11 f ξ)) + ((tlNCbP14c10 f ξ + tlNCbP15c10 f ξ) +
      (tlNCbP16c9 f ξ + tlNCbP17c8 f ξ)))) + ((((tlNCbP19c11 f ξ + tlNCbP20c11 f ξ) + (tlNCbP21c11
      f ξ + tlNCbP22c11 f ξ)) + ((tlNCbP23c11 f ξ + tlNCbP24c10 f ξ) + (tlNCbP25c10 f ξ +
      tlNCbP26c9 f ξ))) + (((tlNCbP27c8 f ξ + tlNCbP28c7 f ξ) + (tlNCbP30c11 f ξ + tlNCbP31c11 f
      ξ)) + ((tlNCbP32c11 f ξ + tlNCbP33c11 f ξ) + (tlNCbP34c11 f ξ + tlNCbP35c10 f ξ))))) +
      (((((tlNCbP36c10 f ξ + tlNCbP37c9 f ξ) + (tlNCbP38c8 f ξ + tlNCbP39c7 f ξ)) + ((tlNCbP40c6 f
      ξ + tlWTwoXP0c11 f ξ) + (tlWTwoXP1c11 f ξ + tlWTwoXP2c11 f ξ))) + (((tlWTwoXP3c11 f ξ +
      tlWOneXP0c11 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP2c11 f ξ)) + ((tlWOneXP3c10 f ξ +
      tlWOneXP4c10 f ξ) + (tlWOneXP5c8 f ξ + tlWZeroXP0c11 f ξ)))) + ((tlWZeroXP1c10 f ξ +
      tlWZeroXP2c8 f ξ) + tlWZeroXP3c3 f ξ)) = 0 := by
  simp only [tlNCbP1c11, tlNCbP2c11, tlNCbP3c11, tlNCbP4c11, tlNCbP5c11, tlNCbP6c10,
      tlNCbP7c9, tlNCbP9c11, tlNCbP10c11, tlNCbP11c11, tlNCbP12c11, tlNCbP13c11,
      tlNCbP14c10, tlNCbP15c10, tlNCbP16c9, tlNCbP17c8, tlNCbP19c11, tlNCbP20c11,
      tlNCbP21c11, tlNCbP22c11, tlNCbP23c11, tlNCbP24c10, tlNCbP25c10, tlNCbP26c9,
      tlNCbP27c8, tlNCbP28c7, tlNCbP30c11, tlNCbP31c11, tlNCbP32c11, tlNCbP33c11,
      tlNCbP34c11, tlNCbP35c10, tlNCbP36c10, tlNCbP37c9, tlNCbP38c8, tlNCbP39c7,
      tlNCbP40c6, tlWTwoXP0c11, tlWTwoXP1c11, tlWTwoXP2c11, tlWTwoXP3c11,
      tlWOneXP0c11, tlWOneXP1c11, tlWOneXP2c11, tlWOneXP3c10, tlWOneXP4c10,
      tlWOneXP5c8, tlWZeroXP0c11, tlWZeroXP1c10, tlWZeroXP2c8, tlWZeroXP3c3]
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

































































































private lemma tl_col10 (f ξ : ℚ) :
    tlColumn f ξ 10 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band10 f ξ

private lemma tl_col11 (f ξ : ℚ) :
    tlColumn f ξ 11 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band11 f ξ






























end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
  tlColumn f ξ (10 : Fin 24) = 0 ∧
  tlColumn f ξ (11 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col10 f ξ, tl_col11 f ξ⟩

#print axioms solution
end
