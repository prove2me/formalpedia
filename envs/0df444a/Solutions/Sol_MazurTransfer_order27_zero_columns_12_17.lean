-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_12_17
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:09:17.33968+00:00
-- url     : https://prove2.me/submissions/037c38a0-5d91-43c9-b649-deb216d7399b

import Definitions.Def_MazurTransfer_Order27ZeroRowData

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Band identities 12 through 17

The third independent band identities for the trisection certificate.
-/



section

namespace MazurTorsion.Kubert

lemma tl_band12 (f ξ : ℚ) :
    (((((tlNCbP1c12 f ξ + tlNCbP2c12 f ξ) + (tlNCbP3c12 f ξ + tlNCbP4c12 f ξ)) + ((tlNCbP5c12 f ξ
      + tlNCbP6c11 f ξ) + (tlNCbP7c10 f ξ + tlNCbP9c12 f ξ))) + (((tlNCbP10c12 f ξ + tlNCbP11c12 f
      ξ) + (tlNCbP12c12 f ξ + tlNCbP13c12 f ξ)) + ((tlNCbP14c11 f ξ + tlNCbP15c11 f ξ) +
      (tlNCbP16c10 f ξ + tlNCbP17c9 f ξ)))) + ((((tlNCbP19c12 f ξ + tlNCbP20c12 f ξ) +
      (tlNCbP21c12 f ξ + tlNCbP22c12 f ξ)) + ((tlNCbP23c12 f ξ + tlNCbP24c11 f ξ) + (tlNCbP25c11 f
      ξ + tlNCbP26c10 f ξ))) + (((tlNCbP27c9 f ξ + tlNCbP28c8 f ξ) + (tlNCbP30c12 f ξ +
      tlNCbP31c12 f ξ)) + ((tlNCbP32c12 f ξ + tlNCbP33c12 f ξ) + (tlNCbP34c12 f ξ + tlNCbP35c11 f
      ξ))))) + (((((tlNCbP36c11 f ξ + tlNCbP37c10 f ξ) + (tlNCbP38c9 f ξ + tlNCbP39c8 f ξ)) +
      ((tlNCbP40c7 f ξ + tlWTwoXP0c12 f ξ) + (tlWTwoXP1c12 f ξ + tlWTwoXP2c12 f ξ))) +
      (((tlWTwoXP3c12 f ξ + tlWOneXP0c12 f ξ) + (tlWOneXP1c12 f ξ + tlWOneXP2c12 f ξ)) +
      ((tlWOneXP3c11 f ξ + tlWOneXP4c11 f ξ) + (tlWOneXP5c9 f ξ + tlWZeroXP0c12 f ξ)))) +
      ((tlWZeroXP1c11 f ξ + tlWZeroXP2c9 f ξ) + tlWZeroXP3c4 f ξ)) = 0 := by
  simp only [tlNCbP1c12, tlNCbP2c12, tlNCbP3c12, tlNCbP4c12, tlNCbP5c12, tlNCbP6c11,
      tlNCbP7c10, tlNCbP9c12, tlNCbP10c12, tlNCbP11c12, tlNCbP12c12, tlNCbP13c12,
      tlNCbP14c11, tlNCbP15c11, tlNCbP16c10, tlNCbP17c9, tlNCbP19c12, tlNCbP20c12,
      tlNCbP21c12, tlNCbP22c12, tlNCbP23c12, tlNCbP24c11, tlNCbP25c11, tlNCbP26c10,
      tlNCbP27c9, tlNCbP28c8, tlNCbP30c12, tlNCbP31c12, tlNCbP32c12, tlNCbP33c12,
      tlNCbP34c12, tlNCbP35c11, tlNCbP36c11, tlNCbP37c10, tlNCbP38c9, tlNCbP39c8,
      tlNCbP40c7, tlWTwoXP0c12, tlWTwoXP1c12, tlWTwoXP2c12, tlWTwoXP3c12,
      tlWOneXP0c12, tlWOneXP1c12, tlWOneXP2c12, tlWOneXP3c11, tlWOneXP4c11,
      tlWOneXP5c9, tlWZeroXP0c12, tlWZeroXP1c11, tlWZeroXP2c9, tlWZeroXP3c4]
  ring1

lemma tl_band13 (f ξ : ℚ) :
    (((((tlNCbP2c13 f ξ + tlNCbP3c13 f ξ) + (tlNCbP4c13 f ξ + tlNCbP5c13 f ξ)) + ((tlNCbP6c12 f ξ
      + tlNCbP7c11 f ξ) + (tlNCbP10c13 f ξ + tlNCbP11c13 f ξ))) + (((tlNCbP12c13 f ξ + tlNCbP13c13
      f ξ) + (tlNCbP14c12 f ξ + tlNCbP15c12 f ξ)) + ((tlNCbP16c11 f ξ + tlNCbP17c10 f ξ) +
      (tlNCbP20c13 f ξ + tlNCbP21c13 f ξ)))) + ((((tlNCbP22c13 f ξ + tlNCbP23c13 f ξ) +
      (tlNCbP24c12 f ξ + tlNCbP25c12 f ξ)) + ((tlNCbP26c11 f ξ + tlNCbP27c10 f ξ) + (tlNCbP28c9 f
      ξ + tlNCbP31c13 f ξ))) + (((tlNCbP32c13 f ξ + tlNCbP33c13 f ξ) + (tlNCbP34c13 f ξ +
      tlNCbP35c12 f ξ)) + ((tlNCbP36c12 f ξ + tlNCbP37c11 f ξ) + (tlNCbP38c10 f ξ + tlNCbP39c9 f
      ξ))))) + ((((tlNCbP40c8 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP1c13 f ξ + tlWTwoXP2c13 f ξ)) +
      ((tlWTwoXP3c13 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP1c13 f ξ + tlWOneXP2c13 f ξ))) +
      (((tlWOneXP3c12 f ξ + tlWOneXP4c12 f ξ) + (tlWOneXP5c10 f ξ + tlWZeroXP0c13 f ξ)) +
      ((tlWZeroXP1c12 f ξ + tlWZeroXP2c10 f ξ) + tlWZeroXP3c5 f ξ))) = 0 := by
  simp only [tlNCbP2c13, tlNCbP3c13, tlNCbP4c13, tlNCbP5c13, tlNCbP6c12, tlNCbP7c11,
      tlNCbP10c13, tlNCbP11c13, tlNCbP12c13, tlNCbP13c13, tlNCbP14c12, tlNCbP15c12,
      tlNCbP16c11, tlNCbP17c10, tlNCbP20c13, tlNCbP21c13, tlNCbP22c13, tlNCbP23c13,
      tlNCbP24c12, tlNCbP25c12, tlNCbP26c11, tlNCbP27c10, tlNCbP28c9, tlNCbP31c13,
      tlNCbP32c13, tlNCbP33c13, tlNCbP34c13, tlNCbP35c12, tlNCbP36c12, tlNCbP37c11,
      tlNCbP38c10, tlNCbP39c9, tlNCbP40c8, tlWTwoXP0c13, tlWTwoXP1c13, tlWTwoXP2c13,
      tlWTwoXP3c13, tlWOneXP0c13, tlWOneXP1c13, tlWOneXP2c13, tlWOneXP3c12,
      tlWOneXP4c12, tlWOneXP5c10, tlWZeroXP0c13, tlWZeroXP1c12, tlWZeroXP2c10,
      tlWZeroXP3c5]
  ring1

lemma tl_band14 (f ξ : ℚ) :
    (((((tlNCbP2c14 f ξ + tlNCbP3c14 f ξ) + (tlNCbP4c14 f ξ + tlNCbP5c14 f ξ)) + ((tlNCbP6c13 f ξ
      + tlNCbP7c12 f ξ) + (tlNCbP11c14 f ξ + tlNCbP12c14 f ξ))) + (((tlNCbP13c14 f ξ + tlNCbP14c13
      f ξ) + (tlNCbP15c13 f ξ + tlNCbP16c12 f ξ)) + ((tlNCbP17c11 f ξ + tlNCbP21c14 f ξ) +
      (tlNCbP22c14 f ξ + tlNCbP23c14 f ξ)))) + ((((tlNCbP24c13 f ξ + tlNCbP25c13 f ξ) +
      (tlNCbP26c12 f ξ + tlNCbP27c11 f ξ)) + ((tlNCbP28c10 f ξ + tlNCbP32c14 f ξ) + (tlNCbP33c14 f
      ξ + tlNCbP34c14 f ξ))) + (((tlNCbP35c13 f ξ + tlNCbP36c13 f ξ) + (tlNCbP37c12 f ξ +
      tlNCbP38c11 f ξ)) + ((tlNCbP39c10 f ξ + tlNCbP40c9 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP1c14 f
      ξ))))) + ((((tlWTwoXP2c14 f ξ + tlWTwoXP3c14 f ξ) + (tlWOneXP0c14 f ξ + tlWOneXP1c14 f ξ)) +
      ((tlWOneXP2c14 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP4c13 f ξ + tlWOneXP5c11 f ξ))) +
      ((tlWZeroXP0c14 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP2c11 f ξ + tlWZeroXP3c6 f ξ))) = 0 := by
  simp only [tlNCbP2c14, tlNCbP3c14, tlNCbP4c14, tlNCbP5c14, tlNCbP6c13, tlNCbP7c12,
      tlNCbP11c14, tlNCbP12c14, tlNCbP13c14, tlNCbP14c13, tlNCbP15c13, tlNCbP16c12,
      tlNCbP17c11, tlNCbP21c14, tlNCbP22c14, tlNCbP23c14, tlNCbP24c13, tlNCbP25c13,
      tlNCbP26c12, tlNCbP27c11, tlNCbP28c10, tlNCbP32c14, tlNCbP33c14, tlNCbP34c14,
      tlNCbP35c13, tlNCbP36c13, tlNCbP37c12, tlNCbP38c11, tlNCbP39c10, tlNCbP40c9,
      tlWTwoXP0c14, tlWTwoXP1c14, tlWTwoXP2c14, tlWTwoXP3c14, tlWOneXP0c14,
      tlWOneXP1c14, tlWOneXP2c14, tlWOneXP3c13, tlWOneXP4c13, tlWOneXP5c11,
      tlWZeroXP0c14, tlWZeroXP1c13, tlWZeroXP2c11, tlWZeroXP3c6]
  ring1

lemma tl_band15 (f ξ : ℚ) :
    (((((tlNCbP3c15 f ξ + tlNCbP4c15 f ξ) + (tlNCbP5c15 f ξ + tlNCbP6c14 f ξ)) + ((tlNCbP7c13 f ξ
      + tlNCbP12c15 f ξ) + (tlNCbP13c15 f ξ + tlNCbP14c14 f ξ))) + (((tlNCbP15c14 f ξ +
      tlNCbP16c13 f ξ) + (tlNCbP17c12 f ξ + tlNCbP22c15 f ξ)) + ((tlNCbP23c15 f ξ + tlNCbP24c14 f
      ξ) + (tlNCbP25c14 f ξ + tlNCbP26c13 f ξ)))) + ((((tlNCbP27c12 f ξ + tlNCbP28c11 f ξ) +
      (tlNCbP32c15 f ξ + tlNCbP33c15 f ξ)) + ((tlNCbP34c15 f ξ + tlNCbP35c14 f ξ) + (tlNCbP36c14 f
      ξ + tlNCbP37c13 f ξ))) + (((tlNCbP38c12 f ξ + tlNCbP39c11 f ξ) + (tlNCbP40c10 f ξ +
      tlWTwoXP0c15 f ξ)) + ((tlWTwoXP1c15 f ξ + tlWTwoXP2c15 f ξ) + (tlWTwoXP3c15 f ξ +
      tlWOneXP1c15 f ξ))))) + (((tlWOneXP2c15 f ξ + tlWOneXP3c14 f ξ) + (tlWOneXP4c14 f ξ +
      tlWOneXP5c12 f ξ)) + ((tlWZeroXP0c15 f ξ + tlWZeroXP1c14 f ξ) + (tlWZeroXP2c12 f ξ +
      tlWZeroXP3c7 f ξ))) = 0 := by
  simp only [tlNCbP3c15, tlNCbP4c15, tlNCbP5c15, tlNCbP6c14, tlNCbP7c13, tlNCbP12c15,
      tlNCbP13c15, tlNCbP14c14, tlNCbP15c14, tlNCbP16c13, tlNCbP17c12, tlNCbP22c15,
      tlNCbP23c15, tlNCbP24c14, tlNCbP25c14, tlNCbP26c13, tlNCbP27c12, tlNCbP28c11,
      tlNCbP32c15, tlNCbP33c15, tlNCbP34c15, tlNCbP35c14, tlNCbP36c14, tlNCbP37c13,
      tlNCbP38c12, tlNCbP39c11, tlNCbP40c10, tlWTwoXP0c15, tlWTwoXP1c15,
      tlWTwoXP2c15, tlWTwoXP3c15, tlWOneXP1c15, tlWOneXP2c15, tlWOneXP3c14,
      tlWOneXP4c14, tlWOneXP5c12, tlWZeroXP0c15, tlWZeroXP1c14, tlWZeroXP2c12,
      tlWZeroXP3c7]
  ring1

lemma tl_band16 (f ξ : ℚ) :
    (((((tlNCbP4c16 f ξ + tlNCbP5c16 f ξ) + (tlNCbP6c15 f ξ + tlNCbP7c14 f ξ)) + ((tlNCbP13c16 f ξ
      + tlNCbP14c15 f ξ) + (tlNCbP15c15 f ξ + tlNCbP16c14 f ξ))) + (((tlNCbP17c13 f ξ +
      tlNCbP23c16 f ξ) + (tlNCbP24c15 f ξ + tlNCbP25c15 f ξ)) + ((tlNCbP26c14 f ξ + tlNCbP27c13 f
      ξ) + (tlNCbP28c12 f ξ + tlNCbP33c16 f ξ)))) + ((((tlNCbP34c16 f ξ + tlNCbP35c15 f ξ) +
      (tlNCbP36c15 f ξ + tlNCbP37c14 f ξ)) + ((tlNCbP38c13 f ξ + tlNCbP39c12 f ξ) + (tlNCbP40c11 f
      ξ + tlWTwoXP0c16 f ξ))) + (((tlWTwoXP1c16 f ξ + tlWTwoXP2c16 f ξ) + (tlWTwoXP3c16 f ξ +
      tlWOneXP1c16 f ξ)) + ((tlWOneXP2c16 f ξ + tlWOneXP3c15 f ξ) + (tlWOneXP4c15 f ξ +
      tlWOneXP5c13 f ξ))))) + ((tlWZeroXP0c16 f ξ + tlWZeroXP1c15 f ξ) + (tlWZeroXP2c13 f ξ +
      tlWZeroXP3c8 f ξ)) = 0 := by
  simp only [tlNCbP4c16, tlNCbP5c16, tlNCbP6c15, tlNCbP7c14, tlNCbP13c16, tlNCbP14c15,
      tlNCbP15c15, tlNCbP16c14, tlNCbP17c13, tlNCbP23c16, tlNCbP24c15, tlNCbP25c15,
      tlNCbP26c14, tlNCbP27c13, tlNCbP28c12, tlNCbP33c16, tlNCbP34c16, tlNCbP35c15,
      tlNCbP36c15, tlNCbP37c14, tlNCbP38c13, tlNCbP39c12, tlNCbP40c11, tlWTwoXP0c16,
      tlWTwoXP1c16, tlWTwoXP2c16, tlWTwoXP3c16, tlWOneXP1c16, tlWOneXP2c16,
      tlWOneXP3c15, tlWOneXP4c15, tlWOneXP5c13, tlWZeroXP0c16, tlWZeroXP1c15,
      tlWZeroXP2c13, tlWZeroXP3c8]
  ring1

lemma tl_band17 (f ξ : ℚ) :
    ((((tlNCbP5c17 f ξ + tlNCbP6c16 f ξ) + (tlNCbP7c15 f ξ + tlNCbP13c17 f ξ)) + ((tlNCbP14c16 f ξ
      + tlNCbP15c16 f ξ) + (tlNCbP16c15 f ξ + tlNCbP17c14 f ξ))) + (((tlNCbP24c16 f ξ +
      tlNCbP25c16 f ξ) + (tlNCbP26c15 f ξ + tlNCbP27c14 f ξ)) + ((tlNCbP28c13 f ξ + tlNCbP34c17 f
      ξ) + (tlNCbP35c16 f ξ + tlNCbP36c16 f ξ)))) + ((((tlNCbP37c15 f ξ + tlNCbP38c14 f ξ) +
      (tlNCbP39c13 f ξ + tlNCbP40c12 f ξ)) + ((tlWTwoXP0c17 f ξ + tlWTwoXP1c17 f ξ) +
      (tlWTwoXP2c17 f ξ + tlWTwoXP3c17 f ξ))) + (((tlWTwoXP4c0 f ξ + tlWOneXP2c17 f ξ) +
      (tlWOneXP3c16 f ξ + tlWOneXP4c16 f ξ)) + ((tlWOneXP5c14 f ξ + tlWZeroXP1c16 f ξ) +
      (tlWZeroXP2c14 f ξ + tlWZeroXP3c9 f ξ)))) = 0 := by
  simp only [tlNCbP5c17, tlNCbP6c16, tlNCbP7c15, tlNCbP13c17, tlNCbP14c16, tlNCbP15c16,
      tlNCbP16c15, tlNCbP17c14, tlNCbP24c16, tlNCbP25c16, tlNCbP26c15, tlNCbP27c14,
      tlNCbP28c13, tlNCbP34c17, tlNCbP35c16, tlNCbP36c16, tlNCbP37c15, tlNCbP38c14,
      tlNCbP39c13, tlNCbP40c12, tlWTwoXP0c17, tlWTwoXP1c17, tlWTwoXP2c17,
      tlWTwoXP3c17, tlWTwoXP4c0, tlWOneXP2c17, tlWOneXP3c16, tlWOneXP4c16,
      tlWOneXP5c14, tlWZeroXP1c16, tlWZeroXP2c14, tlWZeroXP3c9]
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





































































































private lemma tl_col12 (f ξ : ℚ) :
    tlColumn f ξ 12 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band12 f ξ

private lemma tl_col13 (f ξ : ℚ) :
    tlColumn f ξ 13 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band13 f ξ

private lemma tl_col14 (f ξ : ℚ) :
    tlColumn f ξ 14 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band14 f ξ

private lemma tl_col15 (f ξ : ℚ) :
    tlColumn f ξ 15 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band15 f ξ

private lemma tl_col16 (f ξ : ℚ) :
    tlColumn f ξ 16 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band16 f ξ

private lemma tl_col17 (f ξ : ℚ) :
    tlColumn f ξ 17 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band17 f ξ


















end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
tlColumn f ξ (12 : Fin 24) = 0 ∧
tlColumn f ξ (13 : Fin 24) = 0 ∧
tlColumn f ξ (14 : Fin 24) = 0 ∧
tlColumn f ξ (15 : Fin 24) = 0 ∧
tlColumn f ξ (16 : Fin 24) = 0 ∧
tlColumn f ξ (17 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col12 f ξ, ⟨tl_col13 f ξ, ⟨tl_col14 f ξ, ⟨tl_col15 f ξ, ⟨tl_col16 f ξ, tl_col17 f ξ⟩⟩⟩⟩⟩

#print axioms solution

end
