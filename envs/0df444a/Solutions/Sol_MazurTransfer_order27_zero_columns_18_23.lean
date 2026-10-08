-- Prove2me | solution 1 for MazurTransfer.order27_zero_columns_18_23
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:13:22.629292+00:00
-- url     : https://prove2.me/submissions/a707f284-1b21-45c8-a856-ecdb967d3487

import Definitions.Def_MazurTransfer_Order27ZeroRowData

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Band identities 18 through 23

The final independent band identities for the trisection certificate.
-/



section

namespace MazurTorsion.Kubert

lemma tl_band18 (f ξ : ℚ) :
    ((((tlNCbP6c17 f ξ + tlNCbP7c16 f ξ) + (tlNCbP14c17 f ξ + tlNCbP15c17 f ξ)) + ((tlNCbP16c16 f
      ξ + tlNCbP17c15 f ξ) + (tlNCbP24c17 f ξ + tlNCbP25c17 f ξ))) + (((tlNCbP26c16 f ξ +
      tlNCbP27c15 f ξ) + (tlNCbP28c14 f ξ + tlNCbP35c17 f ξ)) + ((tlNCbP36c17 f ξ + tlNCbP37c16 f
      ξ) + (tlNCbP38c15 f ξ + tlNCbP39c14 f ξ)))) + ((((tlNCbP40c13 f ξ + tlWTwoXP0c18 f ξ) +
      (tlWTwoXP1c18 f ξ + tlWTwoXP2c18 f ξ)) + ((tlWTwoXP3c18 f ξ + tlWTwoXP4c1 f ξ) +
      (tlWOneXP2c18 f ξ + tlWOneXP3c17 f ξ))) + (((tlWOneXP4c17 f ξ + tlWOneXP5c15 f ξ) +
      (tlWZeroXP1c17 f ξ + tlWZeroXP2c15 f ξ)) + tlWZeroXP3c10 f ξ)) = 0 := by
  simp only [tlNCbP6c17, tlNCbP7c16, tlNCbP14c17, tlNCbP15c17, tlNCbP16c16, tlNCbP17c15,
      tlNCbP24c17, tlNCbP25c17, tlNCbP26c16, tlNCbP27c15, tlNCbP28c14, tlNCbP35c17,
      tlNCbP36c17, tlNCbP37c16, tlNCbP38c15, tlNCbP39c14, tlNCbP40c13, tlWTwoXP0c18,
      tlWTwoXP1c18, tlWTwoXP2c18, tlWTwoXP3c18, tlWTwoXP4c1, tlWOneXP2c18,
      tlWOneXP3c17, tlWOneXP4c17, tlWOneXP5c15, tlWZeroXP1c17, tlWZeroXP2c15,
      tlWZeroXP3c10]
  ring1

lemma tl_band19 (f ξ : ℚ) :
    ((((tlNCbP7c17 f ξ + tlNCbP15c18 f ξ) + (tlNCbP16c17 f ξ + tlNCbP17c16 f ξ)) + ((tlNCbP25c18 f
      ξ + tlNCbP26c17 f ξ) + (tlNCbP27c16 f ξ + tlNCbP28c15 f ξ))) + (((tlNCbP36c18 f ξ +
      tlNCbP37c17 f ξ) + (tlNCbP38c16 f ξ + tlNCbP39c15 f ξ)) + ((tlNCbP40c14 f ξ + tlWTwoXP0c19 f
      ξ) + (tlWTwoXP1c19 f ξ + tlWTwoXP2c19 f ξ)))) + (((tlWTwoXP3c19 f ξ + tlWTwoXP4c2 f ξ) +
      (tlWOneXP3c18 f ξ + tlWOneXP4c18 f ξ)) + ((tlWOneXP5c16 f ξ + tlWZeroXP1c18 f ξ) +
      (tlWZeroXP2c16 f ξ + tlWZeroXP3c11 f ξ))) = 0 := by
  simp only [tlNCbP7c17, tlNCbP15c18, tlNCbP16c17, tlNCbP17c16, tlNCbP25c18, tlNCbP26c17,
      tlNCbP27c16, tlNCbP28c15, tlNCbP36c18, tlNCbP37c17, tlNCbP38c16, tlNCbP39c15,
      tlNCbP40c14, tlWTwoXP0c19, tlWTwoXP1c19, tlWTwoXP2c19, tlWTwoXP3c19,
      tlWTwoXP4c2, tlWOneXP3c18, tlWOneXP4c18, tlWOneXP5c16, tlWZeroXP1c18,
      tlWZeroXP2c16, tlWZeroXP3c11]
  ring1

lemma tl_band20 (f ξ : ℚ) :
    ((((tlNCbP7c18 f ξ + tlNCbP16c18 f ξ) + (tlNCbP17c17 f ξ + tlNCbP26c18 f ξ)) + ((tlNCbP27c17 f
      ξ + tlNCbP28c16 f ξ) + (tlNCbP37c18 f ξ + tlNCbP38c17 f ξ))) + (((tlNCbP39c16 f ξ +
      tlNCbP40c15 f ξ) + (tlWTwoXP0c20 f ξ + tlWTwoXP1c20 f ξ)) + ((tlWTwoXP2c20 f ξ +
      tlWTwoXP3c20 f ξ) + (tlWTwoXP4c3 f ξ + tlWOneXP3c19 f ξ)))) + ((tlWOneXP4c19 f ξ +
      tlWOneXP5c17 f ξ) + (tlWZeroXP2c17 f ξ + tlWZeroXP3c12 f ξ)) = 0 := by
  simp only [tlNCbP7c18, tlNCbP16c18, tlNCbP17c17, tlNCbP26c18, tlNCbP27c17, tlNCbP28c16,
      tlNCbP37c18, tlNCbP38c17, tlNCbP39c16, tlNCbP40c15, tlWTwoXP0c20,
      tlWTwoXP1c20, tlWTwoXP2c20, tlWTwoXP3c20, tlWTwoXP4c3, tlWOneXP3c19,
      tlWOneXP4c19, tlWOneXP5c17, tlWZeroXP2c17, tlWZeroXP3c12]
  ring1

lemma tl_band21 (f ξ : ℚ) :
    (((tlNCbP17c18 f ξ + tlNCbP27c18 f ξ) + (tlNCbP28c17 f ξ + tlNCbP38c18 f ξ)) + ((tlNCbP39c17 f
      ξ + tlNCbP40c16 f ξ) + (tlWTwoXP1c21 f ξ + tlWTwoXP2c21 f ξ))) + (((tlWTwoXP3c21 f ξ +
      tlWTwoXP4c4 f ξ) + (tlWOneXP4c20 f ξ + tlWOneXP5c18 f ξ)) + (tlWZeroXP2c18 f ξ +
      tlWZeroXP3c13 f ξ)) = 0 := by
  simp only [tlNCbP17c18, tlNCbP27c18, tlNCbP28c17, tlNCbP38c18, tlNCbP39c17, tlNCbP40c16,
      tlWTwoXP1c21, tlWTwoXP2c21, tlWTwoXP3c21, tlWTwoXP4c4, tlWOneXP4c20,
      tlWOneXP5c18, tlWZeroXP2c18, tlWZeroXP3c13]
  ring1

lemma tl_band22 (f ξ : ℚ) :
    ((tlNCbP28c18 f ξ + tlNCbP39c18 f ξ) + (tlNCbP40c17 f ξ + tlWTwoXP2c22 f ξ)) + ((tlWTwoXP4c5 f
      ξ + tlWOneXP5c19 f ξ) + (tlWZeroXP2c19 f ξ + tlWZeroXP3c14 f ξ)) = 0 := by
  simp only [tlNCbP28c18, tlNCbP39c18, tlNCbP40c17, tlWTwoXP2c22, tlWTwoXP4c5, tlWOneXP5c19,
      tlWZeroXP2c19, tlWZeroXP3c14]
  ring1

lemma tl_band23 (f ξ : ℚ) :
    (tlNCbP40c18 f ξ + tlWTwoXP4c6 f ξ) + (tlWOneXP5c20 f ξ + tlWZeroXP3c15 f ξ) = 0 := by
  simp only [tlNCbP40c18, tlWTwoXP4c6, tlWOneXP5c20, tlWZeroXP3c15]
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

















































































































private lemma tl_col18 (f ξ : ℚ) :
    tlColumn f ξ 18 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band18 f ξ

private lemma tl_col19 (f ξ : ℚ) :
    tlColumn f ξ 19 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band19 f ξ

private lemma tl_col20 (f ξ : ℚ) :
    tlColumn f ξ 20 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band20 f ξ

private lemma tl_col21 (f ξ : ℚ) :
    tlColumn f ξ 21 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band21 f ξ

private lemma tl_col22 (f ξ : ℚ) :
    tlColumn f ξ 22 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band22 f ξ

private lemma tl_col23 (f ξ : ℚ) :
    tlColumn f ξ 23 = 0 := by
  simpa [tlColumn,
      tlRowCell0, tlRowCell1, tlRowCell2, tlRowCell3,
      tlRowCell4, tlRowCell5, tlRowCell6, tlRowCell7,
      tlRowCell8, tlRowCell9, tlRowCell10, tlRowCell11,
      tlRowCell12, tlRowCell13, tlRowCell14, tlRowCell15,
      tlRowCell16,
      add_assoc, add_zero, zero_add] using tl_band23 f ξ






end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ,
tlColumn f ξ (18 : Fin 24) = 0 ∧
tlColumn f ξ (19 : Fin 24) = 0 ∧
tlColumn f ξ (20 : Fin 24) = 0 ∧
tlColumn f ξ (21 : Fin 24) = 0 ∧
tlColumn f ξ (22 : Fin 24) = 0 ∧
tlColumn f ξ (23 : Fin 24) = 0 := by
  intro f ξ
  exact ⟨tl_col18 f ξ, ⟨tl_col19 f ξ, ⟨tl_col20 f ξ, ⟨tl_col21 f ξ, ⟨tl_col22 f ξ, tl_col23 f ξ⟩⟩⟩⟩⟩

#print axioms solution

end
