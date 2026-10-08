-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:12.421369+00:00
-- url     : https://prove2.me/submissions/481e63cf-b356-49e2-b3c0-d2131ca4c967

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

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
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0, tlTOneP0c1, tlTOneP0c2,
      tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6, tlTOneP0c7, tlTOneP0c8,
      tlTOneP1c0, tlTOneP1c1, tlTOneP1c2, tlTOneP1c3, tlTOneP1c4, tlTOneP1c5,
      tlTOneP1c6, tlTOneP1c7, tlTOneP1c8, tlTOneP1c9, tlTOneP2c0, tlTOneP2c1,
      tlWOneXP0c0, tlWOneXP0c1, tlWOneXP0c10, tlWOneXP0c11, tlWOneXP0c12,
      tlWOneXP0c13, tlWOneXP0c14, tlWOneXP0c2, tlWOneXP0c3, tlWOneXP0c4,
      tlWOneXP0c5, tlWOneXP0c6, tlWOneXP0c7, tlWOneXP0c8, tlWOneXP0c9]
  ring1

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
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP2c10, tlTOneP2c11, tlTOneP2c2,
      tlTOneP2c3, tlTOneP2c4, tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8,
      tlTOneP2c9, tlTOneP3c0, tlTOneP3c1, tlTOneP3c10, tlTOneP3c2, tlTOneP3c3,
      tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7, tlTOneP3c8, tlTOneP3c9,
      tlWOneXP1c0, tlWOneXP1c1, tlWOneXP1c10, tlWOneXP1c11, tlWOneXP1c12,
      tlWOneXP1c13, tlWOneXP1c14, tlWOneXP1c15, tlWOneXP1c16, tlWOneXP1c2,
      tlWOneXP1c3, tlWOneXP1c4, tlWOneXP1c5, tlWOneXP1c6, tlWOneXP1c7, tlWOneXP1c8,
      tlWOneXP1c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP2c0 f ξ +
      tlTOneP2c1 f ξ) * tlMOneV0 f =
      (((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + tlWOneXP0c14 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ +
      tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
      tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ +
      tlTOneP3c10 f ξ) * tlMOneV0 f =
      ((((tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ) + (tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ)) +
        ((tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ))) +
        (((tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ)) +
        ((tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ) + (tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ))))
        + tlWOneXP1c16 f ξ) := by
  exact ⟨MazurTorsion.Kubert.tlWOneX_s0, MazurTorsion.Kubert.tlWOneX_s1⟩

#print axioms MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP2c0 f ξ +
      tlTOneP2c1 f ξ) * tlMOneV0 f =
      (((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + tlWOneXP0c14 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ +
      tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
      tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ +
      tlTOneP3c10 f ξ) * tlMOneV0 f =
      ((((tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ) + (tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ)) +
        ((tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ))) +
        (((tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ)) +
        ((tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ) + (tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ))))
        + tlWOneXP1c16 f ξ)  := by
  exact MazurTransfer.order27_certificate_tlWOneX_s0_tlWOneX_s1

#print axioms solution
