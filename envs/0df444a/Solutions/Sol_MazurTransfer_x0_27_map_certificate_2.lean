-- Prove2me | solution 1 for MazurTransfer.x0_27_map_certificate_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:09:17.638626+00:00
-- url     : https://prove2.me/submissions/0180c2e6-37c3-400f-8f51-d9a08bc01b24

import Mathlib
import Definitions.Def_MazurTransfer_XZeroTwentySevenMapCertificateData

open MazurTorsion.XZeroTwentySeven
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


theorem MazurTransfer.x0_27_map_certificate_2 {s₁ s₂ s₃ : ℚ}
    (h2 : s₂ ^ 2 * s₃ ^ 3 + 36 * s₂ ^ 2 * s₃ ^ 2 + 270 * s₂ ^ 2 * s₃ - s₂ ^ 3 +
      729 * s₂ * s₃ ^ 2 + 26244 * s₂ * s₃ + 531441 * s₃ = 0) :
    remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
      + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
      + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
      + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
      + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
      + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃ + remPart24 s₂ s₃
      = 0 := by
  linear_combination (norm := skip)
    (cofTwoPart0 s₁ s₂ s₃ + cofTwoPart1 s₁ s₂ s₃ + cofTwoPart2 s₁ s₂ s₃ + cofTwoPart3 s₁ s₂ s₃
       + cofTwoPart4 s₁ s₂ s₃ + cofTwoPart5 s₁ s₂ s₃ + cofTwoPart6 s₁ s₂ s₃
       + cofTwoPart7 s₁ s₂ s₃ + cofTwoPart8 s₁ s₂ s₃ + cofTwoPart9 s₁ s₂ s₃
       + cofTwoPart10 s₁ s₂ s₃ + cofTwoPart11 s₂ s₃ + cofTwoPart12 s₂ s₃ + cofTwoPart13 s₂ s₃
       + cofTwoPart14 s₂ s₃ + cofTwoPart15 s₂ s₃) *
      h2
  simp only [
    remPart0, remPart1, remPart2, remPart3, remPart4, remPart5, remPart6, remPart7,
    remPart8, remPart9, remPart10, remPart11, remPart12, remPart13, remPart14,
    remPart15, remPart16, remPart17, remPart18, remPart19, remPart20, remPart21,
    remPart22, remPart23, remPart24,
    cofTwoPart0, cofTwoPart1, cofTwoPart2, cofTwoPart3, cofTwoPart4, cofTwoPart5,
    cofTwoPart6, cofTwoPart7, cofTwoPart8, cofTwoPart9, cofTwoPart10, cofTwoPart11,
    cofTwoPart12, cofTwoPart13, cofTwoPart14, cofTwoPart15]
  ring1

theorem solution {s₁ s₂ s₃ : ℚ}
    (h2 : s₂ ^ 2 * s₃ ^ 3 + 36 * s₂ ^ 2 * s₃ ^ 2 + 270 * s₂ ^ 2 * s₃ - s₂ ^ 3 +
      729 * s₂ * s₃ ^ 2 + 26244 * s₂ * s₃ + 531441 * s₃ = 0) :
    remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
      + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
      + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
      + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
      + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
      + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃ + remPart24 s₂ s₃
      = 0  := by
  exact MazurTransfer.x0_27_map_certificate_2 h2

#print axioms MazurTransfer.x0_27_map_certificate_2
#print axioms solution
