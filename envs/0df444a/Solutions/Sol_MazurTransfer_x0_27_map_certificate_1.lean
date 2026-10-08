-- Prove2me | solution 1 for MazurTransfer.x0_27_map_certificate_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:09:49.307089+00:00
-- url     : https://prove2.me/submissions/d893b185-4e8b-4fdf-ba6b-bff4e143fefe

import Mathlib
import Definitions.Def_MazurTransfer_XZeroTwentySevenMapCertificateData

open MazurTorsion.XZeroTwentySeven
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


theorem MazurTransfer.x0_27_map_certificate_1 {s₁ s₂ s₃ : ℚ}
    (h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0) :
    (mapNya s₂ s₃ ^ 2 + mapNya s₂ s₃ * mapDya s₂ s₃ + 7 * mapDya s₂ s₃ ^ 2) *
        mapDx s₁ s₂ s₃ ^ 3 - mapNx s₁ s₂ s₃ ^ 3 * mapDya s₂ s₃ ^ 2 =
      remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
        + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
        + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
        + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
        + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
        + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃
        + remPart24 s₂ s₃ := by
  linear_combination (norm := skip)
    (cofOnePart0 s₁ s₂ s₃ + cofOnePart1 s₁ s₂ s₃ + cofOnePart2 s₁ s₂ s₃ + cofOnePart3 s₁ s₂ s₃
       + cofOnePart4 s₁ s₂ s₃ + cofOnePart5 s₁ s₂ s₃ + cofOnePart6 s₁ s₂ s₃
       + cofOnePart7 s₁ s₂ s₃ + cofOnePart8 s₁ s₂ s₃ + cofOnePart9 s₁ s₂ s₃
       + cofOnePart10 s₁ s₂ s₃ + cofOnePart11 s₁ s₂ s₃ + cofOnePart12 s₁ s₂ s₃
       + cofOnePart13 s₁ s₂ s₃ + cofOnePart14 s₂ s₃ + cofOnePart15 s₂ s₃ + cofOnePart16 s₂ s₃
       + cofOnePart17 s₂ s₃ + cofOnePart18 s₂ s₃ + cofOnePart19 s₂ s₃ + cofOnePart20 s₂ s₃
       + cofOnePart21 s₂ s₃) *
      h1
  simp only [mapNya, mapDya, mapNx, mapDx,
    remPart0, remPart1, remPart2, remPart3, remPart4, remPart5, remPart6, remPart7,
    remPart8, remPart9, remPart10, remPart11, remPart12, remPart13, remPart14,
    remPart15, remPart16, remPart17, remPart18, remPart19, remPart20, remPart21,
    remPart22, remPart23, remPart24,
    cofOnePart0, cofOnePart1, cofOnePart2, cofOnePart3, cofOnePart4, cofOnePart5,
    cofOnePart6, cofOnePart7, cofOnePart8, cofOnePart9, cofOnePart10, cofOnePart11,
    cofOnePart12, cofOnePart13, cofOnePart14, cofOnePart15, cofOnePart16,
    cofOnePart17, cofOnePart18, cofOnePart19, cofOnePart20, cofOnePart21]
  ring1

theorem solution {s₁ s₂ s₃ : ℚ}
    (h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0) :
    (mapNya s₂ s₃ ^ 2 + mapNya s₂ s₃ * mapDya s₂ s₃ + 7 * mapDya s₂ s₃ ^ 2) *
        mapDx s₁ s₂ s₃ ^ 3 - mapNx s₁ s₂ s₃ ^ 3 * mapDya s₂ s₃ ^ 2 =
      remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
        + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
        + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
        + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
        + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
        + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃
        + remPart24 s₂ s₃  := by
  exact MazurTransfer.x0_27_map_certificate_1 h1

#print axioms MazurTransfer.x0_27_map_certificate_1
#print axioms solution
