-- Prove2me | solution 1 for HlawkaSchatten.tripleGap_le_ratio_mul_mappedPairGapSum
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T00:52:43.16122+00:00
-- url     : https://prove2.me/submissions/1af378ba-8d05-421d-a1d7-445c0d746e32

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_MazurGapComparison
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Gap comparison through a nonlinear Mazur map

The Mazur map is not additive, so the Hilbert model for a family
`x, y, z` must use sums of the three *images*, rather than the image of
`x + y + z`.  This file records that distinction in the interface used by
the variational proof and carries out the final ordered-algebraic transfer.
-/


variable {E H : Type*} [Add E]
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]







include 𝕜

open HlawkaSchatten

omit 𝕜 in

theorem solution
    (size : E → ℝ) (modelSize : E → ℝ) (map : E → H)
    (m M : ℝ) (x y z : E)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : tripleGap size x y z ≤
      2 * M * mappedTripleGap modelSize map x y z)
    (hPairXY : 2 * m * mappedPairGap modelSize map x y ≤ pairGap size x y)
    (hPairXZ : 2 * m * mappedPairGap modelSize map x z ≤ pairGap size x z)
    (hPairYZ : 2 * m * mappedPairGap modelSize map y z ≤ pairGap size y z)
    (hModel : mappedTripleGap modelSize map x y z ≤
      mappedPairGapSum modelSize map x y z) :
    tripleGap size x y z ≤ (M / m) * pairGapSum size x y z := by
  have hPair : 2 * m * mappedPairGapSum modelSize map x y z ≤
      pairGapSum size x y z := by
    dsimp only [mappedPairGapSum, pairGapSum]
    nlinarith
  have hRatio : 0 ≤ M / m := div_nonneg hM hm.le
  have hScaled := mul_le_mul_of_nonneg_left hPair hRatio
  have hCancel :
      (M / m) * (2 * m * mappedPairGapSum modelSize map x y z) =
        2 * M * mappedPairGapSum modelSize map x y z := by
    field_simp [ne_of_gt hm]
  rw [hCancel] at hScaled
  calc
    tripleGap size x y z ≤
        2 * M * mappedTripleGap modelSize map x y z := hTriple
    _ ≤ 2 * M * mappedPairGapSum modelSize map x y z :=
      mul_le_mul_of_nonneg_left hModel (mul_nonneg (by positivity) hM)
    _ ≤ (M / m) * pairGapSum size x y z := hScaled
