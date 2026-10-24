-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.cofinal_actualMatrix_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:10:28.264021+00:00
-- url     : https://prove2.me/submissions/ae38bb2a-26d0-42c4-9975-0f1816bb1447
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_actualPacket_surjective
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualPacket_surjective_iff_matrix_surjective
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (L : Real) :
    ∃ H : Real, L ≤ H ∧ 0 < H ∧
      Function.Surjective (actualMatrix d H).mulVecLin := by
  have hpacket :=
    OAI.PiExponent.DeterminantContradiction.eventually_actualPacket_surjective nu d
  have hlarge : ∀ᶠ H : Real in atTop, max L 1 ≤ H :=
    Filter.eventually_ge_atTop (max L 1)
  obtain ⟨H, hHpacket, hHlarge⟩ := (hpacket.and hlarge).exists
  have hL : L ≤ H := (le_max_left L 1).trans hHlarge
  have hHpos : 0 < H :=
    lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hHlarge)
  exact ⟨H, hL, hHpos,
    (OAI.PiExponent.DeterminantContradiction.actualPacket_surjective_iff_matrix_surjective
      nu d H).mp hHpacket⟩