-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:06:19.639469+00:00
-- url     : https://prove2.me/submissions/8b3ec7f7-326c-44ca-bdce-58d5763ede9d

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_shifted_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_volume_aux
import Mathlib.Data.Real.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real =>
        (H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)
          ≤ ((strictWeightedSimplex w H).card : Real))
      atTop := by
  have hthreshold : ∀ᶠ H : Real in atTop, Finset.univ.sum w < H :=
    Filter.eventually_gt_atTop (Finset.univ.sum w)
  filter_upwards [hthreshold] with H hH
  have hpositive : 0 < H - Finset.univ.sum w := by linarith
  set T : Real := H - Finset.univ.sum w
  have hcut : T + Finset.univ.sum w = H := by
    dsimp [T]
    ring
  have hcover :=
    OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume
      n w hw T hpositive
  rw [OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_volume_aux
    n w hw T hpositive] at hcover
  rw [hcut] at hcover
  simpa [T] using hcover
