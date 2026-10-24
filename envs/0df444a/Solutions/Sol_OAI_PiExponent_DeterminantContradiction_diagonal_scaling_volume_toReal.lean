-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:02:04.694845+00:00
-- url     : https://prove2.me/submissions/6c089a91-0858-40fd-8ad5-69ae41628dff

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_scaling_volume_toReal_nonzero
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (hw : ∀ i, 0 < w i)
    (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      (∏ i : Fin m, w i) * (MeasureTheory.volume s).toReal := by
  have hnz : ∀ i, w i ≠ 0 := fun i => ne_of_gt (hw i)
  simpa [abs_of_pos (Finset.prod_pos fun i _ => hw i)] using
    OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal_nonzero
      w hnz s hs