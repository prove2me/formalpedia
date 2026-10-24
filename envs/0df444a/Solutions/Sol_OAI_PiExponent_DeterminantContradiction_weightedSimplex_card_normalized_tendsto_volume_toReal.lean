-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:30:31.255473+00:00
-- url     : https://prove2.me/submissions/d8d3cc0c-63a1-4689-8a40-10b6f56432b2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_explicit_sandwich
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_explicit_bounds_tendsto_for_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_of_eventual_squeeze

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => ((realWeightedSimplex w (A * H)).card : Real) / H ^ m) atTop
      (nhds ((MeasureTheory.volume
        {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by
  let S : Real := ∑ i : Fin m, w i
  let V : Real := (MeasureTheory.volume
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal
  let lower : Real → Real := fun H =>
    (A - S / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i
  let upper : Real → Real := fun H =>
    (A + S / H) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i
  have hlim := OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto_for_volume
    (m := m) (w := w) (A := A) hw hA
  have hbounds : ∀ᶠ H : Real in atTop,
      lower H ≤ ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ∧
      ((realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤ upper H := by
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => le_of_lt (hw i)
    have hSA_nonneg : 0 ≤ S / A := div_nonneg hS (le_of_lt hA)
    filter_upwards [Filter.eventually_gt_atTop (S / A + 1)] with H hH
    have hHpos : 0 < H := by linarith
    have hSA : S / A < H := by linarith
    have hSH : S < H * A := (div_lt_iff₀ hA).1 hSA
    have hcut : S / H < A := (div_lt_iff₀ hHpos).2 (by nlinarith)
    simpa [S, lower, upper] using
      OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_explicit_sandwich
        (m := m) (w := w) (A := A) (H := H) hw hHpos hcut
  apply OAI.PiExponent.DeterminantContradiction.tendsto_of_eventual_squeeze
    (f := fun H : Real => ((realWeightedSimplex w (A * H)).card : Real) / H ^ m)
    (lower := lower) (upper := upper) (L := V) hbounds
  · simpa [lower, upper, S, V] using hlim.1
  · simpa [lower, upper, S, V] using hlim.2