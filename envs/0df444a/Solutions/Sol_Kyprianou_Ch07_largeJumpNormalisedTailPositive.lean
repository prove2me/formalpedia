-- Prove2me | solution 1 for Kyprianou.Ch07.largeJumpNormalisedTailPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:16:03.169334+00:00
-- url     : https://prove2.me/submissions/6303add8-e7ba-4e0c-8de6-f58918d13fbf

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    ∀ x : Real, 0 < x →
      0 < (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) (Set.Ioi x) := by
  intro x hx
  let z : Real := max x 1
  have hz : 0 < z := lt_of_lt_of_le hx (le_max_left x 1)
  have hposReal : 0 < (PiH (Set.Ioi z)).toReal := hRegular.1 z hz
  have hpos : 0 < PiH (Set.Ioi z) := by
    have hne : PiH (Set.Ioi z) ≠ 0 := by
      intro hh
      simp [hh] at hposReal
    exact pos_iff_ne_zero.mpr hne
  have hsubset : Set.Ioi z ⊆ Set.Ioi x ∩ Set.Ioi 1 := by
    intro y hy
    exact ⟨lt_of_le_of_lt (le_max_left x 1) hy,
      lt_of_le_of_lt (le_max_right x 1) hy⟩
  have hrest : 0 < (PiH.restrict (Set.Ioi (1 : Real))) (Set.Ioi x) := by
    rw [Measure.restrict_apply measurableSet_Ioi]
    exact lt_of_lt_of_le hpos (measure_mono hsubset)
  have hInv : 0 < (PiH (Set.Ioi (1 : Real)))⁻¹ := by
    exact ENNReal.inv_pos.mpr (ne_of_lt hLargeFinite)
  change ((PiH.restrict (Set.Ioi (1 : Real))).withDensity
    (fun _ : Real => (PiH (Set.Ioi (1 : Real)))⁻¹))
      (Set.Ioi x) > 0
  rw [MeasureTheory.withDensity_const]
  simp only [Measure.smul_apply]
  exact ENNReal.mul_pos (ne_of_gt hInv) (ne_of_gt hrest)
