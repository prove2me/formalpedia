-- Prove2me | solution 1 for Kyprianou.Ch05.blackwellUniformTruncatedIntervalBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:31:55.614602+00:00
-- url     : https://prove2.me/submissions/563ed317-f5fc-4af0-a47b-09eb43cd688e

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Blackwell convergence gives a global bound on truncated interval masses. -/
theorem solution
    (V : Measure Real) (mu : Real) (hmu : 0 < mu)
    (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu))) :
    ∀ d : Real, 0 < d → ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C := by
  intro d hd
  have he : ∀ᶠ a : Real in atTop,
      (V (Set.Ioc a (a+d))).toReal < d/mu+1 :=
    (hBlackwell d hd).eventually (gt_mem_nhds (by linarith : d/mu < d/mu+1))
  obtain ⟨R, hR⟩ := eventually_atTop.1 he
  let C := max (V (Set.Icc 0 (max R 0+d))) (ENNReal.ofReal (d/mu+1))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact max_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr (hfinite _), ENNReal.ofReal_lt_top⟩ |>.ne
  · intro a x
    by_cases ha : max R 0 ≤ a
    · have hsub : Set.Ioc a (a+d) ⊆ Set.Icc 0 (a+d) := by
        intro z hz
        exact ⟨le_trans (le_trans (le_max_right R 0) ha) hz.1.le, hz.2⟩
      have hf := ne_top_of_le_ne_top (hfinite (a+d)) (measure_mono hsub)
      have hb := hR a (le_trans (le_max_left R 0) ha)
      have hle : V (Set.Ioc a (a+d)) ≤ ENNReal.ofReal (d/mu+1) := by
        rw [← ENNReal.ofReal_toReal hf]
        exact ENNReal.ofReal_le_ofReal hb.le
      exact (measure_mono Set.inter_subset_right).trans (hle.trans (le_max_right _ _))
    · have hsub : Set.Icc 0 x ∩ Set.Ioc a (a+d) ⊆
          Set.Icc 0 (max R 0+d) := by
        intro z hz
        exact ⟨hz.1.1, hz.2.2.trans ((by linarith [le_of_lt (lt_of_not_ge ha)] : a+d ≤ max R 0+d))⟩
      exact (measure_mono hsub).trans (le_max_left _ _)
