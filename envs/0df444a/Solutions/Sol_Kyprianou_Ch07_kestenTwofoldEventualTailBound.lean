-- Prove2me | solution 1 for Kyprianou.Ch07.kestenTwofoldEventualTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:47:01.746223+00:00
-- url     : https://prove2.me/submissions/e7157694-ead9-4286-8d7b-0c83df51f66a

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvTwo : Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
          ((2 : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)))
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ T : Real, 0 < T ∧
      ∀ x : Real, T ≤ x →
        ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal < 2 + epsilon := by
  have hThreshold : (1 : Real) < 1 + epsilon / 2 := by linarith
  have hEv : ∀ᶠ x : Real in atTop,
      ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
          ((2 : Real) * (G (Set.Ioi x)).toReal) <
            1 + epsilon / 2 :=
    Filter.Tendsto.eventually_lt_const hThreshold hConvTwo
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨max M 1, lt_of_lt_of_le (by norm_num) (le_max_right M 1), ?_⟩
  intro x hx
  have hMx : M ≤ x := le_trans (le_max_left M 1) hx
  have hXpos : 0 < x := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right M 1) hx)
  have hGT : G (Set.Ioi x) < ⊤ :=
    lt_of_le_of_lt (prob_le_one) (by norm_num)
  have hDen : 0 < (G (Set.Ioi x)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hPositiveTail x hXpos, hGT⟩
  have hEq :
      ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal =
      (((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
        ((2 : Real) * (G (Set.Ioi x)).toReal)) * 2 := by
    field_simp [ne_of_gt hDen]
  rw [hEq]
  nlinarith [hM x hMx]
