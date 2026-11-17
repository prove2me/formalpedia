-- Prove2me | solution 1 for Kyprianou.Ch07.kestenFixedNUniformTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:44:56.348296+00:00
-- url     : https://prove2.me/submissions/f94750d8-edc2-44a1-aa68-8b03395e6b5d

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (n : Nat) (hn : 2 ≤ n)
    (hConv : Tendsto (fun x : Real =>
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        ((n : Real) * (G (Set.Ioi x)).toReal))
      atTop (nhds (1 : Real))) :
    ∃ C : Real, 0 < C ∧
      ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ C := by
  have hev : ∀ᶠ x : Real in atTop,
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        ((n : Real) * (G (Set.Ioi x)).toReal) < 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) hConv
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hev
  let M : Real := max X0 1
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right X0 1)
  have hGLtTop (x : Real) : G (Set.Ioi x) < ⊤ :=
    lt_of_le_of_lt (prob_le_one) (by norm_num)
  have hD : 0 < (G (Set.Ioi M)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hPositiveTail M hMpos, hGLtTop M⟩
  have hnPos : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  let C : Real := 2 * (n : Real) + 1 / (G (Set.Ioi M)).toReal + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have hd0 : 0 ≤ (1 : Real) / (G (Set.Ioi M)).toReal :=
      div_nonneg (by norm_num) (le_of_lt hD)
    nlinarith
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  letI : IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) :=
    Kyprianou.Ch07.convolutionPowerProbability G n
  have hNumer : ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal ≤ 1 := by
    have hb : (Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x) ≤ 1 := prob_le_one
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hb)
  have hDx : 0 < (G (Set.Ioi x)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hPositiveTail x hx, hGLtTop x⟩
  by_cases hxM : M ≤ x
  · have hUpper := hX0 x (le_trans (le_max_left X0 1) hxM)
    have hEq : ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal =
        (((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal)) * n := by
      field_simp [ne_of_gt hDx, ne_of_gt hnPos]
    have hTailUpper : ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal < 2 * (n : Real) := by
      rw [hEq]
      exact (mul_lt_mul_of_pos_right hUpper hnPos)
    dsimp [C]
    have hInvNonneg : 0 ≤ (1 : Real) / (G (Set.Ioi M)).toReal :=
      div_nonneg (by norm_num) (le_of_lt hD)
    linarith
  · have hxBound : x ≤ M := le_of_lt (lt_of_not_ge hxM)
    have hSubset : Set.Ioi M ⊆ Set.Ioi x := by
      intro y hy
      exact lt_of_le_of_lt hxBound hy
    have hDLe : (G (Set.Ioi M)).toReal ≤ (G (Set.Ioi x)).toReal :=
      ENNReal.toReal_mono (ne_of_lt (hGLtTop x)) (measure_mono hSubset)
    have hSmall :
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ 1 / (G (Set.Ioi M)).toReal := by
      calc
        _ ≤ 1 / (G (Set.Ioi x)).toReal := by
            exact (div_le_div_iff_of_pos_right hDx).mpr hNumer
        _ ≤ 1 / (G (Set.Ioi M)).toReal :=
            div_le_div_of_nonneg_left (by norm_num) hD hDLe
    dsimp [C]
    linarith [hSmall, hnPos]
