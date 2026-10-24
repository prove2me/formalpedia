-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:07:25.617701+00:00
-- url     : https://prove2.me/submissions/e500b2e1-acef-40a0-a03b-8fdc60099d00

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators Interval
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.integral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0) =
      T / ((m + 1 : Nat) : Real) := by
  have hT0 : T ≠ 0 := ne_of_gt hT
  let g : Real → Real := fun t => ((T - t) / T) ^ m
  calc
    MeasureTheory.integral MeasureTheory.volume
        (fun t : Real => if 0 ≤ t ∧ t < T then g t else 0) =
        ∫ t, Set.indicator (Set.Ioc 0 T) g t ∂volume := by
          apply integral_congr_ae
          filter_upwards [Measure.ae_ne volume (0 : Real), Measure.ae_ne volume T]
            with t ht0 htT
          have hiff : (0 ≤ t ∧ t < T) ↔ t ∈ Set.Ioc 0 T := by
            simp only [Set.mem_Ioc]
            constructor
            · rintro ⟨h0, hlt⟩
              exact ⟨lt_of_le_of_ne h0 (Ne.symm ht0), le_of_lt hlt⟩
            · rintro ⟨hlt, hle⟩
              exact ⟨le_of_lt hlt, lt_of_le_of_ne hle htT⟩
          simp [Set.indicator, hiff]
    _ = ∫ t in Set.Ioc 0 T, g t ∂volume :=
      integral_indicator measurableSet_Ioc
    _ = ∫ t in (0 : Real)..T, g t := by
      rw [intervalIntegral.integral_of_le hT.le]
    _ = ∫ t in (0 : Real)..T, (t / T) ^ m := by
      dsimp [g]
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : Real)) (b := T) (f := fun x : Real => (x / T) ^ m) T)
    _ = T * ∫ t in (0 : Real)..1, t ^ m := by
      have hs := intervalIntegral.mul_integral_comp_mul_right
        (a := (0 : Real)) (b := (1 : Real))
        (f := fun x : Real => (x / T) ^ m) T
      have hs' :
          T * ∫ t in (0 : Real)..1, (t * T / T) ^ m =
            ∫ t in (0 : Real)..T, (t / T) ^ m := by
        simpa using hs
      rw [hs'.symm]
      simp [hT0]
    _ = T / ((m + 1 : Nat) : Real) := by
      rw [integral_pow]
      simp
      ring