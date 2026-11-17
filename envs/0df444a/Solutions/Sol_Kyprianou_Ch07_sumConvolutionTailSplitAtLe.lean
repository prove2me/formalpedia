-- Prove2me | solution 1 for Kyprianou.Ch07.sumConvolutionTailSplitAtLe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:46:09.87524+00:00
-- url     : https://prove2.me/submissions/8790c07a-2e0c-467e-9e34-6b0ab7b616c8

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (mu nu : Measure Real) [SFinite nu] [IsProbabilityMeasure nu]
    (x T : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) ≤
      mu (Set.Ioi T) +
        ∫⁻ a : Real in Set.Iic T, nu (Set.Ioi (x - a)) ∂mu := by
  rw [Kyprianou.Ch07.sumConvolutionTailIntegral mu nu x]
  have hSplit := MeasureTheory.lintegral_add_compl
    (fun a : Real => nu (Set.Ioi (x - a)))
    (μ := mu) (A := Set.Iic T) measurableSet_Iic
  have hCompl : (Set.Iic T)ᶜ = Set.Ioi T := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ioi, not_le]
  rw [hCompl] at hSplit
  have hUpper :
      (∫⁻ a : Real in Set.Ioi T, nu (Set.Ioi (x - a)) ∂mu) ≤
        mu (Set.Ioi T) := by
    calc
      _ ≤ (∫⁻ a : Real in Set.Ioi T, (1 : ENNReal) ∂mu) := by
        apply lintegral_mono
        intro a
        exact prob_le_one
      _ = mu (Set.Ioi T) := by simp
  calc
    _ = (∫⁻ a : Real in Set.Iic T,
        nu (Set.Ioi (x - a)) ∂mu) +
        (∫⁻ a : Real in Set.Ioi T,
          nu (Set.Ioi (x - a)) ∂mu) := hSplit.symm
    _ ≤ (∫⁻ a : Real in Set.Iic T,
        nu (Set.Ioi (x - a)) ∂mu) + mu (Set.Ioi T) :=
          (by
            simpa only [add_comm] using
              (add_le_add_left hUpper
                (∫⁻ a : Real in Set.Iic T,
                  nu (Set.Ioi (x - a)) ∂mu)))
    _ = mu (Set.Ioi T) +
        (∫⁻ a : Real in Set.Iic T,
          nu (Set.Ioi (x - a)) ∂mu) := by ac_rfl
