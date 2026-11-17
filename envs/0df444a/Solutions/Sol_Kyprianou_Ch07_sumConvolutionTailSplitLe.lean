-- Prove2me | solution 1 for Kyprianou.Ch07.sumConvolutionTailSplitLe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:03.379205+00:00
-- url     : https://prove2.me/submissions/1ec83218-9a8f-40c9-87f1-938dbdb7ffa4

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
    (x : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) ≤
      mu (Set.Ioi x) +
        ∫⁻ a : Real in Set.Iic x, nu (Set.Ioi (x - a)) ∂mu := by
  rw [Kyprianou.Ch07.sumConvolutionTailIntegral mu nu x]
  have hSplit := MeasureTheory.lintegral_add_compl
    (fun a : Real => nu (Set.Ioi (x - a)))
    (μ := mu) (A := Set.Iic x) measurableSet_Iic
  have hCompl : (Set.Iic x)ᶜ = Set.Ioi x := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ioi, not_le]
  rw [hCompl] at hSplit
  have hUpper :
      (∫⁻ a : Real in Set.Ioi x, nu (Set.Ioi (x - a)) ∂mu) ≤
        mu (Set.Ioi x) := by
    calc
      _ ≤ (∫⁻ a : Real in Set.Ioi x, (1 : ENNReal) ∂mu) := by
        apply lintegral_mono
        intro a
        exact prob_le_one
      _ = mu (Set.Ioi x) := by simp
  calc
    _ = (∫⁻ a : Real in Set.Iic x,
        nu (Set.Ioi (x - a)) ∂mu) +
        (∫⁻ a : Real in Set.Ioi x,
          nu (Set.Ioi (x - a)) ∂mu) := hSplit.symm
    _ ≤ (∫⁻ a : Real in Set.Iic x,
        nu (Set.Ioi (x - a)) ∂mu) + mu (Set.Ioi x) :=
          (by
            simpa only [add_comm] using
              (add_le_add_left hUpper
                (∫⁻ a : Real in Set.Iic x,
                  nu (Set.Ioi (x - a)) ∂mu)))
    _ = mu (Set.Ioi x) +
        (∫⁻ a : Real in Set.Iic x,
          nu (Set.Ioi (x - a)) ∂mu) := by ac_rfl
