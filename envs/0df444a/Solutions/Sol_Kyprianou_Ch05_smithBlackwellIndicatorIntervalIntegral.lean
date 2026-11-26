-- Prove2me | solution 1 for Kyprianou.Ch05.smithBlackwellIndicatorIntervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:00:39.825463+00:00
-- url     : https://prove2.me/submissions/a70e69a9-4469-498a-ad94-bb9aaa6683a8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- For a real measure V and x nonnegative, the Stieltjes integral of the translated [0,y) indicator on [0,x+y] is the real mass of the interval (x,x+y]. This preserves the endpoint convention even if V has atoms. -/
theorem solution
    (V : Measure Real) (x y : Real) (hx : 0 ≤ x) :
    (∫ s in Set.Icc 0 (x+y),
      (Set.Ico 0 y).indicator (fun _ : Real => (1 : Real)) (x+y-s) ∂V) =
      (V (Set.Ioc x (x+y))).toReal := by
  calc
    _ = ∫ s in Set.Icc 0 (x+y), (Set.Ioc x (x+y)).indicator (fun _ => (1 : Real)) s
        ∂V := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      have he : x+y-s ∈ Set.Ico (0 : Real) y ↔ s ∈ Set.Ioc x (x+y) := by
        simp only [mem_Ico, mem_Ioc]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      by_cases h : s ∈ Set.Ioc x (x+y)
      · simp [h, he.mpr h]
      · have hn : x+y-s ∉ Set.Ico (0 : Real) y := fun hh => h (he.mp hh)
        change (Set.Ico 0 y).indicator (fun _ : Real => (1 : Real)) (x+y-s) =
          (Set.Ioc x (x+y)).indicator (fun _ : Real => (1 : Real)) s
        rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem h]
    _ = _ := by
      rw [integral_indicator_const 1 measurableSet_Ioc, Measure.real_def,
        Measure.restrict_apply measurableSet_Ioc]
      have hsub : Set.Ioc x (x+y) ⊆ Set.Icc 0 (x+y) :=
        fun _ hs => ⟨hx.trans hs.1.le, hs.2⟩
      rw [Set.inter_eq_left.mpr hsub]
      simp
