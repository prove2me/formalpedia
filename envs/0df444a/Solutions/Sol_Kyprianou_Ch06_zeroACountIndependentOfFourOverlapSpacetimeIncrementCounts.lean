-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:39:44.938319+00:00
-- url     : https://prove2.me/submissions/5db88b4c-376c-4dcd-a082-e835fe3af18b

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeRectanglesValid
import Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeMarksDisjointFromA
import Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeRectanglesSeparated
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfSeparatedOutsideRectangles
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (hst : s ≤ t)
    (x y z w : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s (B \ C)-N omega 0 (B \ C) = x ∧
      N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
      N omega s (C \ B)-N omega 0 (C \ B) = z ∧
      N omega t C-N omega s C = w} =
    P {omega | N omega r A = 0} *
    P {omega |
      N omega s (B \ C)-N omega 0 (B \ C) = x ∧
      N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
      N omega s (C \ B)-N omega 0 (C \ B) = z ∧
      N omega t C-N omega s C = w} := by
  let starts : Fin 4 → NNReal := fun i => if i = 3 then s else 0
  let stops : Fin 4 → NNReal := fun i => if i = 3 then t else s
  let marks : Fin 4 → Set E := fun i =>
    if i = 0 then B \ C else if i = 1 then B ∩ C
      else if i = 2 then C \ B else C
  let counts : Fin 4 → Nat := fun i =>
    if i = 0 then x else if i = 1 then y else if i = 2 then z else w
  have hValid :=
    Kyprianou.Ch06.fourOverlapSpacetimeRectanglesValid
      n B C hB hC hFB hFC s t hst
  have hExternal :=
    Kyprianou.Ch06.fourOverlapSpacetimeMarksDisjointFromA A B C hAB hAC
  have hSep :=
    Kyprianou.Ch06.fourOverlapSpacetimeRectanglesSeparated B C s t hst
  have h :=
    Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
      P n N hPPP A hA hFA 4 starts stops marks counts
      hValid hExternal hSep r
  simpa [starts, stops, marks, counts,
    Fin.forall_fin_succ, and_assoc] using h
