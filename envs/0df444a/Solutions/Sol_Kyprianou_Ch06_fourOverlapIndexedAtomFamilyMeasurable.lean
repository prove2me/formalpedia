-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapIndexedAtomFamilyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:41:42.658667+00:00
-- url     : https://prove2.me/submissions/6ddb4bc5-9b88-449a-9102-51db20f920ed

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (s t : NNReal) (k l : Nat) :
    let F : Fin (k+1) × Fin (l+1) → Set Omega := fun i =>
      {omega | (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)}
    ∀ i, MeasurableSet (F i) := by
  dsimp only
  intro i
  by_cases hi : (i.1 : Nat)+(i.2 : Nat) ≤ l
  · have hX : MeasurableSet
        {omega | N omega s (B \ C) = k-(i.1 : Nat)} :=
      measurableSet_eq_fun (hPPP.1 s (B \ C) (hB.diff hC))
        measurable_const
    have hY : MeasurableSet
        {omega | N omega s (B ∩ C) = (i.1 : Nat)} :=
      measurableSet_eq_fun (hPPP.1 s (B ∩ C) (hB.inter hC))
        measurable_const
    have hZ : MeasurableSet
        {omega | N omega s (C \ B) = (i.2 : Nat)} :=
      measurableSet_eq_fun (hPPP.1 s (C \ B) (hC.diff hB))
        measurable_const
    have hW : MeasurableSet
        {omega | N omega t C-N omega s C =
          l-(i.1 : Nat)-(i.2 : Nat)} :=
      measurableSet_eq_fun
        ((hPPP.1 t C hC).sub (hPPP.1 s C hC))
        measurable_const
    have hAll : MeasurableSet
        {omega | N omega s (B \ C) = k-(i.1 : Nat) ∧
          N omega s (B ∩ C) = (i.1 : Nat) ∧
          N omega s (C \ B) = (i.2 : Nat) ∧
          N omega t C-N omega s C = l-(i.1 : Nat)-(i.2 : Nat)} := by
      simpa only [Set.setOf_and, and_assoc] using
        hX.inter (hY.inter (hZ.inter hW))
    simpa [hi] using hAll
  · simp [hi]
