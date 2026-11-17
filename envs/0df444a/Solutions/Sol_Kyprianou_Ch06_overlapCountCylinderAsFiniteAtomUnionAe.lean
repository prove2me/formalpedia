-- Prove2me | solution 1 for Kyprianou.Ch06.overlapCountCylinderAsFiniteAtomUnionAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:17:06.1632+00:00
-- url     : https://prove2.me/submissions/6909df4a-2a39-4514-bab8-39b78f068250

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_overlapCountCylinderAsDisjointAtomSumAe
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
    (B C : Set E) (t : NNReal) (k l : Nat) :
    ∀ᵐ omega ∂P,
      (N omega t B = k ∧ N omega t C = l) ↔
      ∃ q : Fin (min k l + 1),
        N omega t (B \ C) = k - (q : Nat) ∧
        N omega t (C \ B) = l - (q : Nat) ∧
        N omega t (B ∩ C) = (q : Nat) := by
  have hAtoms :=
    Kyprianou.Ch06.overlapCountCylinderAsDisjointAtomSumAe
      P n N hPPP B C t k l
  filter_upwards [hAtoms] with omega ha
  constructor
  · intro h
    obtain ⟨q, hBound, hB, hC, hI⟩ := ha.mp h
    exact ⟨⟨q, Nat.lt_succ_of_le hBound⟩, hB, hC, hI⟩
  · rintro ⟨q, hB, hC, hI⟩
    exact ha.mpr ⟨q, Nat.le_of_lt_succ q.isLt, hB, hC, hI⟩
