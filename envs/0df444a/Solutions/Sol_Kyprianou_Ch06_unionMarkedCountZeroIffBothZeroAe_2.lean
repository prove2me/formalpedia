-- Prove2me | solution 2 for Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:12:15.18046+00:00
-- url     : https://prove2.me/submissions/c8e28179-7b84-452c-901d-880a81362b7e

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (N omega t B = 0 ∧ N omega t C = 0) ↔
      N omega t (B ∪ C) = 0 := by
  filter_upwards [hPPP.2.1] with omega h t
  have hadd := h.2.1 t
  have h1 : N omega t (B ∪ C) = N omega t B + N omega t (C \ B) := by
    rw [← hadd B (C \ B) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx), Set.union_diff_self]
  have h2 : N omega t C = N omega t (C ∩ B) + N omega t (C \ B) := by
    rw [← hadd (C ∩ B) (C \ B) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2), Set.inter_union_sdiff]
  have h3 : N omega t B = N omega t (C ∩ B) + N omega t (B \ C) := by
    rw [← hadd (C ∩ B) (B \ C) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.1),
      Set.inter_comm, Set.inter_union_sdiff]
  constructor
  · rintro ⟨hB, hC⟩; omega
  · intro hU; omega

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (N omega t B = 0 ∧ N omega t C = 0) ↔
      N omega t (B ∪ C) = 0 :=
  Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe P n N hPPP B C
