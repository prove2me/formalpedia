-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:40:01.638827+00:00
-- url     : https://prove2.me/submissions/98ed940d-81fc-4fc9-9d3c-64a8b8dfbce1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
import Theorems.Thm_Kyprianou_Ch06_fourOverlapAtomCumulativeIncrementCountsAe
import Theorems.Thm_Kyprianou_Ch06_eventIndependenceOfAlmostSureEquivalentEvents
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
      N omega s (B \ C) = x ∧
      N omega s (B ∩ C) = y ∧
      N omega s (C \ B) = z ∧
      N omega t C - N omega s C = w} =
    P {omega | N omega r A = 0} *
    P {omega |
      N omega s (B \ C) = x ∧
      N omega s (B ∩ C) = y ∧
      N omega s (C \ B) = z ∧
      N omega t C - N omega s C = w} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let G : Set Omega := {omega |
    N omega s (B \ C) = x ∧
    N omega s (B ∩ C) = y ∧
    N omega s (C \ B) = z ∧
    N omega t C - N omega s C = w}
  let G' : Set Omega := {omega |
    N omega s (B \ C) - N omega 0 (B \ C) = x ∧
    N omega s (B ∩ C) - N omega 0 (B ∩ C) = y ∧
    N omega s (C \ B) - N omega 0 (C \ B) = z ∧
    N omega t C - N omega s C = w}
  have hRaw :=
    Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeIncrementCounts
      P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
      r s t hst x y z w
  have hRaw' : P (D ∩ G') = P D * P G' := by
    simpa only [D, G', Set.inter_def, Set.mem_inter_iff,
      Set.mem_setOf_eq, and_assoc] using hRaw
  have hAe :=
    Kyprianou.Ch06.fourOverlapAtomCumulativeIncrementCountsAe
      P n N hPPP B C s t x y z w
  change (∀ᵐ omega ∂P, (omega ∈ G) ↔ (omega ∈ G')) at hAe
  have h :=
    Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
      P D D G G' (Filter.Eventually.of_forall (fun _ => Iff.rfl))
      hAe hRaw'
  change P (D ∩ G) = P D * P G
  exact h
