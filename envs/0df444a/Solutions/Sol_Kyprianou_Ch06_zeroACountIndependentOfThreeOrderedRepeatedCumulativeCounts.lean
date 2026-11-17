-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCumulativeCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:23:59.090011+00:00
-- url     : https://prove2.me/submissions/727c1545-8da0-4982-a94b-f8506dd0e32f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeOrderedRepeatedMarkedCountsEqualIncrementsAe
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
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
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) (hkl : k ≤ l) (hlq : l ≤ q) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let G : Set Omega := {omega |
    N omega s B = k ∧ N omega t B = l ∧ N omega u B = q}
  let H : Set Omega := {omega |
    N omega s B-N omega 0 B = k ∧
    N omega t B-N omega s B = l-k ∧
    N omega u B-N omega t B = q-l}
  have hEvent :=
    Kyprianou.Ch06.threeOrderedRepeatedMarkedCountsEqualIncrementsAe
      P n N hPPP B s t u hst htu k l q hkl hlq
  change (∀ᵐ omega ∂P, (omega ∈ G) ↔ (omega ∈ H)) at hEvent
  have hRaw :=
    Kyprianou.Ch06.zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
      P n N hPPP A B hA hB hAB hFA hFB
      r s t u hst htu k (l-k) (q-l)
  have hRaw' : P (D ∩ H) = P D * P H := by
    simpa only [D,H,Set.inter_def,Set.mem_inter_iff,
      Set.mem_setOf_eq,and_assoc] using hRaw
  have hTransfer :=
    Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
      P D D G H
      (Filter.Eventually.of_forall (fun _ => Iff.rfl))
      hEvent hRaw'
  change P (D ∩ G) = P D * P G
  exact hTransfer
