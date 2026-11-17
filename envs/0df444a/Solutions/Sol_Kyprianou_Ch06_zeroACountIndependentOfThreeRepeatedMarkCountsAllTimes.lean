-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeRepeatedMarkCountsAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:29:21.106812+00:00
-- url     : https://prove2.me/submissions/a2bda30a-db02-4be1-90e3-39736fc5753a

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
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
    (r s t u : NNReal) (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t B = l ∧ N omega u B = q} =
    P {omega | N omega r A = 0} *
      P {omega | N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q} := by
  rcases le_total s t with hst | hts
  · rcases le_total t u with htu | hut
    · exact
        Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
          P n N hPPP A B hA hB hAB hFA hFB
          r s t u hst htu k l q
    · rcases le_total s u with hsu | hus
      · have h :=
          Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
            P n N hPPP A B hA hB hAB hFA hFB
            r s u t hsu hut k q l
        simpa only [and_comm, and_left_comm, and_assoc] using h
      · have h :=
          Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
            P n N hPPP A B hA hB hAB hFA hFB
            r u s t hus hst q k l
        simpa only [and_comm, and_left_comm, and_assoc] using h
  · rcases le_total s u with hsu | hus
    · have h :=
        Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
          P n N hPPP A B hA hB hAB hFA hFB
          r t s u hts hsu l k q
      simpa only [and_comm, and_left_comm, and_assoc] using h
    · rcases le_total t u with htu | hut
      · have h :=
          Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
            P n N hPPP A B hA hB hAB hFA hFB
            r t u s htu hus l q k
        simpa only [and_comm, and_left_comm, and_assoc] using h
      · have h :=
          Kyprianou.Ch06.zeroACountIndependentOfThreeOrderedRepeatedCountsAllLevels
            P n N hPPP A B hA hB hAB hFA hFB
            r u t s hut hts q l k
        simpa only [and_comm, and_left_comm, and_assoc] using h
