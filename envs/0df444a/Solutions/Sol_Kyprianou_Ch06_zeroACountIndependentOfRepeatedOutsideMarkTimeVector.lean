-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfRepeatedOutsideMarkTimeVector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:13:59.383646+00:00
-- url     : https://prove2.me/submissions/e905cfe6-0038-432d-a2ec-d8efb571b900

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideCountsAllTimes
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAlmostSureCountableStatistic
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
    (A B : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (m : Nat) (r u : NNReal) (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega u B = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m, N omega u B = levels i} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let X : Omega → Nat := fun omega => N omega u B
  let Y : Omega → (Fin m → Nat) := fun omega _ => X omega
  have hD : MeasurableSet D := by
    exact measurableSet_eq_fun (hPPP.1 r A hA) measurable_const
  have hX : ∀ k : Nat, MeasurableSet {omega | X omega = k} := by
    intro k
    exact measurableSet_eq_fun (hPPP.1 u B hB) measurable_const
  have hFact : ∀ k : Nat,
      P (D ∩ {omega | X omega = k}) =
        P D * P {omega | X omega = k} := by
    intro k
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
        P n N hPPP A B B hA hB hB hAB hAB
        hFA hFB hFB r u u k k
    simpa only [D, X, Set.inter_def, Set.mem_inter_iff,
      Set.mem_setOf_eq, and_self] using h
  have h :=
    Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
      P D hD X Y (fun k : Nat => fun _ : Fin m => k)
      hX hFact (Filter.Eventually.of_forall (fun _ => rfl)) levels
  simpa only [D, Y, X, Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq, funext_iff] using h
