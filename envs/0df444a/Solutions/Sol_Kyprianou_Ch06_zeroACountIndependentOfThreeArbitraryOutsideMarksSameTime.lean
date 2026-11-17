-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:46:28.927188+00:00
-- url     : https://prove2.me/submissions/c6d71f88-b67e-429a-8722-fca1a9d60350

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsPairwiseDisjoint
import Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsMeasurableFinite
import Theorems.Thm_Kyprianou_Ch06_threeMarkVennAtomsAllOutsideA
import Theorems.Thm_Kyprianou_Ch06_threeMarkedCountVennPartitionAe
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFiniteCompatibleRectangleObservable
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
    (A B C D : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (r u : NNReal) (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega u B = k ∧ N omega u C = l ∧
      N omega u D = q} =
    P {omega | N omega r A = 0} *
    P {omega | N omega u B = k ∧
      N omega u C = l ∧ N omega u D = q} := by
  let marks : Fin 7 → Set E := fun i =>
    if i = 0 then (B \ C) \ D
    else if i = 1 then (C \ B) \ D
    else if i = 2 then (D \ B) \ C
    else if i = 3 then (B ∩ C) \ D
    else if i = 4 then (B ∩ D) \ C
    else if i = 5 then (C ∩ D) \ B
    else B ∩ C ∩ D
  let starts : Fin 7 → NNReal := fun _ => 0
  let stops : Fin 7 → NNReal := fun _ => u
  let Y : Omega → Fin 3 → Nat := fun omega i =>
    if i = 0 then N omega u B
    else if i = 1 then N omega u C else N omega u D
  let f : (Fin 7 → Nat) → Fin 3 → Nat := fun v i =>
    if i = 0 then v 0 + v 3 + v 4 + v 6
    else if i = 1 then v 1 + v 3 + v 5 + v 6
    else v 2 + v 4 + v 5 + v 6
  let levels : Fin 3 → Nat := fun i =>
    if i = 0 then k else if i = 1 then l else q
  have hValid : ∀ i : Fin 7,
      starts i ≤ stops i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    have hi :=
      Kyprianou.Ch06.threeMarkVennAtomsMeasurableFinite
        n B C D hB hC hD hFB hFC hFD i
    exact ⟨bot_le,hi⟩
  have hExternal : ∀ i : Fin 7, Disjoint A (marks i) :=
    Kyprianou.Ch06.threeMarkVennAtomsAllOutsideA
      A B C D hAB hAC hAD
  have hSep : ∀ i j : Fin 7, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (marks i) (marks j) := by
    intro i j hij
    exact Or.inr (Or.inr
      (Kyprianou.Ch06.threeMarkVennAtomsPairwiseDisjoint
        B C D i j hij))
  have hCounts :=
    Kyprianou.Ch06.threeMarkedCountVennPartitionAe
      P n N hPPP B C D
  have hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i : Fin 7 =>
        N omega (stops i) (marks i) -
        N omega (starts i) (marks i)) := by
    filter_upwards [hCounts,hPPP.2.1] with omega hc hp
    funext i
    fin_cases i
    · simpa [Y,f,marks,starts,stops,hp.1,add_assoc]
        using (hc u).1
    · simpa [Y,f,marks,starts,stops,hp.1,add_assoc]
        using (hc u).2.1
    · simpa [Y,f,marks,starts,stops,hp.1,add_assoc]
        using (hc u).2.2
  have h :=
    Kyprianou.Ch06.zeroACountIndependentOfFiniteCompatibleRectangleObservable
      P n N hPPP A hA hFA 7 3 starts stops marks
      hValid hExternal hSep r Y f hAe levels
  simpa [Y,levels,funext_iff,Fin.forall_fin_succ,and_assoc] using h
