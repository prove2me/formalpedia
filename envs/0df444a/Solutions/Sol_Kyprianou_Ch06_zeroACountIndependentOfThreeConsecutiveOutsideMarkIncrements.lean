-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfThreeConsecutiveOutsideMarkIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:22:21.953778+00:00
-- url     : https://prove2.me/submissions/a4f0eeee-6cb1-404d-8976-dd811f05ab15

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B-N omega 0 B = k ∧
      N omega t B-N omega s B = l ∧
      N omega u B-N omega t B = q} =
    P {omega | N omega r A = 0} *
      P {omega |
        N omega s B-N omega 0 B = k ∧
        N omega t B-N omega s B = l ∧
        N omega u B-N omega t B = q} := by
  let starts : Fin 3 → NNReal := fun i =>
    if i = 0 then 0 else if i = 1 then s else t
  let stops : Fin 3 → NNReal := fun i =>
    if i = 0 then s else if i = 1 then t else u
  let marks : Fin 3 → Set E := fun _ => B
  let counts : Fin 3 → Nat := fun i =>
    if i = 0 then k else if i = 1 then l else q
  have hValid : ∀ i : Fin 3,
      starts i ≤ stops i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
    intro i
    fin_cases i
    · exact ⟨bot_le,hB,hFB⟩
    · exact ⟨hst,hB,hFB⟩
    · exact ⟨htu,hB,hFB⟩
  have hExternal : ∀ i : Fin 3, Disjoint A (marks i) := by
    intro i
    exact hAB
  have hSep : ∀ i j : Fin 3, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (marks i) (marks j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [starts,stops,marks,hst,htu,le_trans hst htu]
  have h :=
    Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
      P n N hPPP A hA hFA 3 starts stops marks counts
      hValid hExternal hSep r
  simpa [starts,stops,marks,counts,Fin.forall_fin_succ,
    and_assoc] using h
