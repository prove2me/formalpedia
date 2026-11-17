-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfFiniteThreeOutsideMarksSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:49:10.790582+00:00
-- url     : https://prove2.me/submissions/ea9990ab-dd85-4204-b9f1-7e4242eb40d2

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
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
    (A B C D : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (m : Nat) (r u : NNReal)
    (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      marks i = B ∨ marks i = C ∨ marks i = D)
    (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega u (marks i) = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m,
        N omega u (marks i) = levels i} := by
  classical
  let AZero : Set Omega := {omega | N omega r A = 0}
  let X : Omega → Nat × (Nat × Nat) := fun omega =>
    (N omega u B,(N omega u C,N omega u D))
  let Y : Omega → Fin m → Nat := fun omega i =>
    N omega u (marks i)
  let f : (Nat × (Nat × Nat)) → Fin m → Nat := fun p i =>
    if marks i = B then p.1
    else if marks i = C then p.2.1 else p.2.2
  have hAZero : MeasurableSet AZero :=
    measurableSet_eq_fun (hPPP.1 r A hA) measurable_const
  have hX : ∀ x : Nat × (Nat × Nat),
      MeasurableSet {omega | X omega = x} := by
    rintro ⟨k,⟨l,q⟩⟩
    have h1 : MeasurableSet {omega | N omega u B = k} :=
      measurableSet_eq_fun (hPPP.1 u B hB) measurable_const
    have h2 : MeasurableSet {omega | N omega u C = l} :=
      measurableSet_eq_fun (hPPP.1 u C hC) measurable_const
    have h3 : MeasurableSet {omega | N omega u D = q} :=
      measurableSet_eq_fun (hPPP.1 u D hD) measurable_const
    simpa only [X,Prod.mk.injEq,Set.setOf_and,and_assoc]
      using h1.inter (h2.inter h3)
  have hFact : ∀ x : Nat × (Nat × Nat),
      P (AZero ∩ {omega | X omega = x}) =
        P AZero * P {omega | X omega = x} := by
    rintro ⟨k,⟨l,q⟩⟩
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
        P n N hPPP A B C D hA hB hC hD
        hAB hAC hAD hFA hFB hFC hFD r u k l q
    simpa only [AZero,X,Prod.mk.injEq,
      Set.inter_def,Set.mem_inter_iff,Set.mem_setOf_eq,and_assoc]
      using h
  have hAe : ∀ᵐ omega ∂P, Y omega = f (X omega) := by
    apply Filter.Eventually.of_forall
    intro omega
    funext i
    change N omega u (marks i) =
      if h : marks i = B then N omega u B
      else if h : marks i = C then N omega u C else N omega u D
    by_cases hBmark : marks i = B
    · rw [dif_pos hBmark,hBmark]
    · by_cases hCmark : marks i = C
      · rw [dif_neg hBmark,dif_pos hCmark,hCmark]
      · have hDmark : marks i = D := by
          rcases hSelect i with hb | hc | hd
          · exact False.elim (hBmark hb)
          · exact False.elim (hCmark hc)
          · exact hd
        rw [dif_neg hBmark,dif_neg hCmark,hDmark]
  have h :=
    Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
      P AZero hAZero X Y f hX hFact hAe levels
  simpa only [AZero,Y,funext_iff,
    Set.inter_def,Set.mem_inter_iff,Set.mem_setOf_eq]
    using h
