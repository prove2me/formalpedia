-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfFiniteTwoOutsideSpacetimeCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:30:29.84583+00:00
-- url     : https://prove2.me/submissions/ee6d95ed-67a0-4eea-a0cc-b2684dfdbf2f

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
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (m : Nat) (r s t : NNReal)
    (times : Fin m → NNReal) (marks : Fin m → Set E)
    (hSelect : ∀ i : Fin m,
      (times i = s ∧ marks i = B) ∨
      (times i = t ∧ marks i = C))
    (levels : Fin m → Nat) :
    P {omega | N omega r A = 0 ∧
      ∀ i : Fin m, N omega (times i) (marks i) = levels i} =
    P {omega | N omega r A = 0} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (marks i) = levels i} := by
  classical
  let D : Set Omega := {omega | N omega r A = 0}
  let X : Omega → Nat × Nat := fun omega =>
    (N omega s B, N omega t C)
  let Y : Omega → (Fin m → Nat) :=
    fun omega i => N omega (times i) (marks i)
  let f : (Nat × Nat) → Fin m → Nat := fun pair i =>
    if (times i = s ∧ marks i = B) then pair.1 else pair.2
  have hD : MeasurableSet D :=
    measurableSet_eq_fun (hPPP.1 r A hA) measurable_const
  have hX : ∀ p : Nat × Nat,
      MeasurableSet {omega | X omega = p} := by
    rintro ⟨k,l⟩
    have hS : MeasurableSet {omega | N omega s B = k} :=
      measurableSet_eq_fun (hPPP.1 s B hB) measurable_const
    have hT : MeasurableSet {omega | N omega t C = l} :=
      measurableSet_eq_fun (hPPP.1 t C hC) measurable_const
    simpa only [X, Prod.mk.injEq, Set.setOf_and] using hS.inter hT
  have hFact : ∀ p : Nat × Nat,
      P (D ∩ {omega | X omega = p}) =
        P D * P {omega | X omega = p} := by
    rintro ⟨k,l⟩
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
        P n N hPPP A B C hA hB hC hAB hAC
        hFA hFB hFC r s t k l
    simpa only [D,X,Prod.mk.injEq,Set.inter_def,
      Set.mem_inter_iff,Set.mem_setOf_eq,and_assoc] using h
  have hAe : ∀ᵐ omega ∂P, Y omega = f (X omega) := by
    apply Filter.Eventually.of_forall
    intro omega
    funext i
    change N omega (times i) (marks i) =
      if h : times i = s ∧ marks i = B then
        N omega s B else N omega t C
    by_cases hf : times i = s ∧ marks i = B
    · rw [dif_pos hf, hf.1, hf.2]
    · have hg : times i = t ∧ marks i = C :=
        (hSelect i).resolve_left hf
      rw [dif_neg hf, hg.1, hg.2]
  have h :=
    Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
      P D hD X Y f hX hFact hAe levels
  simpa only [D,Y,Set.inter_def,Set.mem_inter_iff,
    Set.mem_setOf_eq,funext_iff] using h
