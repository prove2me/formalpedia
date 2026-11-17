-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfFiniteCompatibleRectangleObservable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:33:36.178966+00:00
-- url     : https://prove2.me/submissions/4b1b2cc2-c148-4b93-b5bf-aa30114800a4

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfSeparatedOutsideRectangles
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
    (A : Set E) (hA : MeasurableSet A) (hFA : n A < ⊤)
    (m p : Nat) (starts stops : Fin m → NNReal)
    (B : Fin m → Set E)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (B i) ∧ n (B i) < ⊤)
    (hAB : ∀ i, Disjoint A (B i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (B i) (B j))
    (r : NNReal) (Y : Omega → Fin p → Nat)
    (f : (Fin m → Nat) → Fin p → Nat)
    (hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i =>
        N omega (stops i) (B i) - N omega (starts i) (B i)))
    (levels : Fin p → Nat) :
    P {omega | N omega r A = 0 ∧ Y omega = levels} =
    P {omega | N omega r A = 0} *
      P {omega | Y omega = levels} := by
  let D : Set Omega := {omega | N omega r A = 0}
  let X : Omega → Fin m → Nat := fun omega i =>
    N omega (stops i) (B i) - N omega (starts i) (B i)
  have hD : MeasurableSet D :=
    measurableSet_eq_fun (hPPP.1 r A hA) measurable_const
  have hX : ∀ x : Fin m → Nat,
      MeasurableSet {omega | X omega = x} := by
    intro x
    have hEach : ∀ i : Fin m,
        MeasurableSet {omega | X omega i = x i} := by
      intro i
      have ht := (hValid i).2.1
      exact measurableSet_eq_fun
        ((hPPP.1 (stops i) (B i) ht).sub
          (hPPP.1 (starts i) (B i) ht)) measurable_const
    have hInter :=
      MeasurableSet.iInter (fun i : Fin m => hEach i)
    simpa only [Set.setOf_forall, funext_iff, X] using hInter
  have hFact : ∀ x : Fin m → Nat,
      P (D ∩ {omega | X omega = x}) =
      P D * P {omega | X omega = x} := by
    intro x
    have h :=
      Kyprianou.Ch06.zeroACountIndependentOfSeparatedOutsideRectangles
        P n N hPPP A hA hFA m starts stops B x
        hValid hAB hSep r
    simpa only [D, X, funext_iff, Set.inter_def,
      Set.mem_inter_iff, Set.mem_setOf_eq] using h
  have hTransferred :=
    Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
      P D hD X Y f hX hFact hAe levels
  simpa only [D, Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq] using hTransferred
