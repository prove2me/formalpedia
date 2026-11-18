-- Prove2me | solution 1 for Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:31:14.456195+00:00
-- url     : https://prove2.me/submissions/99b3bf68-a16d-4e97-a51b-dbbdd4e08e31

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAlmostSureCountableStatistic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m p : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) (Y : Omega → Fin p → Nat)
    (f : (Fin m → Nat) → Fin p → Nat)
    (hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i =>
        N omega (stops i) (C i) - N omega (starts i) (C i)))
    (levels : Fin p → Nat) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      Y omega = levels} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega | Y omega = levels} := by
  let Dset : Set Omega := {omega |
    N omega s B - N omega 0 B = 0 ∧
    N omega t D - N omega 0 D = 0}
  let X : Omega → Fin m → Nat := fun omega i =>
    N omega (stops i) (C i) - N omega (starts i) (C i)
  have hDset : MeasurableSet Dset := by
    change MeasurableSet
      ({omega | N omega s B - N omega 0 B = 0} ∩
       {omega | N omega t D - N omega 0 D = 0})
    exact
      (measurableSet_eq_fun
        ((hPPP.1 s B hB).sub (hPPP.1 0 B hB)) measurable_const).inter
      (measurableSet_eq_fun
        ((hPPP.1 t D hD).sub (hPPP.1 0 D hD)) measurable_const)
  have hX : ∀ x : Fin m → Nat,
      MeasurableSet {omega | X omega = x} := by
    intro x
    have hEach : ∀ i : Fin m,
        MeasurableSet {omega | X omega i = x i} := by
      intro i
      have ht := (hValid i).2.1
      exact measurableSet_eq_fun
        ((hPPP.1 (stops i) (C i) ht).sub
          (hPPP.1 (starts i) (C i) ht)) measurable_const
    have hInter :=
      MeasurableSet.iInter (fun i : Fin m => hEach i)
    simpa only [Set.setOf_forall, funext_iff, X] using hInter
  have hFact : ∀ x : Fin m → Nat,
      P (Dset ∩ {omega | X omega = x}) =
      P Dset * P {omega | X omega = x} := by
    intro x
    have h :=
      Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
        P n N hPPP B D hB hD hBD hFB hFD
        m starts stops C x hValid hBC hDC hSep s t
    simpa only [Dset, X, funext_iff, Set.inter_def,
      Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc] using h
  have hTransferred :=
    Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
      P Dset hDset X Y f hX hFact hAe levels
  simpa only [Dset, Set.inter_def, Set.mem_inter_iff,
    Set.mem_setOf_eq, and_assoc] using hTransferred
