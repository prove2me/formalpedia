-- Prove2me | solution 1 for Kyprianou.Ch06.outsideCountVectorCompatibleRectangleRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:36:17.665471+00:00
-- url     : https://prove2.me/submissions/4425c0d1-58d7-458e-91d3-6cb57a08a7fa

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideBooleanAtomFiniteEnumeration
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
import Theorems.Thm_Kyprianou_Ch06_finiteObservationTimeCompatibleIntervalSchedule
import Theorems.Thm_Kyprianou_Ch06_disjointMarkTimeProductCompatible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) :
    ∃ (k : Nat) (starts stops : Fin k → NNReal)
      (D : Fin k → Set E),
      (∀ i, starts i ≤ stops i ∧ MeasurableSet (D i) ∧ n (D i) < ⊤) ∧
      (∀ i, Disjoint A (D i)) ∧
      (∀ i j : Fin k, i ≠ j →
        stops i ≤ starts j ∨ stops j ≤ starts i ∨
          Disjoint (D i) (D j)) ∧
      ∃ f : (Fin k → Nat) → Fin m → Nat,
        ∀ᵐ omega ∂P,
          (fun i : Fin m => N omega (times i) (B i)) =
            f (fun i : Fin k =>
              N omega (stops i) (D i) - N omega (starts i) (D i)) := by
  classical
  obtain ⟨a, mark, selected, hFacts, hMarks, hUnion⟩ :=
    Kyprianou.Ch06.outsideBooleanAtomFiniteEnumeration n A m B hB
  have hSpatial : ∀ i : Fin m, ∀ᵐ omega ∂P,
      ∀ t : NNReal, N omega t (B i) =
        ∑ j ∈ selected i, N omega t (mark j) := by
    intro i
    have hPair : ∀ j ∈ selected i, ∀ l ∈ selected i,
        j ≠ l → Disjoint (mark j) (mark l) := by
      intro j _ l _ hne
      exact hMarks j l hne
    have hAdd :=
      Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
        P n N hPPP mark (selected i) hPair
    filter_upwards [hAdd] with omega h
    intro t
    exact (congrArg (N omega t) (hUnion i).symm).trans (h t)
  have hSpatialAll : ∀ᵐ omega ∂P,
      ∀ i : Fin m, ∀ t : NNReal,
        N omega t (B i) =
          ∑ j ∈ selected i, N omega t (mark j) :=
    Filter.eventually_all.2 hSpatial
  obtain ⟨k, starts, stops, hTimeValid, hSeparated, hRecover⟩ :=
    Kyprianou.Ch06.finiteObservationTimeCompatibleIntervalSchedule
      m times
  let J : Fin m → Finset (Fin k) := fun i =>
    Classical.choose (hRecover i)
  have hJ : ∀ (i : Fin m) (F : NNReal → Nat),
      Monotone F → F 0 = 0 →
        F (times i) =
          ∑ l ∈ J i, (F (stops l) - F (starts l)) := by
    intro i F hMono hZero
    exact (Classical.choose_spec (hRecover i)) F hMono hZero
  let e : Fin (a * k) ≃ Fin a × Fin k := (finProdFinEquiv).symm
  let starts' : Fin (a * k) → NNReal :=
    fun p => starts (e p).2
  let stops' : Fin (a * k) → NNReal :=
    fun p => stops (e p).2
  let D : Fin (a * k) → Set E :=
    fun p => mark (e p).1
  let f : (Fin (a * k) → Nat) → Fin m → Nat :=
    fun counts i =>
      ∑ j ∈ selected i,
        ∑ l ∈ J i, counts (e.symm (j, l))
  have hValid : ∀ p : Fin (a * k),
      starts' p ≤ stops' p ∧
        MeasurableSet (D p) ∧ n (D p) < ⊤ := by
    intro p
    exact ⟨hTimeValid (e p).2, (hFacts (e p).1).1,
      (hFacts (e p).1).2.1⟩
  have hDis : ∀ p : Fin (a * k), Disjoint A (D p) := by
    intro p
    exact (hFacts (e p).1).2.2
  have hCompatible : ∀ p q : Fin (a * k), p ≠ q →
      stops' p ≤ starts' q ∨ stops' q ≤ starts' p ∨
        Disjoint (D p) (D q) := by
    intro p q hne
    exact Kyprianou.Ch06.disjointMarkTimeProductCompatible
      a k mark hMarks starts stops hSeparated p q hne
  refine ⟨a * k, starts', stops', D,
    hValid, hDis, hCompatible, f, ?_⟩
  filter_upwards [hPPP.2.1, hSpatialAll] with omega hPath hSpatialOmega
  funext i
  calc
    N omega (times i) (B i) =
        ∑ j ∈ selected i, N omega (times i) (mark j) :=
      hSpatialOmega i (times i)
    _ = ∑ j ∈ selected i,
        ∑ l ∈ J i,
          (N omega (stops l) (mark j) -
            N omega (starts l) (mark j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hJ i (fun t => N omega t (mark j))
        (hPath.2.2 (mark j)) (hPath.1 (mark j))
    _ = f (fun p =>
        N omega (stops' p) (D p) -
          N omega (starts' p) (D p)) i := by
      dsimp only [f, starts', stops', D]
      simp only [Equiv.apply_symm_apply, Prod.fst, Prod.snd]
