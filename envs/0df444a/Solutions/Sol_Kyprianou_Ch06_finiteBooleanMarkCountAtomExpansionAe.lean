-- Prove2me | solution 1 for Kyprianou.Ch06.finiteBooleanMarkCountAtomExpansionAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:25:17.061586+00:00
-- url     : https://prove2.me/submissions/be14b895-8063-483a-9dc8-17a4c2cb47cb

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkAtomsMeasurableDisjointCover
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i)) (i : Fin m) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t (B i) =
        ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => i ∈ S)),
          N omega t {x : E | ∀ j : Fin m,
            (x ∈ B j ↔ j ∈ S)} := by
  classical
  let atom : Finset (Fin m) → Set E := fun S =>
    {x : E | ∀ j : Fin m, (x ∈ B j ↔ j ∈ S)}
  let u : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun S => i ∈ S)
  obtain ⟨_, hAtoms, hCover⟩ :=
    Kyprianou.Ch06.finiteBooleanMarkAtomsMeasurableDisjointCover m B hB
  have hPair : ∀ S ∈ u, ∀ T ∈ u,
      S ≠ T → Disjoint (atom S) (atom T) := by
    intro S _ T _ hne
    exact hAtoms S T hne
  have hUnion : (⋃ S ∈ u, atom S) = B i := by
    ext x
    simpa [atom, u, Finset.mem_filter, and_comm] using (hCover i x).symm
  have hAdd :=
    Kyprianou.Ch06.finiteDisjointMarkedCountAdditivityAe
      P n N hPPP atom u hPair
  filter_upwards [hAdd] with omega h
  intro t
  change N omega t (B i) =
    ∑ S ∈ u, N omega t (atom S)
  rw [← hUnion]
  exact h t
