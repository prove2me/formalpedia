-- Prove2me | solution 1 for Kyprianou.Ch06.disjointOutsideCountVectorRectangleRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T06:03:20.066205+00:00
-- url     : https://prove2.me/submissions/b67c5634-fb06-4fad-8cc6-642a06bee956

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hDisjoint : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j)) :
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
  refine ⟨m, (fun _ => 0), times, B, ?_, ?_, ?_, id, ?_⟩
  · intro i
    exact ⟨(show (0 : NNReal) ≤ times i from zero_le), (hB i).1, (hB i).2.2⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (hB i).2.1 hxB hxA
  · intro i j hij
    exact Or.inr (Or.inr (hDisjoint i j hij))
  · rcases hPPP with ⟨_, hPath, _⟩
    filter_upwards [hPath] with omega hOmega
    funext i
    simp [hOmega.1 (B i)]
