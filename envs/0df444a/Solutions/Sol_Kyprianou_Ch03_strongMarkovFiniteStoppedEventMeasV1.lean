-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovFiniteStoppedEventMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:20:59.872742+00:00
-- url     : https://prove2.me/submissions/4f852267-5fc2-400d-b89c-fc54ebbe5f5e

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega) (hA : (∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)}))) :
    MeasurableSet (A ∩ {w : Omega | tau w ≠ ⊤}) := by
  classical
  have hUnion : A ∩ {w | tau w ≠ ⊤} =
      ⋃ n : ℕ, A ∩ {w | tau w ≤ ((n : NNReal) : WithTop NNReal)} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨ha, hw⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ((tau w).untop hw)
      refine ⟨n, ha, ?_⟩
      rw [← WithTop.coe_untop (tau w) hw]
      exact_mod_cast hn
    · rintro ⟨n, ha, hn⟩
      refine ⟨ha, ?_⟩
      intro ht
      rw [ht] at hn
      simpa using hn
  rw [hUnion]
  exact MeasurableSet.iUnion (fun n => F.le _ _ (hA (n : NNReal)))
