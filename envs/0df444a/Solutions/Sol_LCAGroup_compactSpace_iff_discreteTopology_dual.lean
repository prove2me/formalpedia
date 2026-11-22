-- Prove2me | solution 1 for LCAGroup.compactSpace_iff_discreteTopology_dual
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:30:31.002827+00:00
-- url     : https://prove2.me/submissions/5a8d2b1f-747a-41d2-b478-aa1298f3000a

import Mathlib
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

namespace Sol_LCAGroup_compactSpace_iff_discreteTopology_dual

/-- The Pontryagin dual of a discrete group is compact: it is homeomorphic to the set of
monoid homomorphisms `A → Circle`, a closed subset of the compact product `A → Circle`. -/
theorem compactSpace_pontryaginDual_of_discrete (A : Type*) [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] : CompactSpace (PontryaginDual A) := by
  let f : PontryaginDual A → (A → Circle) := fun χ => ⇑χ
  have hf : IsInducing f :=
    (ContinuousMap.homeoFnOfDiscrete (X := A) (Y := Circle)).isInducing.comp
      (ContinuousMonoidHom.isInducing_toContinuousMap A Circle)
  have hrange : Set.range f = Set.range ((↑) : (A →* Circle) → A → Circle) := by
    ext g
    constructor
    · rintro ⟨χ, rfl⟩
      exact ⟨χ.toMonoidHom, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨{ toMonoidHom := φ, continuous_toFun := continuous_of_discreteTopology }, rfl⟩
  have hc : IsCompact (Set.range f) := by
    rw [hrange]
    exact (MonoidHom.isClosed_range_coe A Circle).isCompact
  rw [← Set.image_univ, ← hf.isCompact_iff] at hc
  exact ⟨hc⟩

end Sol_LCAGroup_compactSpace_iff_discreteTopology_dual

open LCAGroup

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) := by
  constructor
  · intro _
    infer_instance
  · intro _
    obtain ⟨e, -⟩ := LCAGroup.pontryagin_duality G
    have := Sol_LCAGroup_compactSpace_iff_discreteTopology_dual.compactSpace_pontryaginDual_of_discrete
      (PontryaginDual G)
    exact e.toHomeomorph.symm.compactSpace
