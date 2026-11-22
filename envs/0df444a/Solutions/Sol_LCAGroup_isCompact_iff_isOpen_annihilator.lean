-- Prove2me | solution 1 for LCAGroup.isCompact_iff_isOpen_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:10:43.75347+00:00
-- url     : https://prove2.me/submissions/2ddd51ec-a94e-4a2f-8b17-8f5dbeeeabed

import Mathlib
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_LCAGroup_pontryagin_duality
import Theorems.Thm_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup

open Topology

set_option autoImplicit false

open LCAGroup

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G)) := by
  -- `Ĝ / H^⊥ ≃ₜ* Ĥ`
  obtain ⟨e, -⟩ := LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup G H hH
  constructor
  · intro hc
    -- `H` compact, so `Ĥ` is discrete, so `Ĝ / H^⊥` is discrete, so `H^⊥` is open
    haveI : CompactSpace H := isCompact_iff_compactSpace.mp hc
    haveI : DiscreteTopology (PontryaginDual G ⧸ annihilator H) :=
      e.toHomeomorph.isEmbedding.discreteTopology
    exact QuotientGroup.discreteTopology_iff.mp inferInstance
  · intro ho
    -- `H^⊥` open, so `Ĝ / H^⊥ ≅ Ĥ` is discrete, so `H ≅ Ĥ^` is compact
    haveI : DiscreteTopology (PontryaginDual G ⧸ annihilator H) :=
      QuotientGroup.discreteTopology ho
    haveI : DiscreteTopology (PontryaginDual H) :=
      e.symm.toHomeomorph.isEmbedding.discreteTopology
    haveI : LocallyCompactSpace H := hH.locallyCompactSpace
    obtain ⟨e', -⟩ := LCAGroup.pontryagin_duality H
    haveI : CompactSpace H := e'.toHomeomorph.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
