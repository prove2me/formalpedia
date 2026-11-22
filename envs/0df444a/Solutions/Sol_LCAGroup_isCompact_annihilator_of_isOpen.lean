-- Prove2me | solution 1 for LCAGroup.isCompact_annihilator_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:13:57.743346+00:00
-- url     : https://prove2.me/submissions/cf29aa53-e618-41d3-b742-16efc08739fd

import Mathlib
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_LCAGroup_dual_quotient_equiv_annihilator

open Topology

set_option autoImplicit false

open LCAGroup

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (annihilator H : Set (PontryaginDual G)) := by
  have hcl : IsClosed (H : Set G) := H.isClosed_of_isOpen hH
  obtain ⟨e, -⟩ := LCAGroup.dual_quotient_equiv_annihilator G H hcl
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : CompactSpace (annihilator H) := e.toHomeomorph.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance
