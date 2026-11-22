-- Prove2me | solution 1 for LCAGroup.discreteTopology_iff_compactSpace_dual
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:29:53.568801+00:00
-- url     : https://prove2.me/submissions/0def3e69-66f7-4234-af31-07a0b60f2bad

import Mathlib
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

open LCAGroup

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    DiscreteTopology G ↔ CompactSpace (PontryaginDual G) := by
  constructor
  · intro _
    infer_instance
  · intro _
    obtain ⟨e, -⟩ := LCAGroup.pontryagin_duality G
    exact e.toHomeomorph.symm.discreteTopology
