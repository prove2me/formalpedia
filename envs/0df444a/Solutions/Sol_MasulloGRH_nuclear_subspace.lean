-- Prove2me | solution 1 for MasulloGRH.nuclear_subspace
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T22:49:14.780956+00:00
-- url     : https://prove2.me/submissions/98bfb9c9-89c0-4808-bef2-f588dd357220

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH TensorProduct Topology

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsNuclear E) (V : Submodule ℂ E) : IsNuclear V := by
  obtain ⟨⟨ι, hι, pE, hpE⟩, hT2⟩ := hE.1
  have : IsTopologicalAddGroup E := hpE.topologicalAddGroup
  have : PolynormableSpace ℂ E := hpE.toPolynormableSpace
  -- the restricted seminorm family defines the subspace topology, which is Hausdorff
  have hpV : WithSeminorms (pE.comp V.subtype) := LinearMap.withSeminorms_induced hpE V.subtype
  apply nuclear_of_quasinuclear_domination V ⟨⟨ι, hι, _, hpV⟩, inferInstance⟩
  intro p hp
  -- every continuous seminorm on `V` is dominated by the restriction of one on `E`
  obtain ⟨r, hrc, hpr⟩ :=
    Seminorm.exists_le_comp_of_isInducing (f := V.subtype) hp IsInducing.subtypeVal
  -- quasi-nuclear domination of `r` on `E`, restricted to `V`
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hdom⟩ :=
    nuclear_quasinuclear_domination E hE r hrc
  exact ⟨q.comp V.subtype, fun n => (f n).comp V.subtypeL, c, hq.comp continuous_subtype_val,
    hc0, hcs, fun n x => hfq n x, fun x => (hpr x).trans (hdom x)⟩
