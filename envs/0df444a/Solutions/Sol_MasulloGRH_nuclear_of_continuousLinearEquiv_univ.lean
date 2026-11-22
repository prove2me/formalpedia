-- Prove2me | solution 1 for MasulloGRH.nuclear_of_continuousLinearEquiv_univ
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T19:50:49.375957+00:00
-- url     : https://prove2.me/submissions/58b1cca7-003d-45e8-85a5-460e92bb712d

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

universe u v

namespace MasulloGRHNucUnivAux

open MasulloGRH Topology Filter

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

end MasulloGRHNucUnivAux

open MasulloGRH MasulloGRHNucUnivAux in
theorem solution (F : Type u) (E : Type v)
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (e : F ≃L[ℂ] E)
    (hE : IsNuclear E) : IsNuclear F := by
  obtain ⟨⟨ι, hι, p, hp⟩, hT2⟩ := hE.1
  haveI := hT2
  have hemb : Topology.IsEmbedding e := e.toHomeomorph.isEmbedding
  have hws : WithSeminorms (p.comp (e : F →ₗ[ℂ] E)) := hemb.isInducing.withSeminorms hp
  haveI : IsTopologicalAddGroup F := hws.topologicalAddGroup
  have hF : IsHLCS F :=
    ⟨⟨{q : Seminorm ℂ F // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩, hemb.t2Space⟩
  refine nuclear_of_quasinuclear_domination F hF fun r hr => ?_
  have hr' : Continuous (r.comp (e.symm : E →ₗ[ℂ] F)) := hr.comp e.symm.continuous
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hdom⟩ :=
    nuclear_quasinuclear_domination E hE (r.comp (e.symm : E →ₗ[ℂ] F)) hr'
  refine ⟨q.comp (e : F →ₗ[ℂ] E), fun n => (f n).comp (e : F →L[ℂ] E), c,
    hq.comp e.continuous, hc0, hcs, fun n x => hfq n (e x), fun x => ?_⟩
  have := hdom (e x)
  simpa using this
