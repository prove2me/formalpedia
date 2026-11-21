-- Prove2me | solution 3 for MasulloGRH.bounded_lifting_strict_nuclear_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:51:49.549258+00:00
-- url     : https://prove2.me/submissions/4f3feec4-934b-42c0-97b2-aee0c759631a

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
import Theorems.Thm_MasulloGRH_strictLF_quotient_stage_factorization
import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded

open MasulloGRH Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsStrictLFOfNuclearFrechet E) (V : Submodule ℂ E)
    (hV : IsClosed (V : Set E)) (hQ : IsStrictLFOfNuclearFrechet (E ⧸ V)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by
  obtain ⟨X, hm, he, hX, ht⟩ := hE
  obtain ⟨Y, hn, hf, hY, hs⟩ := hQ
  intro B hB
  obtain ⟨n, A, hA, rfl⟩ := (bounded_in_strict_frechet_stages _ Y hn hf
    (fun n => (hY n).1) hs).2 B hB
  obtain ⟨k, v, hv⟩ := strictLF_quotient_stage_factorization E X hm he hX ht V hV Y hn hf hY hs n
  let W := V.comap (X k).subtype
  have hW : IsClosed (W : Set (X k)) := hV.preimage continuous_subtype_val
  obtain ⟨D, hD, hcover⟩ := nuclear_frechet_quotient_lifts_bounded _ (hX k).1 (hX k).2 W hW
    (v '' A) (hA.image v)
  refine ⟨(X k).subtypeL '' D, hD.image (X k).subtypeL, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨d, hd, heq⟩ := hcover ⟨a, ha, rfl⟩
  refine ⟨d.val, ⟨d, hd, rfl⟩, ?_⟩
  exact (congrArg (Submodule.mapQ W V (X k).subtype le_rfl) heq).trans (hv a)
