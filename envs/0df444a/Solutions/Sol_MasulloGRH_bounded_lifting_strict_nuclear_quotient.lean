-- Prove2me | solution 1 for MasulloGRH.bounded_lifting_strict_nuclear_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:48:38.708194+00:00
-- url     : https://prove2.me/submissions/d4082ce6-1e83-4040-9148-8aa2a12dc22f

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
import Theorems.Thm_MasulloGRH_frechet_stage_image_lifts_in_strict_quotient

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLFOfNuclearFrechet E) (V : Submodule ℂ E)
    (hV : IsClosed (V : Set E)) (hQ : IsStrictLFOfNuclearFrechet (E ⧸ V)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hQ
  have hloc := bounded_in_strict_frechet_stages _ X hmono hexh (fun n => (hX n).1) htop
  haveI := hloc.1.2
  intro B hB
  obtain ⟨n, A, hA, rfl⟩ := hloc.2 B hB
  exact frechet_stage_image_lifts_in_strict_quotient E (X n) hE V hV (hX n).1
    (X n).subtypeL A hA

