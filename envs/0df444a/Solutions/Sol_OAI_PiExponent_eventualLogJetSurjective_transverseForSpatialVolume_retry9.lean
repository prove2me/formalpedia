-- Prove2me | solution 1 for OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_retry9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:41:22.764986+00:00
-- url     : https://prove2.me/submissions/9fe5f6d4-003f-4e76-95d7-3f049587afe5

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
import Theorems.Thm_OAI_PiExponent_logJetSurjective_transverseForSpatialVolume_at
open scoped BigOperators

theorem solution
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c := by
  rcases hjet with ⟨D, hD, H0, hH0⟩
  refine ⟨D, hD, H0, ?_⟩
  intro H hH hdiv
  exact OAI.PiExponent.logJetSurjective_transverseForSpatialVolume_at
    m K w0 v0 alpha hw0 hv0 halpha w hw c H (hH0 H hH hdiv)