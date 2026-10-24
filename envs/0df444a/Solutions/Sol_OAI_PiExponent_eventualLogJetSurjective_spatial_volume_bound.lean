-- Prove2me | solution 1 for OAI.PiExponent.eventualLogJetSurjective_spatial_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:36:44.890761+00:00
-- url     : https://prove2.me/submissions/e01de9ae-39be-43fc-8a28-da2736b1f2f1

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
import Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_transverseForSpatialVolume_retry9
import Theorems.Thm_OAI_PiExponent_eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9

open scoped BigOperators

theorem solution
    (m K : Nat) (hm : 0 < m) (hK : 0 < K)
    (w0 v0 alpha : Rat) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (w : Fin m -> Nat) (hw : forall i, 0 < w i)
    (c : Fin K -> Fin m -> Complex)
    (hc : forall i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    (K : Rat) * alpha ^ m <= 1 := by
  apply OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
      m K alpha w hm hK halpha hw c hc
  exact OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_retry9
      m K w0 v0 alpha hw0 hv0 halpha w hw c hjet