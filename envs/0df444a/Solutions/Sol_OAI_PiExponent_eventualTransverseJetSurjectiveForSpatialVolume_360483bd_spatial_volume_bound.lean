-- Prove2me | solution 1 for OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd_spatial_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:17.801987+00:00
-- url     : https://prove2.me/submissions/1ffcf594-d2a7-43e7-8029-4e9d562c7ea4

import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
import Theorems.Thm_OAI_PiExponent_eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
open scoped BigOperators

theorem solution
    (m K : Nat) (alpha : Rat) (w : Fin m → Nat)
    (hm : 0 < m) (hK : 0 < K) (halpha : 0 < alpha)
    (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (htrans : OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c) :
    (K : Rat) * alpha ^ m ≤ 1 := by
  apply OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9 <;> assumption
