-- Prove2me | solution 1 for GroundTheory.Global.conductorExponent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:03.929262+00:00
-- url     : https://prove2.me/submissions/ce25ece6-3456-48d0-9214-eabb771450c9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Theorems.Thm_GroundTheory_Global_unitsLevel_zero
import Theorems.Thm_GroundTheory_Global_unitsLevel_le_ker_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter IsDedekindDomain WithZero
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
variable {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global
theorem _root_.solution (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) :
    conductorExponent v χ = 0 ↔ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ χ.ker := by
  rw [← unitsLevel_zero, unitsLevel_le_ker_iff v hH χ hχ, Nat.le_zero]
end GroundTheory.Global
