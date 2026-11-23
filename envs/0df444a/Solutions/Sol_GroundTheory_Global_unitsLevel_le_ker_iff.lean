-- Prove2me | solution 1 for GroundTheory.Global.unitsLevel_le_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.874032+00:00
-- url     : https://prove2.me/submissions/eaeee6dc-9bff-4c62-8dcc-613b91d5b84f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Theorems.Thm_GroundTheory_Global_unitsLevel_antitone
import Theorems.Thm_GroundTheory_Global_exists_unitsLevel_le_ker

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
    (hχ : Continuous χ) {n : ℕ} : unitsLevel v n ≤ χ.ker ↔ conductorExponent v χ ≤ n := by
  have hne : {n : ℕ | unitsLevel v n ≤ χ.ker}.Nonempty :=
    (exists_unitsLevel_le_ker v hH χ hχ).imp fun _ h ↦ h.2
  refine ⟨fun h ↦ Nat.sInf_le h, fun h ↦ (unitsLevel_antitone v h).trans (Nat.sInf_mem hne)⟩
end GroundTheory.Global
