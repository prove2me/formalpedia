-- Prove2me | solution 1 for GroundTheory.Global.isOpen_ker_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:50.443671+00:00
-- url     : https://prove2.me/submissions/fffcb19b-ddd8-471a-9000-342b93ab6695

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Theorems.Thm_GroundTheory_Global_isOpen_unitsLevel
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
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨n, -, hn⟩ := exists_unitsLevel_le_ker v hH χ hχ
  exact Subgroup.isOpen_mono hn (isOpen_unitsLevel v n)
end GroundTheory.Global
