-- Prove2me | solution 1 for GroundTheory.Global.unitsLevel_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:46.793949+00:00
-- url     : https://prove2.me/submissions/0b4694e2-59fa-4dd4-8e16-066c3203d27a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor

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
namespace GroundTheory.Global
theorem _root_.solution : Antitone (unitsLevel (K := K) v) := by
  intro m n hmn x hx
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [exp_le_exp]
  omega
end GroundTheory.Global
