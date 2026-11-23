-- Prove2me | solution 1 for GroundTheory.Global.mem_unitsLevel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:44.862811+00:00
-- url     : https://prove2.me/submissions/8c7619c3-5568-4a27-adae-e6c260e3b131

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
variable {v}
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v (x : v.adicCompletion K) = 1 ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl
end GroundTheory.Global
