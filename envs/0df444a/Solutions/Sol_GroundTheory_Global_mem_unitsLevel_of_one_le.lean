-- Prove2me | solution 1 for GroundTheory.Global.mem_unitsLevel_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:29.337905+00:00
-- url     : https://prove2.me/submissions/af3a389d-c525-49c7-8892-e2b9608fe525

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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) := by
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hlt : Valued.v ((x : v.adicCompletion K) - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one]
    refine h.trans_lt ?_
    rw [← exp_zero, exp_lt_exp]
    omega
  simpa using Valuation.map_eq_of_sub_lt _ hlt
end GroundTheory.Global
