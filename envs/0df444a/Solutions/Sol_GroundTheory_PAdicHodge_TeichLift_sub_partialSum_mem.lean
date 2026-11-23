-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.sub_partialSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.626831+00:00
-- url     : https://prove2.me/submissions/f706ae5b-cb1d-4667-ab5b-9e9d36607b27

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (x : Γ) (n : ℕ) : x - T.partialSum x n ∈ Ideal.span {T.π ^ n} :=
  T.mem_span_pow.2 ⟨_, T.sub_partialSum x n⟩
end GroundTheory.PAdicHodge.TeichLift
