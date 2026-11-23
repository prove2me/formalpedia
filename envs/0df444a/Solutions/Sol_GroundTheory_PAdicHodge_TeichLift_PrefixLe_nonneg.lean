-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.PrefixLe.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.322941+00:00
-- url     : https://prove2.me/submissions/ea2c7ffc-1101-4a33-a2d8-24eb5371bd3f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich

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
variable {T}
namespace GroundTheory.PAdicHodge.TeichLift
namespace PrefixLe
theorem _root_.solution {x : Γ} {n : ℕ} {b : ℝ} (h : T.PrefixLe x n b) : 0 ≤ b :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _))
end PrefixLe
end GroundTheory.PAdicHodge.TeichLift
