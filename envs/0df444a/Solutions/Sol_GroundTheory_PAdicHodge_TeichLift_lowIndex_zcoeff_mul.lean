-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.lowIndex_zcoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:42.356023+00:00
-- url     : https://prove2.me/submissions/36b3ece3-74ca-462d-928e-dace4eac0cc3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded

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
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) :
    lowIndex (T.zcoeff (x * y)) ρ = lowIndex (T.zcoeff x) ρ + lowIndex (T.zcoeff y) ρ :=
  (T.gaussNorm_lowIndex_zcoeff_mul hρ0 hρ1 hx hy hx0 hy0).2
end GroundTheory.PAdicHodge.TeichLift
