-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.algebraMap_acrisZero_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:28.976057+00:00
-- url     : https://prove2.me/submissions/8c07cd26-a172-43b8-af4e-5591927eb650

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonDom

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
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (w : AInf K p) :
    algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) w) =
      algebraMap (AInf K p) (ACris K p) w :=
  rfl
end GroundTheory.PAdicHodge.WittTilt
