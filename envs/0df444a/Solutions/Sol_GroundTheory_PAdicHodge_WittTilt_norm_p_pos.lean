-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.norm_p_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:31.550007+00:00
-- url     : https://prove2.me/submissions/3333c957-2058-45aa-a6cc-2289c1e41e6d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm

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
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution : 0 < ‖(p : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
end GroundTheory.PAdicHodge.WittTilt
