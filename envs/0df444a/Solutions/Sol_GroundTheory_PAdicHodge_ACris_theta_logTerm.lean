-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_logTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:57.209222+00:00
-- url     : https://prove2.me/submissions/e832d6e3-e086-4f48-9710-8f7be1999824

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_thetaZero_dpow
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_of


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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    theta K p (logTerm hx n) = 0 := by
  rw [logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    theta_of, logTermZero, map_mul, dpowZero, thetaZero_dpow hx n.succ_ne_zero, mul_zero]
end GroundTheory.PAdicHodge.ACris
