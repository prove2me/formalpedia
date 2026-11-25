-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phiZero_logTermZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:21.357813+00:00
-- url     : https://prove2.me/submissions/d03854d2-851e-46e5-a428-2c423750d18d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_logTermZero
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_phiZero


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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phiZero K p (logTermZero hx n) = logTermZero hφ n := by
  apply Subtype.ext
  rw [coe_phiZero, coe_logTermZero, coe_logTermZero, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, phiAway_dpow]
end GroundTheory.PAdicHodge.ACris
