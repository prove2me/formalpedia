-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.coe_logTermZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:59.845548+00:00
-- url     : https://prove2.me/submissions/5a5d01ab-3937-4608-bbcd-76d4a9737fd7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_dpowZero


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
theorem _root_.solution {y : AInf K p} (hy : y ∈ RingHom.ker θ) (n : ℕ) :
    (logTermZero hy n : 𝔸) = (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) y := by
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]
end GroundTheory.PAdicHodge.ACris
