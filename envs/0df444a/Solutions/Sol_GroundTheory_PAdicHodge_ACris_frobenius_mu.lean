-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.frobenius_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:21.925221+00:00
-- url     : https://prove2.me/submissions/5c45ad25-e2fc-4716-8de9-ebe7b0135f76

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_teichmuller


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
theorem _root_.solution (ε : 𝒪♭) : φ (AInf.mu (K := K) ε) = (1 + AInf.mu ε) ^ p - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, add_sub_cancel]
end GroundTheory.PAdicHodge.ACris
