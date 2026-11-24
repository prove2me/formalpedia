-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobenius_pow_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:13.092744+00:00
-- url     : https://prove2.me/submissions/96520ad1-a5ec-489f-817c-4435a9260e40

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_pow_teichmuller


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ n) (mu ε)) = 0 := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_pow_teichmuller, map_sub, map_one,
    fontaineTheta_teichmuller, map_pow, hε, one_pow, sub_self]
end GroundTheory.PAdicHodge.AInf
