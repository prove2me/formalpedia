-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobenius_pow_mul_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:44.492525+00:00
-- url     : https://prove2.me/submissions/d5b35bd6-6735-47c9-a822-7f48eb6a4cd5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobenius_pow_mu

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
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (b : AInf K p)
    (n : ℕ) : θ ((φ ^ n) (mu ε * b)) = 0 := by
  rw [map_mul, map_mul, fontaineTheta_frobenius_pow_mu hε, zero_mul]
end GroundTheory.PAdicHodge.AInf
