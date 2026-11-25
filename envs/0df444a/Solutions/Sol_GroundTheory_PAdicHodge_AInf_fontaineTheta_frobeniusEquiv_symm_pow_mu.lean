-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobeniusEquiv_symm_pow_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:25.951681+00:00
-- url     : https://prove2.me/submissions/99d0af4a-6001-4cfb-8371-066a0f78c327

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_pow_mu

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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (ε : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (mu ε)) = PreTilt.untilt (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) ε) - 1 := by
  rw [frobeniusEquiv_symm_pow_mu, map_sub, map_one, fontaineTheta_teichmuller]
end GroundTheory.PAdicHodge.AInf
