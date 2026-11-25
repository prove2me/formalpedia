-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.constantCoeff_frobeniusEquiv_symm_pow_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:24.495654+00:00
-- url     : https://prove2.me/submissions/92d4e340-9183-4482-afdc-4e1e518b0106

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
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
theorem _root_.solution (ε : 𝒪♭) (N : ℕ) :
    WittVector.constantCoeff (((φ).symm ^ N) (mu ε) : AInf K p) =
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1 := by
  rw [frobeniusEquiv_symm_pow_mu, map_sub, map_one]
  exact congrArg (· - 1) (teichmuller_coeff_zero p _)
end GroundTheory.PAdicHodge.AInf
