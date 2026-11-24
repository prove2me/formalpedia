-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mu_eq_xi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:34.974355+00:00
-- url     : https://prove2.me/submissions/8ce8f601-4db3-49b2-b8f1-9a7be91d50ad

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_mu

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
theorem _root_.solution (ε : 𝒪♭) : mu ε = xi ε * (φ).symm (mu ε) := by
  rw [frobeniusEquiv_symm_mu, xi, geom_sum_mul, ← map_pow, frobeniusEquiv_symm_pow_p, mu]
end GroundTheory.PAdicHodge.AInf
