-- Prove2me | solution 2 for GroundTheory.PAdicHodge.AInf.eq_xi_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:49.179748+00:00
-- url     : https://prove2.me/submissions/c397379f-b1ce-4c7b-93cc-498b50c5e1af

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mu_eq_xi_mul
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_mu_ne_zero

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
theorem _root_.solution {ε : 𝒪♭} (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {x : AInf K p}
    (h : x * (φ).symm (mu ε) = mu ε) : x = xi ε := by
  have := mul_right_cancel₀ (frobeniusEquiv_symm_mu_ne_zero hζ)
    (h.trans (mu_eq_xi_mul ε))
  exact this
end GroundTheory.PAdicHodge.AInf
