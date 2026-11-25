-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:46.693789+00:00
-- url     : https://prove2.me/submissions/2f869c52-3995-4e5f-b084-caf2b5146cad

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_untilt_frobeniusEquiv_symm_pow_p

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
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : θ (xi ε) = 0 := by
  rw [xi, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller]
  have h := mul_geom_sum (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε)) p
  rw [untilt_frobeniusEquiv_symm_pow_p hε, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ)
end GroundTheory.PAdicHodge.AInf
