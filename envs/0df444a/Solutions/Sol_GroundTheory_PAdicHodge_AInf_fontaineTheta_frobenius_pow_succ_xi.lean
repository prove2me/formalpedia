-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_frobenius_pow_succ_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:56.56113+00:00
-- url     : https://prove2.me/submissions/84103be4-94bc-4c6b-9de6-0970fb86b138

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_xi
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
    θ ((φ ^ (n + 1)) (xi ε)) = p := by
  rw [pow_succ, RingAut.mul_apply, frobeniusEquiv_xi, map_sum, map_sum]
  simp only [map_pow, WittVector.frobeniusEquiv_pow_teichmuller, fontaineTheta_teichmuller, hε,
    one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
end GroundTheory.PAdicHodge.AInf
