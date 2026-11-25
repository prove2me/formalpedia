-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.span_teichmuller_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:28.005927+00:00
-- url     : https://prove2.me/submissions/ff1eba2d-441f-42a7-8a55-49427c68d7b1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_span_teichmuller_pow


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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ϖ ϖ' : 𝒪♭} {m n : ℕ} (h : ‖ϖ‖ ^ m ≤ ‖ϖ'‖ ^ n) :
    Ideal.span {teichmuller p ϖ} ^ m ≤ Ideal.span {(teichmuller p ϖ' : AInf K p)} ^ n := by
  rw [WittVector.span_teichmuller_pow, WittVector.span_teichmuller_pow,
    Ideal.span_singleton_le_span_singleton]
  refine map_dvd (teichmuller p) ?_
  rw [preTilt_dvd_iff_norm_le, norm_pow, norm_pow]
  exact h
end GroundTheory.PAdicHodge.AInf
