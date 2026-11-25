-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mem_span_teichmuller_pow_iff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:06.295889+00:00
-- url     : https://prove2.me/submissions/9604ec3a-90ac-45f3-859e-144c8e7e33dd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_mem_span_teichmuller_pow_iff


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
theorem _root_.solution (ϖ : 𝒪♭) (n : ℕ) (d : AInf K p) :
    d ∈ Ideal.span {teichmuller p ϖ} ^ n ↔ ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ (n * p ^ i) := by
  rw [WittVector.mem_span_teichmuller_pow_iff]
  simp_rw [preTilt_dvd_iff_norm_le, norm_pow]
end GroundTheory.PAdicHodge.AInf
