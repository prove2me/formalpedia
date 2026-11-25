-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.coeff_mem_of_mem_span_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:02.473305+00:00
-- url     : https://prove2.me/submissions/5aff324a-c569-47a2-884d-12a3fa6d33f8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_mem_span_teichmuller_iff


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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution {b : R} {J : Ideal R} (hb : b ∈ J)
    {y : WittVector p R} (hy : y ∈ Ideal.span {teichmuller p b}) (i : ℕ) : y.coeff i ∈ J := by
  obtain ⟨c, hc⟩ := (WittVector.mem_span_teichmuller_iff b y).1 hy i
  rw [hc]
  exact J.mul_mem_right c (J.pow_mem_of_mem hb _ (pow_pos hp.out.pos i))
end WittVector
end GroundTheory.PAdicHodge
