-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_coeff_sub_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:24:49.848109+00:00
-- url     : https://prove2.me/submissions/2e2b178b-c94f-494c-ac73-fed9de117595

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_forall_lt_sub_coeff_mem_iff
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_pow_iff_norm_le

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
theorem _root_.solution (ϖ : 𝒪♭) (k n : ℕ) (x y : AInf K p) :
    (∀ i < n, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ k) ↔ ∀ i < n, ‖(x - y).coeff i‖ ≤ ‖ϖ‖ ^ k := by
  simp_rw [← mem_span_pow_iff_norm_le]
  exact WittVector.forall_lt_sub_coeff_mem_iff _ n x y
end GroundTheory.PAdicHodge.AInf
