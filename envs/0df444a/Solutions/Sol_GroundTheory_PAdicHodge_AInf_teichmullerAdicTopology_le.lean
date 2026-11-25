-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:38.898581+00:00
-- url     : https://prove2.me/submissions/5608afea-34a4-46ea-9e81-09b616f74ebd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_span_teichmuller_pow_le

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
theorem _root_.solution (ϖ ϖ' : 𝒪♭) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0) :
    teichmullerAdicTopology (K := K) ϖ ≤ teichmullerAdicTopology ϖ' := by
  rw [teichmullerAdicTopology, teichmullerAdicTopology, le_iff_nhds]
  intro x
  rw [((Ideal.span {teichmuller p ϖ'}).hasBasis_nhds_adic x).ge_iff]
  intro n _
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (pow_pos (norm_pos_iff.2 hϖ0') n) hϖ1
  exact ((Ideal.span {teichmuller p ϖ}).hasBasis_nhds_adic x).mem_iff.2
    ⟨m, trivial, Set.image_mono (span_teichmuller_pow_le hm.le)⟩
end GroundTheory.PAdicHodge.AInf
