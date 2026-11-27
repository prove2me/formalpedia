-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_teichmullerAdic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:36.803323+00:00
-- url     : https://prove2.me/submissions/7f299572-89e1-4172-bcb2-aa6e49b1ccaa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_teichmullerAdicTopology_eq
import Theorems.Thm_Ideal_continuous_of_map_le
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_symm_span_teichmuller_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_pow_ne_zero_of_norm
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_pow_p_lt_one

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
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ)
      (φ).symm := by
  have h := Ideal.continuous_of_map_le (φ).symm (map_frobeniusEquiv_symm_span_teichmuller_pow ϖ).le
  rwa [← teichmullerAdicTopology, ← teichmullerAdicTopology,
    teichmullerAdicTopology_eq (ϖ ^ p) ϖ (pow_ne_zero_of_norm ϖ hϖ0) (norm_pow_p_lt_one ϖ hϖ1)
      hϖ0 hϖ1] at h
end GroundTheory.PAdicHodge.AInf
