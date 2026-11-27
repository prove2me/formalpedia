-- Prove2me | solution 2 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:47.269804+00:00
-- url     : https://prove2.me/submissions/f7537579-24c0-4906-8a1e-1038c7dfe418

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_weakTopology_eq_adicTopology
import Theorems.Thm_Ideal_continuous_of_map_le
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_span_p_teichmuller
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
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ) := by
  have h := Ideal.continuous_of_map_le (φ) (map_frobeniusEquiv_span_p_teichmuller ϖ).le
  rwa [← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1,
    ← weakTopology_eq_adicTopology (ϖ ^ p) (pow_ne_zero_of_norm ϖ hϖ0)
      (norm_pow_p_lt_one ϖ hϖ1)] at h
end GroundTheory.PAdicHodge.AInf
