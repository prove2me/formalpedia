-- Prove2me | solution 2 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_teichmullerAdic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:44.607636+00:00
-- url     : https://prove2.me/submissions/b1dad71b-1367-4d93-a626-c27590d164bf

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_Ideal_continuous_of_map_le
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_span_teichmuller

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
theorem _root_.solution (ϖ : 𝒪♭) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ) (φ) := by
  refine Ideal.continuous_of_map_le (φ) ?_
  rw [map_frobeniusEquiv_span_teichmuller, Ideal.span_singleton_le_span_singleton]
  exact map_dvd (teichmuller p) (dvd_pow_self ϖ hp.out.ne_zero)
end GroundTheory.PAdicHodge.AInf
