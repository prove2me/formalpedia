-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_coeff_sub_le_of_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:11.695199+00:00
-- url     : https://prove2.me/submissions/a543b085-8398-4d98-89de-63dcf8eddd13

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_le_of_mem_span_pow

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
theorem _root_.solution (ϖ : 𝒪♭) (N : ℕ) (x y : AInf K p)
    (hd : x - y ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ (N + N)) :
    ∀ i < N, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ N :=
  (norm_coeff_sub_le_iff ϖ N N x y).2 (norm_coeff_le_of_mem_span_pow ϖ N _ hd)
end GroundTheory.PAdicHodge.AInf
