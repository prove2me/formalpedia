-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_symm_span_teichmuller_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:15.557151+00:00
-- url     : https://prove2.me/submissions/02ea9fc8-521f-49f7-a57c-4ffb62c23b90

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_teichmuller


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
    Ideal.map (φ).symm (Ideal.span {(teichmuller p (ϖ ^ p) : AInf K p)}) =
      Ideal.span {(teichmuller p ϖ : AInf K p)} := by
  rw [Ideal.map_span, Set.image_singleton, ← WittVector.frobeniusEquiv_teichmuller,
    RingEquiv.symm_apply_apply]
end GroundTheory.PAdicHodge.AInf
