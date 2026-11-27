-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.kerThetaFrob_eq_span_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:50:20.864119+00:00
-- url     : https://prove2.me/submissions/c8e67437-3194-4c61-a391-dd74868557e7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobenius_pow_mul_mu
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_kerThetaFrob
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_mu_of_forall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    kerThetaFrob K p = Ideal.span {mu ε} := by
  refine le_antisymm (fun a ha => mem_span_mu_of_forall hε hζ (mem_kerThetaFrob.1 ha)) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_kerThetaFrob]
  intro n
  simpa using fontaineTheta_frobenius_pow_mul_mu (K := K) hε 1 n
end GroundTheory.PAdicHodge.AInf
