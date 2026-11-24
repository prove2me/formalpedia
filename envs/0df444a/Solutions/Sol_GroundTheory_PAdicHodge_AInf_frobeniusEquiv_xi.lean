-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.frobeniusEquiv_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:13.051075+00:00
-- url     : https://prove2.me/submissions/f8c68f5c-5bd7-42ad-88f6-df124b424913

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (ε : 𝒪♭) :
    φ (xi ε) = ∑ i ∈ Finset.range p, teichmuller p ε ^ i := by
  rw [xi, map_sum]
  simp only [map_pow, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]
end GroundTheory.PAdicHodge.AInf
