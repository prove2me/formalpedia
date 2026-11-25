-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.xi_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:29.810071+00:00
-- url     : https://prove2.me/submissions/5d16a560-a1ff-496f-acb7-a7cc73b4f789

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi

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
    (xi ε).coeff 0 = ∑ i ∈ Finset.range p, (_root_.frobeniusEquiv 𝒪♭ p).symm ε ^ i := by
  change WittVector.constantCoeff (xi ε) = _
  rw [xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow]
  exact congrArg (· ^ i) (teichmuller_coeff_zero p _)
end GroundTheory.PAdicHodge.AInf
