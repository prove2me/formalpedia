-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:24.877496+00:00
-- url     : https://prove2.me/submissions/c85a7f95-41a1-450e-ab65-b5e195811d22

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ne_one_of_untilt_ne_one

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
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : ‖(p : K)‖ ≠ 0 := by
  intro h
  have := norm_sub_one_pow hε hζ
  rw [h, zero_pow hp.out.ne_zero, pow_eq_zero_iff (Nat.sub_ne_zero_of_lt hp.out.one_lt),
    norm_eq_zero, sub_eq_zero] at this
  exact ne_one_of_untilt_ne_one hζ this
end GroundTheory.PAdicHodge.AInf
