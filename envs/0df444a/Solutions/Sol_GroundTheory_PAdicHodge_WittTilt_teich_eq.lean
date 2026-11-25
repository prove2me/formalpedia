-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.teich_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:31.77881+00:00
-- url     : https://prove2.me/submissions/3e094021-09fd-4797-952c-6324dc0a95d3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_teichLift_red
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_iterate_frobeniusEquiv_symm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_span_pow_anti
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_sub_pow_mem


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
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (a : K♭) : (teichLift K p).teich a = teichmuller p a := by
  haveI := (teichLift K p).isAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := (teichLift K p).I) _ fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, (teichLift K p).I_pow]
  have h := (teichLift K p).teich_sub_pow_mem a n
    (teichmuller p ((((frobeniusEquiv K♭ p).symm : K♭ →+* K♭))^[n] a))
    (by rw [teichLift_red, teichmuller_coeff_zero])
  rw [← map_pow, TeichLift.iterate_frobeniusEquiv_symm_pow] at h
  exact (teichLift K p).span_pow_anti (Nat.le_succ n) h
end GroundTheory.PAdicHodge.WittTilt
