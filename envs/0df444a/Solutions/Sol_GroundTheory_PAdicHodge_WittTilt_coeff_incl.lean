-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.coeff_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:58.5577+00:00
-- url     : https://prove2.me/submissions/62af97c2-6beb-4cf0-b12b-becd6316f8a0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_incl_teichmuller
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_teich_eq
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_eq_teichmullerSeries_iff
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0


attribute [local simp] GroundTheory.PAdicHodge.WittTilt.teichLift_π

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
theorem _root_.solution (x : AInf K p) (n : ℕ) :
    (teichLift K p).coeff (incl K p x) n = algebraMap 𝒪♭ K♭ (tcoeff x n) := by
  refine (teichLift K p).coeff_eq_of_mem (a := fun i => algebraMap 𝒪♭ K♭ (tcoeff x i)) ?_ n le_rfl
  have hx := (WittVector.eq_teichmullerSeries_iff (tcoeff x) x).1
    (WittVector.teichmullerSeries_coeff_eq x).symm n
  have h2 := map_dvd (incl K p) hx
  rw [map_pow, map_natCast, map_sub, map_sum] at h2
  rw [Ideal.mem_span_singleton, teichLift_π]
  convert h2 using 2
  rw [TeichLift.finSum, show Finset.range (n + 1) = Finset.Iic n by ext; simp [Nat.lt_succ_iff]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_natCast, incl_teichmuller, teich_eq, teichLift_π, mul_comm]
end GroundTheory.PAdicHodge.WittTilt
