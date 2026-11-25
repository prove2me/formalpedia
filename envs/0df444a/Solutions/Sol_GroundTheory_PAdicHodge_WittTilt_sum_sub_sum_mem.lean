-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.sum_sub_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:36.274012+00:00
-- url     : https://prove2.me/submissions/44fee20e-a097-4448-8049-86c7286a1428

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonDom
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65
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
attribute [local simp] P2M_GroundTheory_PAdicHodge_WittTilt_teichLift___5f5b1ec71a65



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {ρ : ℝ}
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (C : ℕ → R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) :
    ∑ i ∈ Finset.range (d + 1), C i * a ^ i * b ^ (d - i) -
      ∑ i ∈ Finset.range (d + 1), C i * a' ^ i * b' ^ (d - i) ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_sum, map_mul, map_pow, Ideal.Quotient.eq.2 ha, Ideal.Quotient.eq.2 hb]
end GroundTheory.PAdicHodge.WittTilt
