-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:20.618325+00:00
-- url     : https://prove2.me/submissions/73101cef-3802-4482-8fc2-caacdf66d993

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_span_p_pow_map
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
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (a : ACris K p) (N : ℕ) :
    ∃ c : ACrisZero K p, a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} := by
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) N a)
  refine ⟨c, ?_⟩
  have h : a - _root_.AdicCompletion.of _ _ c ∈
      (Ideal.span {(p : ACrisZero K p)} ^ N).map (algebraMap (ACrisZero K p) (ACris K p)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
    rw [← hc]
    exact sub_eq_zero.2 (_root_.AdicCompletion.evalₐ_of _ N c).symm
  rwa [span_p_pow_map, Ideal.span_singleton_pow] at h
end GroundTheory.PAdicHodge.WittTilt
