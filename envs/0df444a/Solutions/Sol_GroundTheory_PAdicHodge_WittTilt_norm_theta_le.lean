-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.norm_theta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:38.10851+00:00
-- url     : https://prove2.me/submissions/3d4709d1-2c6f-4a09-b463-86644be10fbd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_convergesAt_zcoeff_incl
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_zcoeff_incl_natCast
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_p_pos
import Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_p_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_eq_teichmullerSeries_iff
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq
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
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
variable [CharZero K]
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution (x : AInf K p) :
    ‖((θ x : 𝒪) : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 x) := by
  set r₀ := ‖(p : K)‖ with hr₀
  set G := gn K p r₀ (algebraMap (AInf K p) 𝔸 x) with hG
  have hr0 : 0 < r₀ := norm_p_pos
  have hr1 : r₀ < 1 := norm_p_lt_one
  have key : ∀ n : ℕ, ‖((θ x : 𝒪) : K)‖ ≤ max G (r₀ ^ (n + 1)) := by
    intro n
    obtain ⟨d, hd⟩ := (WittVector.eq_teichmullerSeries_iff (tcoeff x) x).1
      (WittVector.teichmullerSeries_coeff_eq x).symm n
    have hθ : ((θ x : 𝒪) : K) = ∑ i ∈ Finset.Iic n,
        ((PreTilt.untilt (tcoeff x i) : 𝒪) : K) * (p : K) ^ i + (p : K) ^ (n + 1) * ((θ d : 𝒪) : K) := by
      have e := congrArg (fun y => ((θ y : 𝒪) : K)) (eq_add_of_sub_eq hd)
      simp only [map_add, map_sum, map_mul, map_pow, map_natCast, fontaineTheta_teichmuller] at e
      push_cast at e
      rw [e, add_comm]
    rw [hθ]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (gn_nonneg hr0 _) fun i _ => ?_
      rw [norm_mul, norm_pow, ← preTilt_norm_def]
      have := (convergesAt_zcoeff_incl x hr0 hr1).le_gaussNorm (i : ℤ)
      rw [zcoeff_incl_natCast, norm_algebraMap_preTilt, zpow_natCast] at this
      rw [hG, gn_algebraMap]
      exact this
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (mem_normInteger.1 (θ d).2)
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (lt_of_le_of_lt (gn_nonneg hr0 _) hlt) hr1
  have h2 : r₀ ^ (n + 1) < ‖((θ x : 𝒪) : K)‖ :=
    (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ n)).trans_lt hn
  exact lt_irrefl _ ((key n).trans_lt (max_lt hlt h2))
end GroundTheory.PAdicHodge.WittTilt
