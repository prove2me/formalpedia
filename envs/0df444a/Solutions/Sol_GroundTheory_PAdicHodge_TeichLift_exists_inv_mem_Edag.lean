-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_inv_mem_Edag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:10.447152+00:00
-- url     : https://prove2.me/submissions/e52a65c2-800f-48cb-86f7-cdd61bb39d24

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_zcoeff_teich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_eq_zero_of_mul_pow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_Econ
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_invSelf_mem_Econ
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_inv_convergesAt
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_eq_of_coeff_eq
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum
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



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {b : T.B} (hb : b ∈ T.Edag) (hb0 : b ≠ 0) :
    ∃ c ∈ T.Edag, b * c = 1 := by
  classical
  obtain ⟨ρ, hρ⟩ := hb
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hb0 (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  have hxc : ConvergesAt (T.zcoeff x) ρ := by
    rw [T.coeffB_eq hx, convergesAt_shift_iff ρ.2.1] at hρ; exact hρ
  have hex : ∃ k, T.coeff x k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (T.eq_of_coeff_eq (funext fun n => by rw [h n, coeff_zero_elem]))
  obtain ⟨k0, hk0, hlow⟩ : ∃ k0, T.coeff x k0 ≠ 0 ∧ ∀ i < k0, T.coeff x i = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      have := Nat.find_min hex hi; push_neg at this; exact this⟩
  have hxx' : x = T.π ^ k0 * T.tail^[k0] x := by
    have h0 : T.partialSum x (k0) = 0 := by
      simp only [partialSum, finSum]
      exact Finset.sum_eq_zero fun i hi => by
        rw [hlow i (Finset.mem_range.1 hi), T.teich_zero, mul_zero]
    have := T.sub_partialSum x (k0); rw [h0, sub_zero] at this; exact this
  have hx'0 : T.coeff (T.tail^[k0] x) 0 = T.coeff x (k0) := by
    rw [coeff_tail_iterate, zero_add]
  have hx'c : ConvergesAt (T.zcoeff (T.tail^[k0] x)) ρ := by
    have : T.zcoeff (T.tail^[k0] x) = fun k => T.zcoeff x (k + k0) := by
      funext k
      conv_rhs => rw [hxx']
      rw [T.zcoeff_π_pow_mul]
    rw [this]; exact convergesAt_shift ρ.2.1 hxc _
  have hu0 : T.coeff (T.teich (T.coeff x (k0))⁻¹ * T.tail^[k0] x) 0 = 1 := by
    rw [coeff_teich_mul, hx'0, inv_mul_cancel₀ hk0]
  have hu := T.convergesAt_zcoeff_mul ρ.2.1 ρ.2.2
    (by rw [zcoeff_teich]; exact convergesAt_pi_single _ _ _) hx'c
    (x := T.teich (T.coeff x (k0))⁻¹)
  obtain ⟨v, huv, ρ', hρ'0, hρ'1, hv⟩ := T.exists_inv_convergesAt ρ.2.1 ρ.2.2 hu hu0
  refine ⟨algebraMap Γ T.B (T.teich (T.coeff x (k0))⁻¹ * v) *
    algebraMap Γ T.B T.π ^ N * IsLocalization.Away.invSelf T.π ^ k0,
    ⟨⟨ρ', hρ'0, hρ'1⟩, ?_⟩, ?_⟩
  · refine Subring.mul_mem _ (Subring.mul_mem _ ?_
      (Subring.pow_mem _ (T.algebraMap_π_mem_Econ _) _)) (Subring.pow_mem _ (T.invSelf_mem_Econ _) _)
    rw [mem_Econ, coeffB_algebraMap]
    exact T.convergesAt_zcoeff_mul hρ'0 hρ'1
      (by rw [zcoeff_teich]; exact convergesAt_pi_single _ _ _) hv
  · have hb' : b * algebraMap Γ T.B T.π ^ N =
        algebraMap Γ T.B T.π ^ k0 * algebraMap Γ T.B (T.tail^[k0] x) := by
      rw [hx]; conv_lhs => rw [hxx']
      rw [map_mul, map_pow]
    have huv' := congrArg (algebraMap Γ T.B) huv
    rw [map_mul, map_mul, map_one] at huv'
    calc b * (algebraMap Γ T.B (T.teich (T.coeff x (k0))⁻¹ * v) *
          algebraMap Γ T.B T.π ^ N * IsLocalization.Away.invSelf T.π ^ k0)
        = (b * algebraMap Γ T.B T.π ^ N) * algebraMap Γ T.B (T.teich (T.coeff x (k0))⁻¹ * v) *
          IsLocalization.Away.invSelf T.π ^ k0 := by ring
      _ = (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ k0 *
          (algebraMap Γ T.B (T.teich (T.coeff x (k0))⁻¹) *
            algebraMap Γ T.B (T.tail^[k0] x) * algebraMap Γ T.B v) := by
          rw [hb', map_mul]; ring
      _ = 1 := by rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul, huv']
end GroundTheory.PAdicHodge.TeichLift
