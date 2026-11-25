-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.commute_of_commute_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:05.992255+00:00
-- url     : https://prove2.me/submissions/cece6996-6c29-4620-b652-637ded675576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Theorems.Thm_GlobalTheory_WeilDeligne_isNilpotent_pow_sub_one
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]
end GlobalTheory.WeilDeligne
