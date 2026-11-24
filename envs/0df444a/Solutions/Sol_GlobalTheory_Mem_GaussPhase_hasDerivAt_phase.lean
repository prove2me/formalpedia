-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.hasDerivAt_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:17:26.419843+00:00
-- url     : https://prove2.me/submissions/4be5bb17-6cc4-4645-b64e-4ef3a58ec03d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_differentiableAt_det
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_differentiableAt_inv_apply
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_hasDerivAt_dot
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_hasDerivAt_mulVec
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_dot_symm
import Theorems.Thm_GlobalTheory_DifferentiableDet_differentiableAt_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace GlobalTheory.Mem.GaussPhase
theorem _root_.solution (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ)
    (x y : σ → ℂ) (t : ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hu : IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det) :
    let w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x)
    let u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s
    HasDerivAt (fun s : ℝ => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s)) (u t ⬝ᵥ w t) t := by
  intro w u
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  set M : ℝ → Matrix σ σ ℂ := fun s => 1 - ((s : ℂ) ^ 2) • (T * S) with hMdef
  have hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := by
    intro i j
    simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (differentiableAt_const _).fun_sub ((hof.differentiableAt.fun_pow 2).mul_const _)
  have hne : (M t).det ≠ 0 := hu.ne_zero
  have hev : ∀ᶠ s in nhds t, (M s).det ≠ 0 :=
    (differentiableAt_det M t hM).continuousAt.eventually_ne hne
  have hwd : DifferentiableAt ℝ w t := by
    refine differentiableAt_pi.mpr fun i => ?_
    change DifferentiableAt ℝ (fun s => ∑ k, (M s)⁻¹ i k * (y k + (s : ℂ) * (T *ᵥ x) k)) t
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_inv_apply M t hM hne i k).fun_mul
        ((differentiableAt_const _).fun_add (hof.differentiableAt.mul_const _))
  obtain ⟨w', hw⟩ : ∃ w', HasDerivAt w w' t := ⟨_, hwd.hasDerivAt⟩
  have hU : HasDerivAt u ((t : ℂ) • S *ᵥ w' + S *ᵥ w t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec S hw)).const_add x
    simpa only [one_smul] using this
  set u' := (t : ℂ) • S *ᵥ w' + S *ᵥ w t with hu'
  have hkey : ∀ s, (M s).det ≠ 0 → w s = y + (s : ℂ) • T *ᵥ u s := by
    intro s hs
    have h1 : M s *ᵥ w s = y + (s : ℂ) • T *ᵥ x := by
      change M s *ᵥ ((M s)⁻¹ *ᵥ _) = _
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]
    simp only [hMdef, sub_mulVec, one_mulVec, smul_mulVec] at h1
    simp only [u, mulVec_add, mulVec_smul, mulVec_mulVec, smul_add, smul_smul]
    rw [← add_assoc, ← h1, pow_two, sub_add_cancel]
  have hw2 : HasDerivAt w ((t : ℂ) • T *ᵥ u' + T *ᵥ u t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec T hU)).const_add y
    simp only [one_smul] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs using hkey s hs
  have hw' : w' = (t : ℂ) • T *ᵥ u' + T *ᵥ u t := hw.unique hw2
  have hx : x = u t - (t : ℂ) • S *ᵥ w t := by simp [u]
  have hy : y = w t - (t : ℂ) • T *ᵥ u t := by rw [eq_sub_iff_add_eq]; exact (hkey t hne).symm
  have hmain := (hof.div_const 2).fun_mul ((hasDerivAt_dot x hw).fun_add (hasDerivAt_dot y hU))
  refine hmain.congr_deriv ?_
  have e1 : x ⬝ᵥ w t = u t ⬝ᵥ w t - t * (w t ⬝ᵥ S *ᵥ w t) := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e2 : y ⬝ᵥ u t = u t ⬝ᵥ w t - t * (u t ⬝ᵥ T *ᵥ u t) := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul, dotProduct_comm]
  have e3 : x ⬝ᵥ w' = u t ⬝ᵥ w' - t * (w t ⬝ᵥ S *ᵥ w') := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e4 : y ⬝ᵥ u' = w t ⬝ᵥ u' - t * (u t ⬝ᵥ T *ᵥ u') := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul]
  have e5 : w t ⬝ᵥ u' = t * (w t ⬝ᵥ S *ᵥ w') + w t ⬝ᵥ S *ᵥ w t := by
    rw [hu', dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e6 : u t ⬝ᵥ w' = t * (u t ⬝ᵥ T *ᵥ u') + u t ⬝ᵥ T *ᵥ u t := by
    conv_lhs => rw [hw']
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4, e5, e6]
  ring
end GlobalTheory.Mem.GaussPhase
