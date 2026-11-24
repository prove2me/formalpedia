-- Prove2me | solution 1 for GlobalTheory.MatrixGaussian.integral_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:35.676524+00:00
-- url     : https://prove2.me/submissions/af876e3a-2ce0-4c48-bed3-3e47eb2dcf73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart
import Theorems.Thm_GlobalTheory_MatrixGaussian_exists_congr_diagonal
import Theorems.Thm_GlobalTheory_MatrixGaussian_gaussian_diagonal
import Theorems.Thm_GlobalTheory_MatrixGaussian_map_mulVec_volume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.MatrixGaussian
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MatrixGaussian
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  obtain ⟨M, d, hM, hd, hMA⟩ := exists_congr_diagonal A hA
  obtain ⟨hi, he⟩ := gaussian_diagonal d hd
  have hn : 0 < normSq M.det := normSq_pos.2 hM
  have hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det := by
    rw [← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  have hd0 : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
    have := hd i
    simp [h] at this
  have hA0 : A.det ≠ 0 := fun h => hd0 (by rw [hdet, h, mul_zero])
  have hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z := fun z => by
    rw [← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) := by fun_prop
  have hcM : Continuous fun z : ι → ℂ => M *ᵥ z := by fun_prop
  have hmap := map_mulVec_volume M hM
  refine ⟨hA0, ?_, ?_⟩
  · have h := (integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2
      (by simpa only [Function.comp_def, hcomp] using hi)
    rw [hmap] at h
    exact (integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h
  · have h := integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable
    simp only [hcomp] at h
    rw [hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul,
      mul_inv, ofReal_inv] at h
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h
end GlobalTheory.MatrixGaussian
