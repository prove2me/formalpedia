-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.hTrans_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:47.52186+00:00
-- url     : https://prove2.me/submissions/9b1a8240-6ffc-4c09-9071-e6b97849b097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformZeroEq
import Theorems.Thm_GlobalTheory_HeckeTwo_phi_ofReal_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution (σ : ℂ) (y : ℝ) (hy : y ≠ 0) :
    hTrans σ 0 y = cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  have h0 : hTrans σ 0 y = ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) := by simp [hTrans]
  have h1 : cConst σ = ∫ t : ℝ, phi σ ((t : ℂ) + I) := by simp [cConst, hTrans]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) y
  have h2 : (∫ u : ℝ, phi σ (((y * u : ℝ) : ℂ) + (y : ℂ) * I)) =
      (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * ∫ u : ℝ, phi σ ((u : ℂ) + I) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext u
    rw [← phi_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [h2] at hsub
  have hya : (|y| : ℝ) ≠ 0 := abs_ne_zero.mpr hy
  have hyc : ((|y| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hya
  have h3 : (∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I)) =
      ((|y| : ℝ) : ℂ) * ((((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) *
        ∫ u : ℝ, phi σ ((u : ℂ) + I)) := by
    rw [hsub, abs_inv, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hyc, one_mul]
  have hc : ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) = ((|y| : ℝ) : ℂ)⁻¹ * ((|y| : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [show (-1 - 2 * σ) = -1 + -2 * σ by ring, cpow_add _ _ hyc, cpow_neg_one]
  rw [h0, h3, ← h1, hc]
  field_simp
end GlobalTheory.HeckeTwo
