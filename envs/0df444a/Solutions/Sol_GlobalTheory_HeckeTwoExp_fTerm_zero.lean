-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.fTerm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:24.612483+00:00
-- url     : https://prove2.me/submissions/c9b200da-d8cb-4aed-b38d-0ec3f6d1bcac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinWeightTwoQExpansion
import Theorems.Thm_GlobalTheory_HeckeTwoExp_hTrans_zero
import Theorems.Thm_GlobalTheory_HeckeTwoExp_abs_norm_eq_prod
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution [IsTotallyReal F] {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b ν : F} (hb : b ≠ 0) (hν : ν ≠ 0) :
    fTerm 0 z b ν = if ∀ τ : Emb F, 0 < τ (ν * b) then
      (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) * qPow (ν * b) z
      else 0 := by
  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  unfold fTerm
  simp only [hTrans_zero _ _ (hyτ _)]
  split_ifs with hc
  · have hc' : ∀ τ : Emb F, 0 < τ ν * (τ b * (z τ).im) := fun τ => by
      have := hc τ; rw [map_mul] at this; rw [← mul_assoc]; exact mul_pos this (hz τ)
    rw [Finset.prod_congr rfl fun τ _ => by rw [if_pos (hc' τ)]]
    rw [abs_norm_eq_prod, qPow, Finset.mul_sum, Complex.exp_sum]
    rw [show ((-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ)) *
        ∏ x : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((x (ν * b) : ℂ) * z x)) =
        ∏ τ : Emb F, ((-4 * (Real.pi : ℂ) ^ 2) * ((|τ ν| : ℝ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (ν * b) : ℂ) * z τ))) by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; congr 1
    conv_rhs => rw [← Complex.re_add_im (z τ)]
    simp only [map_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * (τ ν : ℂ) * (τ b : ℂ) * ((z τ).im : ℂ)) * I_sq
  · push_neg at hc
    obtain ⟨τ, hτ⟩ := hc
    have : ¬ 0 < τ ν * (τ b * (z τ).im) := by
      rw [map_mul] at hτ; rw [← mul_assoc]; exact not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hτ (hz τ).le)
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg this, mul_zero])
end GlobalTheory.HeckeTwoExp
