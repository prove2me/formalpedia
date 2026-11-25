-- Prove2me | solution 1 for GlobalTheory.IsSiegel.riemannTheta_eq_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:26.970712+00:00
-- url     : https://prove2.me/submissions/c982facf-f946-4469-a1eb-c8e628df36b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_integral_cexp_quadratic
import Theorems.Thm_GlobalTheory_tsum_poisson_pi_int
import Theorems.Thm_GlobalTheory_riemannThetaTerm_zero_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) (a : ι → ℝ)
    (w : ι → ℂ) :
    riemannTheta a 0 σ w = siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) *
      riemannTheta 0 a (-σ⁻¹) (σ⁻¹ *ᵥ w) := by
  have hsi : σ⁻¹.IsSymm := by rw [Matrix.IsSymm, transpose_nonsing_inv, h.isSymm.eq]
  set f : (ι → ℝ) → ℂ := fun x => cexp (2 * π * I *
    (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 + (fun i => (x i : ℂ)) ⬝ᵥ w)) with hf
  have hc : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hfn (n : ι → ℤ) (u : ι → ℝ) :
      f ((fun i => (n i : ℝ)) + u) = riemannThetaTerm u 0 σ w n := by
    simp [hf, riemannThetaTerm_def]
  have key := tsum_poisson_pi_int (f := f) (F := fun y => siegelGaussIntegral σ *
      cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) * cexp (2 * π * I *
      (((fun i => (y i : ℂ)) ⬝ᵥ (-σ⁻¹ *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ (σ⁻¹ *ᵥ w)))) hc (fun R => ?_) (fun y => ?_) ?_ a
  · simp only [hfn] at key
    rw [riemannTheta, key, riemannTheta, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have := riemannThetaTerm_add_ofReal 0 0 a (-σ⁻¹) (σ⁻¹ *ᵥ w) n
    rw [zero_add] at this
    rw [← this, riemannThetaTerm_add, riemannThetaTerm_zero_zero]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, ofReal_intCast]
    ring
  · obtain ⟨c, hc0, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ι → ℝ) R).exists_bound_of_continuousOn
      hc.continuousOn
    obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : ι → ℝ) R).exists_bound_of_continuousOn
      (f := fun u => w + σ *ᵥ fun i => (u i : ℂ)) (Continuous.continuousOn (by
        refine continuous_const.add (continuous_pi fun i => ?_)
        simp only [mulVec, dotProduct]
        fun_prop))
    refine ⟨_, (summable_riemannThetaBound 0 hc0 S).mul_left M, fun n u hu => ?_⟩
    have hu' := mem_closedBall_zero_iff.2 hu
    have e : riemannThetaTerm u 0 σ w n =
        f u * riemannThetaTerm 0 0 σ (w + σ *ᵥ fun i => (u i : ℂ)) n := by
      rw [riemannThetaTerm_add_mulVec_ofReal h.isSymm, ← mul_assoc, hf, ← Complex.exp_add]
      simp
    rw [hfn, e, norm_mul]
    exact mul_le_mul (hM u hu') (norm_riemannThetaTerm_le 0 0 hY
      (fun i => (abs_im_apply_le_norm _ i).trans (hS u hu')) n) (norm_nonneg _)
      ((norm_nonneg _).trans (hM u hu'))
  · have := h.integral_cexp_quadratic (w - fun i => (y i : ℂ))
    rw [mul_assoc (siegelGaussIntegral σ), ← Complex.exp_add]
    convert this using 3 with x
    · rw [hf, ← Complex.exp_add, dotProduct_sub]
      congr 1
      ring
    · rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, neg_mulVec, dotProduct_neg,
        dotProduct_mulVec_comm_of_isSymm hsi w fun i => (y i : ℂ)]
      ring
  · have := (h.neg_inv.summable_norm_riemannThetaTerm 0 0 (σ⁻¹ *ᵥ w)).mul_left
      ‖siegelGaussIntegral σ * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w)))‖
    simpa only [← norm_mul, riemannThetaTerm_zero_zero, ofReal_intCast] using this
end IsSiegel
end GlobalTheory
