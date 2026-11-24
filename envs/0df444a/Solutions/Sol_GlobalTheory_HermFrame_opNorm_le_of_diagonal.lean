-- Prove2me | solution 1 for GlobalTheory.HermFrame.opNorm_le_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:24.763828+00:00
-- url     : https://prove2.me/submissions/8680fcf4-1416-4ba8-85ee-9d26489c2139

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_parallelogram
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_add_le
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_smul_le
import Theorems.Thm_GlobalTheory_HermFrame_le_two_mul_of_forall_scale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_le_of_selfAdjoint
import Theorems.Thm_GlobalTheory_HermFrame_IsSesq_polarisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
namespace GlobalTheory.HermFrame
theorem _root_.solution {H : Matrix n n ℂ} {G : Matrix m m ℂ} (hH : H.PosDef)
    (hG : G.PosSemidef) {F : (m → ℂ) → (m → ℂ) → Matrix n n ℂ} (hF : IsSesq F)
    (hs : ∀ ξ v w, form H (F ξ ξ *ᵥ v) w = form H v (F ξ ξ *ᵥ w)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ v, ‖form H (F ξ ξ *ᵥ v) v‖ ≤ C * gnorm G ξ ^ 2 * gnorm H v ^ 2) (ξ η : m → ℂ) :
    opNorm H H (F ξ η) ≤ 2 * C * gnorm G ξ * gnorm G η := by
  have hH' := hH.posSemidef
  have h1 : ∀ x, opNorm H H (F x x) ≤ C * gnorm G x ^ 2 := fun x =>
    opNorm_le_of_selfAdjoint hH' (hs x) (by positivity) (h x)
  have h2 : ∀ (c : ℂ) x, ‖c‖ = 1 → opNorm H H (c • F x x) ≤ C * gnorm G x ^ 2 := fun c x hc =>
    (opNorm_smul_le hH hH' c _).trans (by rw [hc, one_mul]; exact h1 x)
  have h3 : ∀ x y, opNorm H H (F x y) ≤ C * (gnorm G x ^ 2 + gnorm G y ^ 2) := fun x y => by
    rw [hF.polarisation x y]
    refine (opNorm_smul_le hH hH' _ _).trans ?_
    have a := (opNorm_add_le hH hH' _ _).trans (add_le_add
      ((opNorm_add_le hH hH' _ _).trans (add_le_add (h1 (x + y)) (h2 (-1) (x - y) (by simp))))
      ((opNorm_add_le hH hH' _ _).trans (add_le_add (h2 I (x + I • y) (by simp))
        (h2 (-I) (x - I • y) (by simp)))))
    have b1 := gnorm_parallelogram hG x y
    have b2 := gnorm_parallelogram hG x (I • y)
    rw [gnorm_smul hG I, norm_I, one_mul] at b2
    rw [← mul_add, ← mul_add, b1, b2] at a
    have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [this]; linarith
  refine le_two_mul_of_forall_scale hC (gnorm_nonneg _ _) (gnorm_nonneg _ _) fun s hs => ?_
  have hq : 0 < √s := Real.sqrt_pos.2 hs
  have := h3 ((√s : ℂ) • ξ) ((((√s)⁻¹ : ℝ) : ℂ) • η)
  rw [hF.smul_left, hF.smul_right, gnorm_smul hG,
    gnorm_smul hG, conj_ofReal, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hq.ne', ofReal_one,
    one_smul, norm_real, norm_real, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, inv_pow, Real.sq_sqrt hs.le] at this
  rwa [div_eq_inv_mul _ s]
end GlobalTheory.HermFrame
