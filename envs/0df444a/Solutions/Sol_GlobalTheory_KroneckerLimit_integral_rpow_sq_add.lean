-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.integral_rpow_sq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:44.970802+00:00
-- url     : https://prove2.me/submissions/6863ea4d-cb09-4612-a9e1-9988398e9a8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology MeasureTheory Set
open scoped Real
namespace GlobalTheory.KroneckerLimit
private theorem integral_rpow_mul_exp_neg_sq_add_mul_eq {Y s u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * (u ^ (s - 1 / 2 - 1) * Real.exp (-(Y ^ 2 * u))) := by
  have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
      fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
    funext t
    rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
    ring
  rw [h, integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le,
    show s - 1 / 2 - 1 = (s - 1) - 1 / 2 by ring, Real.rpow_sub hu (s - 1) (1 / 2), Real.sqrt_eq_rpow u]
  ring
private theorem integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma {Y s t : ℝ} (hY : 0 < Y) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := by
  have hp : 0 < t ^ 2 + Y ^ 2 := by positivity
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp, one_div, Real.inv_rpow hp.le,
    Real.rpow_neg hp.le]
private theorem integrable_uncurry_rpow_mul_exp_neg_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    Integrable (Function.uncurry fun u t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 ^ (s - 1) * Real.exp (-((p.2 ^ 2 + Y ^ 2) * p.1)) := by
    fun_prop
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
        fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
      funext t
      rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
      ring
    rw [h]
    exact (integrable_exp_neg_mul_sq hu).const_mul _
  · have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 / 2 - 1) (b := Y ^ 2)
      (by linarith) one_pos (by positivity)
    simp only [Real.rpow_one, neg_mul] at hI
    refine IntegrableOn.congr_fun (hI.const_mul √π) (fun u hu => ?_) measurableSet_Ioi
    have hu' : 0 < u := hu
    try dsimp only
    rw [← integral_rpow_mul_exp_neg_sq_add_mul_eq hu']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    try dsimp only
    rw [Real.norm_of_nonneg (by positivity)]
end GlobalTheory.KroneckerLimit
end

set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    ∫ t : ℝ, (t ^ 2 + Y ^ 2) ^ (-s) = betaConst s * Y ^ (1 - 2 * s) := by
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
  have hK := integrable_uncurry_rpow_mul_exp_neg_sq_add hY hs
  have hswap := integral_integral_swap hK
  have hB : ∫ u in Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * ((1 / Y ^ 2) ^ (s - 1 / 2) * Real.Gamma (s - 1 / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => integral_rpow_mul_exp_neg_sq_add_mul_eq (s := s) (Y := Y) hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
  have hA : ∀ t : ℝ, ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := fun t => integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma hY (by linarith)
  simp only [hA, hB, integral_mul_const] at hswap
  have hY2 : (1 / Y ^ 2) ^ (s - 1 / 2) = Y ^ (1 - 2 * s) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le,
      ← Real.rpow_neg hY.le]
    congr 1
    push_cast
    ring
  rw [hY2] at hswap
  unfold betaConst
  rw [show √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * Y ^ (1 - 2 * s) =
      √π * (Y ^ (1 - 2 * s) * Real.Gamma (s - 1 / 2)) / Real.Gamma s by ring, hswap,
    mul_div_assoc, div_self hΓ.ne', mul_one]
end GlobalTheory.KroneckerLimit
