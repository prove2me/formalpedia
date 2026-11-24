-- Prove2me | solution 1 for GlobalTheory.ContinuousHomDifferentiable.continuous_hom_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:50.596963+00:00
-- url     : https://prove2.me/submissions/f459ab2e-ec37-4b59-823d-56b81b4927b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousHomDifferentiable
import Theorems.Thm_GlobalTheory_ContinuousHomDifferentiable_exists_integral_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ContinuousHomDifferentiable
open intervalIntegral
namespace GlobalTheory.ContinuousHomDifferentiable
theorem _root_.solution :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ (0 : ℝ) = (1 : ℂ) →
      (∀ (s t : ℝ), χ (s + t) = χ s * χ t) → Differentiable ℝ χ := by
  intro χ hc h0 hmul
  obtain ⟨δ, hδ⟩ := exists_integral_ne_zero χ hc h0
  set c : ℂ := ∫ x in (0:ℝ)..δ, χ x with hcdef
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, χ x with hF
  have hFd : Differentiable ℝ F := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have key : ∀ s, χ s = c⁻¹ * (F (s + δ) - F s) := by
    intro s
    have e1 : χ s * c = ∫ x in (0:ℝ)..δ, χ (s + x) := by
      rw [hcdef, ← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      rw [hmul]
    have e2 : (∫ x in (0:ℝ)..δ, χ (s + x)) = ∫ x in s..s + δ, χ x := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) s]
      simp
    have e3 : F (s + δ) - F s = ∫ x in s..s + δ, χ x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [e3, ← e2, ← e1]
    field_simp
  have hfun : χ = fun s => c⁻¹ * (F (s + δ) - F s) := funext key
  rw [hfun]
  fun_prop
end GlobalTheory.ContinuousHomDifferentiable
