-- Prove2me | solution 1 for GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:53.909977+00:00
-- url     : https://prove2.me/submissions/3874b71b-36b0-4373-84a5-2c0d2239df26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Theorems.Thm_GlobalTheory_eq_zero_of_cube_fourierCoeff_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) := by
  intro H g f hf hper h0
  funext w
  have hc := hf.continuous
  have := eq_zero_of_cube_fourierCoeff_eq_zero (A := fun x => f ((fun i => (x i : ℂ)) + w))
    (by fun_prop) (fun i x => by
      rw [← hper i ((fun i => (x i : ℂ)) + w)]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp; ring
      · simp [hj])
    (fun m => by rw [H g f hf hper m w, h0 m, mul_zero]) 0
  have h1 : (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ)) + w = w := by
    funext j; simp
  rw [h1] at this
  exact this
end GlobalTheory
