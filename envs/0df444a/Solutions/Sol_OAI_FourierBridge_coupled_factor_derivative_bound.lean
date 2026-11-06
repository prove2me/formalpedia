-- Prove2me | solution 1 for OAI.FourierBridge.coupled_factor_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:13.308206+00:00
-- url     : https://prove2.me/submissions/142d2f6d-f92b-4d1b-a7b3-b9dae51f92f3

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_exp_argument_derivative_bound

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg (ENat.natCast_le_of_coe_top_le_withTop le_rfl _) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁
end OAI.FourierBridge
