-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6d971951-f2ce-50af-a4b0-a5c685c5ebee

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow

set_option autoImplicit false

theorem solution
    {ι : Type*} [Fintype ι] {P : Type*} (e : ι → ℂ) (j : ι → ℕ) (c : ι → P → ℂ)
    (hinj : Function.Injective fun i => (e i, j i))
    (θ₀ : ℝ) (F R : ℝ → P → ℂ)
    (hF : ∀ p : P, ∀ y : ℝ, 0 < y → y ≤ 1 → F y p = ∑ i, c i p * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) + R y p)
    (hR : ∀ p : P, ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖R y p‖ ≤ K * y ^ θ₀)
    (hray : ∀ p : P, ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖F y₁ p‖ ≤ C * y₁ ^ θ₀) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by
  intro i hi
  funext p
  exact LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow e j (fun k => c k p)
    hinj θ₀ (fun y => F y p) (fun y => R y p) (hF p) (hR p) (hray p) i hi

end S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow (solution)
