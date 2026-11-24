-- Prove2me | solution 1 for GlobalTheory.LOneLower.inv_le_norm_LFunction_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:22.111628+00:00
-- url     : https://prove2.me/submissions/836c15a6-ec3c-4596-a292-8cc43729ceda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Theorems.Thm_GlobalTheory_LOneLower_lambert_lower
import Theorems.Thm_GlobalTheory_LOneLower_compare_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (h2 : χ ^ 2 = 1) : 1 / (36 * (q : ℝ)) ≤ ‖LFunction χ 1‖ := by
  have hq : 0 < q := NeZero.pos q
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := lambert_lower h2 (M := 6 * q) (by omega)
  have h3 := compare_one χ hχ (α := (((6 * q : ℕ) : ℝ) ^ 2)⁻¹) (by positivity)
  rw [norm_sub_rev] at h3
  have h4 := (norm_sub_norm_le _ _).trans h3
  rw [norm_mul, Complex.norm_real, inv_inv, Real.norm_of_nonneg (by positivity)] at h4
  have h5 := (sub_le_sub_right h1 _).trans h4
  push_cast at h5
  rw [div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ hq'
  nlinarith
end GlobalTheory.LOneLower
