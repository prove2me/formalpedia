-- Prove2me | solution 1 for GlobalTheory.LOneLower.exists_le_norm_LFunction_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:48.793865+00:00
-- url     : https://prove2.me/submissions/41299f4c-49da-4593-ace5-88df9ebefea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Theorems.Thm_GlobalTheory_LOneLower_inv_le_norm_LFunction_one

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
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      c / (q : ℝ) ^ ((3 : ℝ) / 2) ≤ ‖LFunction χ 1‖ := by
  refine ⟨1 / 36, by norm_num, fun q _ χ h1 h2 => le_trans ?_ (inv_le_norm_LFunction_one χ h1 h2)⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have : (q : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.self_le_rpow_of_one_le hq (by norm_num)
  rw [div_div]
  gcongr
end GlobalTheory.LOneLower
