-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.le_of_pow_le_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:08.044858+00:00
-- url     : https://prove2.me/submissions/c999e808-1802-42c3-a81b-f3bad6a02bd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution {a b C : ℕ} (hb : 1 ≤ b) (h : ∀ k : ℕ, a ^ k ≤ C * b ^ k) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (1 : ℝ) < a / b := by rw [one_lt_div hb']; exact_mod_cast hab
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop (C : ℝ)).exists
  rw [div_pow, lt_div_iff₀ (pow_pos hb' k)] at hk
  have := h k
  have h2 : ((a : ℝ)) ^ k ≤ C * b ^ k := by exact_mod_cast this
  linarith
end GlobalTheory.FinrankGrowthBounds
