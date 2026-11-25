-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.cyclic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:17.515601+00:00
-- url     : https://prove2.me/submissions/b958431a-54ee-4d17-843b-473b16e68a27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min y
  obtain ⟨a₁, h₁⟩ := Finite.exists_max y
  refine le_trans ?_ (h₀ a)
  have e0 := hy a₀
  have e1 := hy a₁
  have f0 := h₁ (a₀ - 1)
  have f1 := h₀ (a₁ - 1)
  have g := hX a₁ a₀
  have k : l * y (a₀ - 1) ≤ l * y a₁ := mul_le_mul_of_nonneg_left f0 (by linarith)
  have k2 : 0 ≤ (l * l - 1) * y a₀ := by rw [← e0] at g; nlinarith
  have k3 : 0 < l * l - 1 := by nlinarith
  exact (mul_nonneg_iff_of_pos_left k3).1 k2
end GlobalTheory.FlowProgramme
