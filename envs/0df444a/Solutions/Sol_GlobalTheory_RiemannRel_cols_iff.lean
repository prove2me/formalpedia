-- Prove2me | solution 1 for GlobalTheory.RiemannRel.cols_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:48.978893+00:00
-- url     : https://prove2.me/submissions/9a5210af-39b7-4aea-9900-f064db4ccc4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Theorems.Thm_GlobalTheory_RiemannRel_of_cols_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
theorem _root_.solution (h τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → Fin g → ℂ) :
    (∀ k, h *ᵥ a k = Pi.single k 1 ∧ h *ᵥ b k = τ *ᵥ Pi.single k 1) ↔
      h * (Matrix.of fun i j => a j i) = 1 ∧ τ = h * (Matrix.of fun i j => b j i) := by
  constructor
  · intro H
    constructor
    · ext i j
      have := congrFun (H j).1 i
      simp only [mulVec, dotProduct] at this
      simp [mul_apply, this, one_apply, Pi.single_apply]
    · ext i j
      have := congrFun (H j).2 i
      rw [mulVec_single_one] at this
      simp only [mulVec, dotProduct] at this
      simp [mul_apply, this]
  · rintro ⟨h1, rfl⟩ k
    constructor
    · rw [← of_cols_mulVec a k, mulVec_mulVec, h1, one_mulVec]
    · rw [← mulVec_mulVec, of_cols_mulVec]
end GlobalTheory.RiemannRel
