-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.ae_affine_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:22.471174+00:00
-- url     : https://prove2.me/submissions/03576b94-6aa2-4ea2-bf51-e6bf5b89e5f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv
namespace GlobalTheory.FibLine.UnitaryInv
theorem _root_.solution (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) : ∀ᵐ x : ℂ, a + b * x ≠ 0 := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  simp only [ne_eq, not_not, Set.mem_setOf_eq] at hx hy
  by_cases hb : b = 0
  · rcases h with h | h
    · simp [hb, h] at hx
    · exact absurd hb h
  · apply mul_left_cancel₀ hb
    linear_combination hx - hy
end GlobalTheory.FibLine.UnitaryInv
