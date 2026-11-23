-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:40.742952+00:00
-- url     : https://prove2.me/submissions/296b719f-0da2-4aab-9f00-e755ec1e4bf5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
namespace GlobalTheory.HermFrame
theorem _root_.solution (K : Matrix n n ℂ) (A : Matrix n m ℂ) (B : Matrix n l ℂ) (u : m → ℂ)
    (w : l → ℂ) : form K (A *ᵥ u) (B *ᵥ w) = u ⬝ᵥ (Aᵀ * K * Bᴴᵀ) *ᵥ star w := by
  rw [form, star_mulVec, ← mulVec_transpose, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.HermFrame
