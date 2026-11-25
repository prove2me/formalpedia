-- Prove2me | solution 1 for GlobalTheory.HermFrame.orthProj_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:32.347536+00:00
-- url     : https://prove2.me/submissions/f4f7cf2c-d3ed-40ff-81a2-3b16414ec862

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : orthProj H * incl m l = 1 := by
  simp [orthProj, incl, fromCols_mul_fromRows]
end GlobalTheory.HermFrame
