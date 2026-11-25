-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:49.902268+00:00
-- url     : https://prove2.me/submissions/1b040fde-7626-445a-a7c0-3d0de42f90b5

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
theorem _root_.solution (H K : Matrix n n ℂ) (v w : n → ℂ) :
    form (H + K) v w = form H v w + form K v w := by simp [form, add_mulVec]
end GlobalTheory.HermFrame
