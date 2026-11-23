-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:09.548678+00:00
-- url     : https://prove2.me/submissions/3347ce88-79b3-4cd9-936e-fd44c4b3f8d1

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
theorem _root_.solution (H : Matrix n n ℂ) (c : ℂ) (v w : n → ℂ) :
    form H v (c • w) = conj c * form H v w := by simp [form, mulVec_smul]
end GlobalTheory.HermFrame
