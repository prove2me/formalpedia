-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:30.830982+00:00
-- url     : https://prove2.me/submissions/1d94d36d-5ad3-4f65-90ac-35f4a874d4a6

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
theorem _root_.solution (c : ℂ) (H : Matrix n n ℂ) (v w : n → ℂ) :
    form (c • H) v w = c * form H v w := by simp [form, smul_mulVec]
end GlobalTheory.HermFrame
