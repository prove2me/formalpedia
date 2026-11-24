-- Prove2me | solution 1 for GlobalTheory.HermFrame.gnorm_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:20.096319+00:00
-- url     : https://prove2.me/submissions/38273e44-9ace-4ec6-9b20-3dcebf60b09c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_form_add_left
import Theorems.Thm_GlobalTheory_HermFrame_form_add_right
import Theorems.Thm_GlobalTheory_HermFrame_form_sub_left
import Theorems.Thm_GlobalTheory_HermFrame_form_sub_right
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq

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
theorem _root_.solution {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    gnorm H (v + w) ^ 2 + gnorm H (v - w) ^ 2 = 2 * (gnorm H v ^ 2 + gnorm H w ^ 2) := by
  simp only [gnorm_sq hH, form_add_left, form_add_right, form_sub_left, form_sub_right, add_re,
    sub_re]
  ring
end GlobalTheory.HermFrame
