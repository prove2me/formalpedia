-- Prove2me | solution 1 for GlobalTheory.HermFrame.isSesq_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:34.744357+00:00
-- url     : https://prove2.me/submissions/33198a94-6be2-43a8-9a6e-03b0fe4e807f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_form_add_left
import Theorems.Thm_GlobalTheory_HermFrame_form_add_right
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_left
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_right

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : Matrix n n ℂ) : IsSesq (form H) :=
  ⟨form_add_left H, form_smul_left H, form_add_right H, form_smul_right H⟩
end GlobalTheory.HermFrame
