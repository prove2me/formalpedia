-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:26.083157+00:00
-- url     : https://prove2.me/submissions/73965997-1447-4fc9-bcff-82fd6179fe1a

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
theorem _root_.solution [DecidableEq n] (H : Matrix n n ℂ) (a b : n) :
    form H (Pi.single a 1) (Pi.single b 1) = H a b := by
  simp [form_eq_sum, Pi.single_apply, apply_ite]
end GlobalTheory.HermFrame
