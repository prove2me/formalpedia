-- Prove2me | solution 1 for GlobalTheory.HermFrame.conj_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:52.684336+00:00
-- url     : https://prove2.me/submissions/23ea1096-cfb9-4cf2-a708-89bd201ef32b

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
theorem _root_.solution {H : Matrix n n ℂ} (hH : H.IsHermitian) (v w : n → ℂ) :
    conj (form H v w) = form H w v := by
  simp only [form_eq_sum, map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b]; simp; ring
end GlobalTheory.HermFrame
