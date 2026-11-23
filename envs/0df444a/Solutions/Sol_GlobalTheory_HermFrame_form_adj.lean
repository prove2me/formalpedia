-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:04.291957+00:00
-- url     : https://prove2.me/submissions/5b6a0bac-f3bf-4f93-ab8d-ac71c2e7b79c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_conj_form

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
theorem _root_.solution [DecidableEq m] {H : Matrix m m ℂ} {K : Matrix n n ℂ} (hH : H.IsHermitian)
    (hu : IsUnit H.det) (hK : K.IsHermitian) (T : Matrix n m ℂ) (v : m → ℂ) (w : n → ℂ) :
    form K (T *ᵥ v) w = form H v (adj H K T *ᵥ w) := by
  have hu' : IsUnit Hᵀ.det := by rwa [det_transpose]
  rw [← conj_form hH, ← conj_form hK, form_eq_transpose, form_eq_transpose, adj, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]
end GlobalTheory.HermFrame
