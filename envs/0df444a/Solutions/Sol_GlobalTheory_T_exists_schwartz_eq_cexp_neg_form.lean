-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartz_eq_cexp_neg_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:50.539191+00:00
-- url     : https://prove2.me/submissions/1878fb08-6b11-4fcf-ac12-4cd0dbac9857

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzCexpNegForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzCexpNegFormStatement
import Theorems.Thm_GlobalTheory_GaussComplexForm_exists_schwartz_cexp_neg_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  first | exact @GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | exact GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | (intros; apply GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form <;> assumption)
end _root_.GlobalTheory.T
