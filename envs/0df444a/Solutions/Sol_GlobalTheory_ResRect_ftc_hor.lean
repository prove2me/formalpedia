-- Prove2me | solution 1 for GlobalTheory.ResRect.ftc_hor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:49.005964+00:00
-- url     : https://prove2.me/submissions/22a1b5e1-3250-47ff-be5c-3964f0cb4f31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_int_hor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    ∫ x : ℝ in a..b, f (x + c * I) = F (b + c * I) - F (a + c * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + c * I))
    (fun x hx => ?_) (int_hor hf h)
  have h1 : HasDerivAt (fun t : ℂ => F (t + c * I)) (f (x + c * I)) (x : ℂ) :=
    HasDerivAt.comp_add_const (x : ℂ) (c * I) (hF _ (h x hx))
  exact h1.comp_ofReal
end GlobalTheory.ResRect
