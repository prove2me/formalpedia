-- Prove2me | solution 1 for GlobalTheory.ResRect.ftc_ver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:35.751391+00:00
-- url     : https://prove2.me/submissions/c2c31f33-aba5-4867-ac5a-fd491101e44b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_int_ver

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
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    I * ∫ y : ℝ in c..d, f (a + y * I) = F (a + d * I) - F (a + c * I) := by
  rw [mul_comm, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (a + y * I))
    (fun y hy => ?_) ((int_ver hf h).mul_const I)
  have h0 : HasDerivAt (fun t : ℂ => (a : ℂ) + t * I) I (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ)
  have h1 : HasDerivAt (fun t : ℂ => F (a + t * I)) (f (a + y * I) * I) (y : ℂ) :=
    HasDerivAt.comp (y : ℂ) (hF _ (h y hy)) h0
  exact h1.comp_ofReal
end GlobalTheory.ResRect
