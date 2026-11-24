-- Prove2me | solution 1 for GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:04.379664+00:00
-- url     : https://prove2.me/submissions/6b46bf0b-2918-4b4e-9dda-a20bbb5ebfb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
import Theorems.Thm_GlobalTheory_Div_CMAlgChar_place_factor
import Theorems.Thm_GlobalTheory_Div_CMAlgChar_fiber_eq
import Theorems.Thm_GlobalTheory_Div_CMAlgChar_embedding_ne_conjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar
namespace GlobalTheory.Div.CMAlgChar
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  intro E _ _ _ n w0 hn k hk
  classical
  have hfib : ∀ f : (E →+* ℂ) → ℂ, ∏ φ, f φ =
      ∏ w : InfinitePlace E, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
    intro f
    rw [← Finset.prod_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [fiber_eq w, Finset.prod_pair (embedding_ne_conjugate w)]
  rw [hfib (fun φ => ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)),
    hfib (fun φ => φ k ^ n φ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding k ≠ 0 := (map_ne_zero _).2 hk
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact place_factor _ hz _ _ _ (hn _)
end GlobalTheory.Div.CMAlgChar
