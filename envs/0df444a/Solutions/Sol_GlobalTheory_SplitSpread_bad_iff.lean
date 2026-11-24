-- Prove2me | solution 1 for GlobalTheory.SplitSpread.bad_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:16.645799+00:00
-- url     : https://prove2.me/submissions/e7589748-af59-4578-92aa-ba2b6ad68b5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
import Theorems.Thm_GlobalTheory_SplitSpread_totalDegree_sum_le
import Theorems.Thm_GlobalTheory_SplitSpread_sum_coeff
import Theorems.Thm_GlobalTheory_SplitSpread_eval_eqs_coeff
import Theorems.Thm_GlobalTheory_SplitSpread_eval_eqs_point
import Theorems.Thm_GlobalTheory_SplitSpread_eval_eqs_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]
namespace GlobalTheory.SplitSpread
theorem _root_.solution (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) :
    (∃ z : Var σ D → k, ∀ j, eval₂ ψ z (eqs A D f g j) = 0) ↔ Bad f g D k ψ := by
  constructor
  · rintro ⟨z, hz⟩
    have hinv : ∀ b, MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i))))
        (MvPolynomial.map ψ g) ≠ 0 := by
      intro b h0
      have := hz (Sum.inr (Sum.inr b))
      rw [eval_eqs_inv, h0] at this
      simp at this
    refine ⟨spec z true, spec z false, totalDegree_sum_le _, totalDegree_sum_le _, ?_,
      fun i => z (Sum.inr (Sum.inl (true, i))), fun i => z (Sum.inr (Sum.inl (false, i))),
      ?_, hinv true, ?_, hinv false⟩
    · ext n
      have := hz (Sum.inl n)
      rw [eval_eqs_coeff, coeff_sub, sub_eq_zero] at this
      exact this
    · have := hz (Sum.inr (Sum.inl true)); rwa [eval_eqs_point] at this
    · have := hz (Sum.inr (Sum.inl false)); rwa [eval_eqs_point] at this
  · rintro ⟨u, v, hu, hv, huv, P, Q, hPu, hPg, hQv, hQg⟩
    let z : Var σ D → k := Sum.elim (fun p => coeff p.2.1 (if p.1 then u else v))
      (Sum.elim (fun p => if p.1 then P p.2 else Q p.2)
        (fun b => (MvPolynomial.eval (if b then P else Q) (MvPolynomial.map ψ g))⁻¹))
    have hs : ∀ b, spec z b = if b then u else v := by
      intro b
      cases b
      · exact sum_coeff v hv
      · exact sum_coeff u hu
    refine ⟨z, ?_⟩
    rintro (n | b | b)
    · rw [eval_eqs_coeff, hs, hs]
      simp [huv]
    · rw [eval_eqs_point, hs]
      cases b <;> simpa [z]
    · rw [eval_eqs_inv]
      cases b
      · simp only [z, Sum.elim_inr, Bool.false_eq_true, if_false]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hQg)
      · simp only [z, Sum.elim_inr, if_true]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hPg)
end GlobalTheory.SplitSpread
