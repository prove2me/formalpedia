-- Prove2me | solution 1 for GlobalTheory.FibLine.eq_zero_of_eval_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:56.595623+00:00
-- url     : https://prove2.me/submissions/b5c4d684-fe41-4eee-ad91-284fc833d830

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Theorems.Thm_GlobalTheory_FibLine_eq_zero_of_eval_real
import Theorems.Thm_GlobalTheory_FibLine_eval_bind_hermSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution (P : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (h : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → MvPolynomial.eval (entries H) P = 0) : P = 0 := by
  have hQ : bind₁ hermSubst P = 0 := by
    refine eq_zero_of_eval_real _ fun x => ?_
    rw [eval_bind_hermSubst]
    refine h _ ?_
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]
  refine MvPolynomial.funext fun y => ?_
  have h2 := eval_bind_hermSubst P
    (entries !![y (0, 0), (y (0, 1) + y (1, 0)) / 2; (y (0, 1) - y (1, 0)) / (2 * Complex.I), y (1, 1)])
  rw [hQ] at h2
  rw [map_zero] at h2 ⊢
  rw [h2]
  congr 2
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [entries] <;> field_simp <;> ring
end GlobalTheory.FibLine
