-- Prove2me | solution 1 for GlobalTheory.FibLine.eval_bind_hermSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:28.007546+00:00
-- url     : https://prove2.me/submissions/c97a64d8-d7da-4b72-9257-4731f4e1f6ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian

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
theorem _root_.solution (P : MvPolynomial (Fin 2 × Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    eval x (bind₁ hermSubst P) =
      eval (entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)]) P := by
  have h1 : (fun i => eval x (hermSubst i)) =
      entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)] := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [hermSubst, entries]
  rw [← h1]
  exact eval₂Hom_bind₁ (RingHom.id ℂ) x hermSubst P
end GlobalTheory.FibLine
