-- Prove2me | solution 1 for GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:39.282917+00:00
-- url     : https://prove2.me/submissions/9ef33149-0bc8-49cf-a4f3-c9ef180faa37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MultilinearSumEqOfProdFunEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MultilinearSumEqOfProdFunEqStatement
import Theorems.Thm_GlobalTheory_multilinear_sum_eq_of_prod_fun_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  first | exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq | exact GlobalTheory.multilinear_sum_eq_of_prod_fun_eq | (intros; apply GlobalTheory.multilinear_sum_eq_of_prod_fun_eq <;> assumption)
end _root_.GlobalTheory.T
