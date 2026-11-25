-- Prove2me | solution 1 for GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:09.506803+00:00
-- url     : https://prove2.me/submissions/ab035df2-aec5-4c19-88e8-a855947d3958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInner
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInnerStatement
import Theorems.Thm_GlobalTheory_MultilinearMap_inner_map_eq_const_mul_prod_inner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)] [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : MultilinearMap ℂ Xs E) (K : ℝ), (∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) → ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  first | exact @GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | exact GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | (intros; apply GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner <;> assumption)
end _root_.GlobalTheory.T
