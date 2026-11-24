-- Prove2me | solution 1 for GlobalTheory.VFComp.symb_coefVF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:25.59568+00:00
-- url     : https://prove2.me/submissions/ccdb06d3-f6ee-4d57-b681-9ebde518b716

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Theorems.Thm_GlobalTheory_VFComp_sum_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}
namespace GlobalTheory.VFComp
theorem _root_.solution (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (x ξ : E d) : symb (m + 1) (coefVF m a c) x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ := by
  unfold symb coefVF coefB
  rw [sum_cons, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [coefA, le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false, add_zero, Fin.cons_zero,
    Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ]
  ring
end GlobalTheory.VFComp
