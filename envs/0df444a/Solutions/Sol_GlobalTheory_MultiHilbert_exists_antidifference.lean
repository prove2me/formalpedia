-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.exists_antidifference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:50.123843+00:00
-- url     : https://prove2.me/submissions/efd1fe1d-7d43-47eb-a04d-5a29909af53d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_add
import Theorems.Thm_GlobalTheory_MultiHilbert_eval_polynomial_aeval_X
import Theorems.Thm_GlobalTheory_MultiHilbert_eval_monomial_erase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (Φ : MvPolynomial (Fin r) ℚ) (k : Fin r) :
    ∃ Ψ : MvPolynomial (Fin r) ℚ, ∀ x : Fin r → ℚ,
      eval (Function.update x k (x k + 1)) Ψ - eval x Ψ = eval x Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | monomial d c =>
    refine ⟨monomial (d.erase k) (c / (d k + 1)) *
      Polynomial.aeval (X k : MvPolynomial (Fin r) ℚ) (Polynomial.bernoulli (d k + 1)),
      fun x => ?_⟩
    have hd : monomial d c = monomial (d.erase k) c * (X k : MvPolynomial (Fin r) ℚ) ^ d k := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [map_mul, map_mul, eval_monomial_erase, eval_polynomial_aeval_X, eval_polynomial_aeval_X,
      Function.update_self, add_comm (x k) 1, Polynomial.bernoulli_eval_one_add, hd, map_mul,
      eval_monomial, eval_monomial]
    have : (d k : ℚ) + 1 ≠ 0 := by positivity
    simp only [map_pow, eval_X, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    refine ⟨P + Q, fun x => ?_⟩
    rw [map_add, map_add, map_add, ← hP, ← hQ]
    ring
end GlobalTheory.MultiHilbert
