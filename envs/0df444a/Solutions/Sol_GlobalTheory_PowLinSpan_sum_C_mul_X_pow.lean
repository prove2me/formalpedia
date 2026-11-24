-- Prove2me | solution 1 for GlobalTheory.PowLinSpan.sum_C_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:11.193985+00:00
-- url     : https://prove2.me/submissions/cf2658dd-3018-499f-9a83-54fb78e8d4d2

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.PowLinSpan
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace GlobalTheory.PowLinSpan
theorem _root_.solution (u : σ → ℝ) (d : ℕ) :
    (∑ x, C (u x) * X x : MvPolynomial σ ℝ) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, u x ^ k x) •
          monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul, map_natCast, C_1, one_mul,
    Finsupp.coe_equivFunOnFinite_symm]
  ring
end GlobalTheory.PowLinSpan
