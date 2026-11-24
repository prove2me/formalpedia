-- Prove2me | solution 1 for GlobalTheory.PowLinSpan.homog_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:20.389502+00:00
-- url     : https://prove2.me/submissions/613fa111-d578-43e8-8358-d84eb434cc88

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots
import Theorems.Thm_GlobalTheory_PowLinSpan_monomial_kill

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
theorem _root_.solution (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsHomogeneous d) : φ Q = 0 := by
  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : ∑ x, m x = d := by
    have := hQ (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : monomial m (coeff m Q) = coeff m Q • monomial m (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, monomial_kill φ d hP m hdeg, smul_zero]
end GlobalTheory.PowLinSpan
