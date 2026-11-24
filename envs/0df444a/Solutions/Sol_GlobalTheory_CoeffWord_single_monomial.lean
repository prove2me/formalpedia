-- Prove2me | solution 1 for GlobalTheory.CoeffWord.single_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:41.297068+00:00
-- url     : https://prove2.me/submissions/e86f1320-fb7a-46f5-90a1-240e8a1af918

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (p : Fin r × Fin n) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    single R p (monomial m c) = Polynomial.monomial (m p) (monomial (m.erase p) c) := by
  classical
  have h1 : (monomial m c : MvPolynomial (Fin r × Fin n) R) = monomial (m.erase p) c * X p ^ (m p) := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
  have h2 : single R p (monomial (m.erase p) c) = Polynomial.C (monomial (m.erase p) c) := by
    rw [single, aeval_monomial, monomial_eq, map_mul, map_finsuppProd]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v ≠ p := by
      rintro rfl
      simp at hv
    simp [this]
  have h3 : single R p (X p) = Polynomial.X := by simp [single]
  rw [h1, map_mul, map_pow, h2, h3, Polynomial.C_mul_X_pow_eq_monomial]
end GlobalTheory.CoeffWord
