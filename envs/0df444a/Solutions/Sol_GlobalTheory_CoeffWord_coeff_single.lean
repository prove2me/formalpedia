-- Prove2me | solution 1 for GlobalTheory.CoeffWord.coeff_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:38.045972+00:00
-- url     : https://prove2.me/submissions/94f0ee19-defe-4f24-8af6-b0430bc55685

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_single_monomial
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
theorem _root_.solution (p : Fin r × Fin n) (e : Fin r × Fin n →₀ ℕ) (he : e p = 0) (k : ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) :
    coeff e ((single R p G).coeff k) = coeff (e + Finsupp.single p k) G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | add G H hG hH => simp [hG, hH]
  | monomial m c =>
    rw [single_monomial, Polynomial.coeff_monomial, coeff_monomial]
    by_cases h : m = e + Finsupp.single p k
    · have h1 : m p = k := by simp [h, he]
      have h2 : m.erase p = e := by
        ext v
        by_cases hv : v = p
        · simp [hv, he]
        · simp [h, Finsupp.erase_ne hv, Finsupp.single_apply, Ne.symm hv]
      simp [h1, h2, ← h]
    · rw [if_neg h]
      split_ifs with h1
      · rw [coeff_monomial, if_neg]
        intro h2
        apply h
        rw [← h2, ← h1, Finsupp.erase_add_single]
      · simp
end GlobalTheory.CoeffWord
