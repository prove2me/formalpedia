-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:32.678802+00:00
-- url     : https://prove2.me/submissions/1469255b-d8f9-4f22-984d-2775d533f5f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_eq_sum
import Theorems.Thm_GlobalTheory_MinorNorm_fock_add_left
import Theorems.Thm_GlobalTheory_MinorNorm_mfact_add_single
import Theorems.Thm_P2M_GlobalTheory_MinorNorm_coeff_pderiv__5701bf4a009b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {σ : Type}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (v : σ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (X v * P) Q = Formalism.E.fock P (pderiv v Q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [mul_add, fock_add_left, h₁, h₂]
  | monomial a c =>
    rw [mul_comm, X, monomial_mul, mul_one,
      fock_eq_sum _ _ {a + Finsupp.single v 1} support_monomial_subset,
      fock_eq_sum _ _ {a} support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton,
      coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl, coeff_pderiv', mfact_add_single]
    simp only [star_mul', star_add, star_natCast, star_one]
    push_cast
    ring
end GlobalTheory.MinorNorm
