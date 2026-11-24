-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_int_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:02.017459+00:00
-- url     : https://prove2.me/submissions/26d97877-c782-4350-89d3-90495c2486c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_eq_sum

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
theorem _root_.solution (z : ℤ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock ((z : MvPolynomial σ ℂ) * P) Q = z * Formalism.E.fock P Q := by
  have e : (z : MvPolynomial σ ℂ) = C (z : ℂ) := by simp
  rw [e, C_mul', fock_eq_sum _ Q P.support support_smul, Formalism.E.fock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring
end GlobalTheory.MinorNorm
