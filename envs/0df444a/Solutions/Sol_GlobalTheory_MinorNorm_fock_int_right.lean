-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_int_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:11.882416+00:00
-- url     : https://prove2.me/submissions/e8989eca-f6cd-4a88-a534-e8d6b83b3582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

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
    Formalism.E.fock P ((z : MvPolynomial σ ℂ) * Q) = z * Formalism.E.fock P Q := by
  have e : (z : MvPolynomial σ ℂ) = C (z : ℂ) := by simp
  rw [e, Formalism.E.fock, Formalism.E.fock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_C_mul, star_mul', star_intCast]; ring
end GlobalTheory.MinorNorm
