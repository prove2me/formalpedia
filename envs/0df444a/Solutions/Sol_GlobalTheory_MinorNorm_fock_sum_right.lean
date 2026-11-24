-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:31.545815+00:00
-- url     : https://prove2.me/submissions/4800b03f-2290-42d9-a221-70bc889d066c

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
theorem _root_.solution {ι : Type} (s : Finset ι) (P : MvPolynomial σ ℂ) (Q : ι → MvPolynomial σ ℂ) :
    Formalism.E.fock P (∑ i ∈ s, Q i) = ∑ i ∈ s, Formalism.E.fock P (Q i) := by
  unfold Formalism.E.fock
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]
end GlobalTheory.MinorNorm
