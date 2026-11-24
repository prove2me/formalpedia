-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:08.276591+00:00
-- url     : https://prove2.me/submissions/e5283ffe-f301-4f01-bbf9-97d8ad5de6f3

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    Formalism.E.fock P Q = ∑ m ∈ s, P.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
  unfold Formalism.E.fock
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm]; simp
end GlobalTheory.MinorNorm
