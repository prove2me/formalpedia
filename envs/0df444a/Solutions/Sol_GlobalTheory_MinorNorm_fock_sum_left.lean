-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:57.117826+00:00
-- url     : https://prove2.me/submissions/8c3df261-9f35-41f3-bbcc-46b0a79350dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_add_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (∑ i ∈ s, P i) Q = ∑ i ∈ s, Formalism.E.fock (P i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.E.fock]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]
end GlobalTheory.MinorNorm
