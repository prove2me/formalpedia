-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:59.814583+00:00
-- url     : https://prove2.me/submissions/11b8a2ff-7667-4017-8dd2-935329323231

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
theorem _root_.solution (P P' Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (P + P') Q = Formalism.E.fock P Q + Formalism.E.fock P' Q := by
  classical
  rw [fock_eq_sum (P + P') Q (P.support ∪ P'.support) support_add,
    fock_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left,
    fock_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring
end GlobalTheory.MinorNorm
