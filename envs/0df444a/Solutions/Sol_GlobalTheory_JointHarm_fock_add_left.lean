-- Prove2me | solution 1 for GlobalTheory.JointHarm.fock_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:15.813033+00:00
-- url     : https://prove2.me/submissions/37351db7-2f89-4277-9e4d-29a0abad78cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E
namespace GlobalTheory.JointHarm
theorem _root_.solution {σ : Type} (P P' Q : MvPolynomial σ ℂ) :
    fock (P + P') Q = fock P Q + fock P' Q := by
  classical
  have key : ∀ (F : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)), F.support ⊆ s →
      fock F Q = ∑ m ∈ s, F.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
    intro F s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
  rw [key _ _ support_add, key P _ Finset.subset_union_left, key P' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring
end GlobalTheory.JointHarm
