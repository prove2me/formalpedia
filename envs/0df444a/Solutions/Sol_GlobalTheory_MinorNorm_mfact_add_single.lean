-- Prove2me | solution 1 for GlobalTheory.MinorNorm.mfact_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:32.318356+00:00
-- url     : https://prove2.me/submissions/899ae5fc-5caa-43cb-8c2c-becc7d3ce4b8

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
theorem _root_.solution (m : σ →₀ ℕ) (v : σ) :
    Formalism.A.mfact (m + Finsupp.single v 1) = (m v + 1) * Formalism.A.mfact m := by
  classical
  have h : ∀ (g : σ →₀ ℕ) (s : Finset σ), g.support ⊆ s →
      Formalism.A.mfact g = ∏ i ∈ s, (g i).factorial := by
    intro g s hs
    unfold Formalism.A.mfact
    exact Finset.prod_subset hs fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi]; rfl
  have h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro i hi
    by_cases hv : i = v
    · simp [hv]
    · simpa [hv, Finsupp.single_apply, Ne.symm hv] using hi
  rw [h _ _ h1, h m (insert v m.support) (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v _), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, Ne.symm this]
end GlobalTheory.MinorNorm
