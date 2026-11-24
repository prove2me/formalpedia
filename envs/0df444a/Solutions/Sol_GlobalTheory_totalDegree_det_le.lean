-- Prove2me | solution 1 for GlobalTheory.totalDegree_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:47.19935+00:00
-- url     : https://prove2.me/submissions/17385de8-1c43-46bc-9476-a7b855910b95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
open MvPolynomial
variable {S τ : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (MvPolynomial τ S)) {d : ℕ} (hH : ∀ i j, (H i j).totalDegree ≤ d) :
    H.det.totalDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  have h : (∏ i, H (σ i) i).totalDegree ≤ Fintype.card ι * d :=
    (totalDegree_finsetProd _ _).trans <| by
      simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => (H (σ i) i).totalDegree) d
        fun i _ => hH _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h
  · rw [hs, Units.neg_smul, one_smul, totalDegree_neg]; exact h
end GlobalTheory
