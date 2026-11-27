-- Prove2me | solution 1 for GlobalTheory.totalDegree_perpVector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:22.759393+00:00
-- url     : https://prove2.me/submissions/87d8760e-fa28-4318-9d3a-32f77f75d482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
import Theorems.Thm_GlobalTheory_totalDegree_det_le
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
theorem _root_.solution {p : ℕ} {κ : Type*}
    (ε : Fin p → Module.Dual (MvPolynomial τ S) (κ → MvPolynomial τ S))
    (e' : Fin p → κ → MvPolynomial τ S) (g : κ → MvPolynomial τ S) {d m : ℕ}
    (he : ∀ a a', (ε a (e' a')).totalDegree ≤ d) (hg : ∀ a, (ε a g).totalDegree ≤ d)
    (he' : ∀ a k, (e' a k).totalDegree ≤ m) (hgm : ∀ k, (g k).totalDegree ≤ m) (k : κ) :
    (perpVector ε e' g k).totalDegree ≤ p * d + m := by
  have hdet := totalDegree_det_le (pairingMatrix ε e') (d := d) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  simp only [perpVector, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (add_le_add hdet (hgm k))
  · refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun a' _ => ?_
    refine (totalDegree_mul _ _).trans (add_le_add ?_ (he' a' k))
    cases p with
    | zero => exact a.elim0
    | succ n =>
      refine (totalDegree_mul _ _).trans ?_
      rw [Nat.succ_mul]
      refine add_le_add ?_ (hg a)
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      have h := totalDegree_det_le ((pairingMatrix ε e').submatrix a'.succAbove a.succAbove)
        (d := d) fun _ _ => he _ _
      rw [Fintype.card_fin] at h
      rcases neg_one_pow_eq_or (MvPolynomial τ S) ((a' : ℕ) + a) with hs | hs
      · rw [hs, one_mul]; exact h
      · rw [hs, neg_one_mul, totalDegree_neg]; exact h
end GlobalTheory
