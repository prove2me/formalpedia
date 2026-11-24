-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.trace_path
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:58.033523+00:00
-- url     : https://prove2.me/submissions/8caa228b-1af5-4c0c-9231-f327d972d2bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_sum_cons_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {S : Type} [CommRing S] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution (X : Matrix (Fin n) (Fin n) S) (k : ℕ) : ∀ Y : Matrix (Fin n) (Fin n) S,
    (Y * X ^ k).trace = ∑ idx : Fin (k + 1) → Fin n,
      Y (idx (Fin.last k)) (idx 0) * ∏ a : Fin k, X (idx a.castSucc) (idx a.succ) := by
  induction k with
  | zero =>
    intro Y
    rw [sum_cons_split]
    simp [Matrix.trace]
  | succ k ih =>
    intro Y
    rw [pow_succ', ← mul_assoc, ih, sum_cons_split (d := k + 1)]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_succ, ← Fin.succ_last]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.castSucc_zero, ← Fin.succ_castSucc, mul_assoc]
end GlobalTheory.SmoothForms.PermWord
