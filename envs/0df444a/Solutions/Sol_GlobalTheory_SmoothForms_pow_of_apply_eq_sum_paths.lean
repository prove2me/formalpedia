-- Prove2me | solution 1 for GlobalTheory.SmoothForms.pow_of_apply_eq_sum_paths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:59.232925+00:00
-- url     : https://prove2.me/submissions/a2902f29-4cf6-45f2-94ee-94300c6ca24f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Theorems.Thm_GlobalTheory_SmoothForms_sum_fin_succ_fun_cons

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
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.SmoothForms
theorem _root_.solution (E : Fin n → Fin n → A) (k : ℕ) (c e : Fin n) :
    (Matrix.of E ^ (k + 1)) c e = ∑ idx : Fin k → Fin n, (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons c idx : Fin (k + 1) → Fin n) a) ((Fin.snoc idx e : Fin (k + 1) → Fin n) a)).prod := by
  induction k generalizing c with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_fun_cons]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [List.ofFn_succ (n := k + 1), List.prod_cons, ← Fin.cons_snoc_eq_snoc_cons]
    simp
end GlobalTheory.SmoothForms
