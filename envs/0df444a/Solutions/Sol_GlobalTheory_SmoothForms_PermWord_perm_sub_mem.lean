-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.perm_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:30.56303+00:00
-- url     : https://prove2.me/submissions/62a8f8e5-bfe4-46a2-ba75-c02819cb5f2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_cons
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_mem_shorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_mul_mem_shorter

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    wd E l - wd E l' ∈ shorter E l.length := by
  induction h with
  | nil => simp
  | cons z _ ih => rw [wd_cons, wd_cons, ← mul_sub]; exact mul_mem_shorter E z ih
  | swap x y l =>
    simp only [wd_cons]
    rw [← mul_assoc, ← mul_assoc, ← sub_mul, hE, sub_mul]
    refine sub_mem ?_ ?_
    · split_ifs
      · exact wd_mem_shorter E (l := (y.1, x.2) :: l) (by simp)
      · simp
    · split_ifs
      · exact wd_mem_shorter E (l := (x.1, y.2) :: l) (by simp)
      · simp
  | trans h1 _ ih1 ih2 =>
    rw [← h1.length_eq] at ih2
    simpa using add_mem ih1 ih2
end GlobalTheory.SmoothForms.PermWord
