-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.exp_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:15.773712+00:00
-- url     : https://prove2.me/submissions/b7125509-6ccd-45dd-bf25-e725fea6855d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_exp_mul_eq
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_pr
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_rp
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_up_p
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_up_r

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m : Type} [Fintype m] [DecidableEq m]
variable {N A B A' B' : Matrix m m ℂ}
variable {p r q θ Z : Matrix m m ℂ}
namespace GlobalTheory.IndLine.Iwasawa
theorem _root_.solution (h : Grading p r q θ) (Z : Matrix m m ℂ) (t : ℝ) :
    NormedSpace.exp (t • up p r q Z) * p = p ∧ (1 - p) * NormedSpace.exp (t • up p r q Z) * r = r := by
  set A := t • up p r q Z with hA
  have a1 : A * p = 0 := by rw [hA, Matrix.smul_mul, h.up_p, smul_zero]
  have a2 : A * r = p * (t • Z) * r := by rw [hA, Matrix.smul_mul, h.up_r, Matrix.mul_smul, Matrix.smul_mul]
  have e1 : NormedSpace.exp A * p = p := by
    rw [exp_mul_eq (D := 0) (by rw [a1, Matrix.mul_zero]), NormedSpace.exp_zero, Matrix.mul_one]
  refine ⟨e1, ?_⟩
  have e2 : NormedSpace.exp A * (p + r) = (p + r) * NormedSpace.exp (A * r) := by
    refine exp_mul_eq ?_
    rw [Matrix.mul_add, a1, zero_add, a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_mul, h.pp, h.rp, add_zero]
  have e3 : r * NormedSpace.exp (A * r) = r := by
    rw [← exp_mul_eq (A := 0) (by rw [a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.rp]; simp), NormedSpace.exp_zero,
      Matrix.one_mul]
  have e4 : (1 - p) * (p + r) = r := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, h.pp, h.pr]; abel
  have e5 : (1 - p) * p = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h.pp, sub_self]
  calc (1 - p) * NormedSpace.exp A * r = (1 - p) * (NormedSpace.exp A * (p + r)) - (1 - p) * (NormedSpace.exp A * p) := by
        noncomm_ring
    _ = r := by rw [e1, e2, e5, sub_zero, ← Matrix.mul_assoc, e4, e3]
end GlobalTheory.IndLine.Iwasawa
