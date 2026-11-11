-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:09:06.464509+00:00
-- url     : https://prove2.me/submissions/0009d588-f3bf-45da-a98a-81be3e116116

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E056
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8137_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8138_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8139_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8140_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8141_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8142_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8143_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8144_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8145_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8146_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8147_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8148_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8149_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8150_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8125 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8125 := by decide +kernel

theorem rowCheck8125 : row8125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8125 := by decide +kernel

theorem rowEval8125 (x : Key → ℝ) : Integer.Sparse.eval row8125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8125, Integer.Sparse.eval_collectBalanced, rawRowCheck8125]

theorem rawRowCheck8126 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8126 := by decide +kernel

theorem rowCheck8126 : row8126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8126 := by decide +kernel

theorem rowEval8126 (x : Key → ℝ) : Integer.Sparse.eval row8126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8126, Integer.Sparse.eval_collectBalanced, rawRowCheck8126]

theorem rawRowCheck8127 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8127 := by decide +kernel

theorem rowCheck8127 : row8127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8127 := by decide +kernel

theorem rowEval8127 (x : Key → ℝ) : Integer.Sparse.eval row8127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8127, Integer.Sparse.eval_collectBalanced, rawRowCheck8127]

theorem rawRowCheck8128 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5 = rawRow8128 := by decide +kernel

theorem rowCheck8128 : row8128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8128 := by decide +kernel

theorem rowEval8128 (x : Key → ℝ) : Integer.Sparse.eval row8128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8128, Integer.Sparse.eval_collectBalanced, rawRowCheck8128]

theorem rawRowCheck8129 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5 = rawRow8129 := by decide +kernel

theorem rowCheck8129 : row8129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8129 := by decide +kernel

theorem rowEval8129 (x : Key → ℝ) : Integer.Sparse.eval row8129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8129, Integer.Sparse.eval_collectBalanced, rawRowCheck8129]

theorem rawRowCheck8130 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5 = rawRow8130 := by decide +kernel

theorem rowCheck8130 : row8130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8130 := by decide +kernel

theorem rowEval8130 (x : Key → ℝ) : Integer.Sparse.eval row8130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8130, Integer.Sparse.eval_collectBalanced, rawRowCheck8130]

theorem rawRowCheck8131 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5 = rawRow8131 := by decide +kernel

theorem rowCheck8131 : row8131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8131 := by decide +kernel

theorem rowEval8131 (x : Key → ℝ) : Integer.Sparse.eval row8131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8131, Integer.Sparse.eval_collectBalanced, rawRowCheck8131]

theorem rawRowCheck8132 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5 = rawRow8132 := by decide +kernel

theorem rowCheck8132 : row8132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8132 := by decide +kernel

theorem rowEval8132 (x : Key → ℝ) : Integer.Sparse.eval row8132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8132, Integer.Sparse.eval_collectBalanced, rawRowCheck8132]

theorem rawRowCheck8133 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5 = rawRow8133 := by decide +kernel

theorem rowCheck8133 : row8133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8133 := by decide +kernel

theorem rowEval8133 (x : Key → ℝ) : Integer.Sparse.eval row8133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8133, Integer.Sparse.eval_collectBalanced, rawRowCheck8133]

theorem rawRowCheck8134 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8134 := by decide +kernel

theorem rowCheck8134 : row8134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8134 := by decide +kernel

theorem rowEval8134 (x : Key → ℝ) : Integer.Sparse.eval row8134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8134, Integer.Sparse.eval_collectBalanced, rawRowCheck8134]

theorem rawRowCheck8135 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8135 := by decide +kernel

theorem rowCheck8135 : row8135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8135 := by decide +kernel

theorem rowEval8135 (x : Key → ℝ) : Integer.Sparse.eval row8135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8135, Integer.Sparse.eval_collectBalanced, rawRowCheck8135]

theorem rawRowCheck8136 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8136 := by decide +kernel

theorem rowCheck8136 : row8136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8136 := by decide +kernel

theorem rowEval8136 (x : Key → ℝ) : Integer.Sparse.eval row8136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8136, Integer.Sparse.eval_collectBalanced, rawRowCheck8136]

theorem rawRowCheck8151 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5 = rawRow8151 := by decide +kernel

theorem rowCheck8151 : row8151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8151 := by decide +kernel

theorem rowEval8151 (x : Key → ℝ) : Integer.Sparse.eval row8151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8151, Integer.Sparse.eval_collectBalanced, rawRowCheck8151]

theorem rawRowCheck8152 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5 = rawRow8152 := by decide +kernel

theorem rowCheck8152 : row8152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8152 := by decide +kernel

theorem rowEval8152 (x : Key → ℝ) : Integer.Sparse.eval row8152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8152, Integer.Sparse.eval_collectBalanced, rawRowCheck8152]

theorem rawRowCheck8153 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5 = rawRow8153 := by decide +kernel

theorem rowCheck8153 : row8153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8153 := by decide +kernel

theorem rowEval8153 (x : Key → ℝ) : Integer.Sparse.eval row8153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8153, Integer.Sparse.eval_collectBalanced, rawRowCheck8153]

theorem rawRowCheck8154 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5 = rawRow8154 := by decide +kernel

theorem rowCheck8154 : row8154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8154 := by decide +kernel

theorem rowEval8154 (x : Key → ℝ) : Integer.Sparse.eval row8154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8154, Integer.Sparse.eval_collectBalanced, rawRowCheck8154]

theorem rawRowCheck8155 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5 = rawRow8155 := by decide +kernel

theorem rowCheck8155 : row8155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8155 := by decide +kernel

theorem rowEval8155 (x : Key → ℝ) : Integer.Sparse.eval row8155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8155, Integer.Sparse.eval_collectBalanced, rawRowCheck8155]

theorem rawRowCheck8156 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5 = rawRow8156 := by decide +kernel

theorem rowCheck8156 : row8156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8156 := by decide +kernel

theorem rowEval8156 (x : Key → ℝ) : Integer.Sparse.eval row8156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8156, Integer.Sparse.eval_collectBalanced, rawRowCheck8156]

theorem rawRowCheck8157 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5 = rawRow8157 := by decide +kernel

theorem rowCheck8157 : row8157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8157 := by decide +kernel

theorem rowEval8157 (x : Key → ℝ) : Integer.Sparse.eval row8157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8157, Integer.Sparse.eval_collectBalanced, rawRowCheck8157]

theorem rawRowCheck8158 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5 = rawRow8158 := by decide +kernel

theorem rowCheck8158 : row8158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8158 := by decide +kernel

theorem rowEval8158 (x : Key → ℝ) : Integer.Sparse.eval row8158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8158, Integer.Sparse.eval_collectBalanced, rawRowCheck8158]

theorem rawRowCheck8159 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5 = rawRow8159 := by decide +kernel

theorem rowCheck8159 : row8159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8159 := by decide +kernel

theorem rowEval8159 (x : Key → ℝ) : Integer.Sparse.eval row8159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8159, Integer.Sparse.eval_collectBalanced, rawRowCheck8159]

theorem rawRowCheck8160 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5 = rawRow8160 := by decide +kernel

theorem rowCheck8160 : row8160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8160 := by decide +kernel

theorem rowEval8160 (x : Key → ℝ) : Integer.Sparse.eval row8160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8160, Integer.Sparse.eval_collectBalanced, rawRowCheck8160]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound8_5_e_oai (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8125 x
  · exact rowEval8126 x
  · exact rowEval8127 x
  · exact rowEval8128 x
  · exact rowEval8129 x
  · exact rowEval8130 x
  · exact rowEval8131 x
  · exact rowEval8132 x
  · exact rowEval8133 x
  · exact rowEval8134 x
  · exact rowEval8135 x
  · exact rowEval8136 x
  · exact rowEval8137_e x
  · exact rowEval8138_e x
  · exact rowEval8139_e x
  · exact rowEval8140_e x
  · exact rowEval8141_e x
  · exact rowEval8142_e x
  · exact rowEval8143_e x
  · exact rowEval8144_e x
  · exact rowEval8145_e x
  · exact rowEval8146_e x
  · exact rowEval8147_e x
  · exact rowEval8148_e x
  · exact rowEval8149_e x
  · exact rowEval8150_e x
  · exact rowEval8151 x
  · exact rowEval8152 x
  · exact rowEval8153 x
  · exact rowEval8154 x
  · exact rowEval8155 x
  · exact rowEval8156 x
  · exact rowEval8157 x
  · exact rowEval8158 x
  · exact rowEval8159 x
  · exact rowEval8160 x

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_5_e_oai
