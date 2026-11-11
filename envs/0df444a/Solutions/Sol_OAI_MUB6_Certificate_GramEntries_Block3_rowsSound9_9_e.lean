-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:09:12.5425+00:00
-- url     : https://prove2.me/submissions/170faa9a-fec5-421c-85ef-ff2bfbefce09

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E056
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8449_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8450_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8451_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8452_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8453_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8454_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8455_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8456_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8467_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8468_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8469_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8470_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8471_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8472_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8457 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form9 = rawRow8457 := by decide +kernel

theorem rowCheck8457 : row8457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8457 := by decide +kernel

theorem rowEval8457 (x : Key → ℝ) : Integer.Sparse.eval row8457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8457, Integer.Sparse.eval_collectBalanced, rawRowCheck8457]

theorem rawRowCheck8458 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form9 = rawRow8458 := by decide +kernel

theorem rowCheck8458 : row8458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8458 := by decide +kernel

theorem rowEval8458 (x : Key → ℝ) : Integer.Sparse.eval row8458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8458, Integer.Sparse.eval_collectBalanced, rawRowCheck8458]

theorem rawRowCheck8459 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form9 = rawRow8459 := by decide +kernel

theorem rowCheck8459 : row8459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8459 := by decide +kernel

theorem rowEval8459 (x : Key → ℝ) : Integer.Sparse.eval row8459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8459, Integer.Sparse.eval_collectBalanced, rawRowCheck8459]

theorem rawRowCheck8460 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form9 = rawRow8460 := by decide +kernel

theorem rowCheck8460 : row8460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8460 := by decide +kernel

theorem rowEval8460 (x : Key → ℝ) : Integer.Sparse.eval row8460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8460, Integer.Sparse.eval_collectBalanced, rawRowCheck8460]

theorem rawRowCheck8461 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form9 = rawRow8461 := by decide +kernel

theorem rowCheck8461 : row8461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8461 := by decide +kernel

theorem rowEval8461 (x : Key → ℝ) : Integer.Sparse.eval row8461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8461, Integer.Sparse.eval_collectBalanced, rawRowCheck8461]

theorem rawRowCheck8462 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form9 = rawRow8462 := by decide +kernel

theorem rowCheck8462 : row8462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8462 := by decide +kernel

theorem rowEval8462 (x : Key → ℝ) : Integer.Sparse.eval row8462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8462, Integer.Sparse.eval_collectBalanced, rawRowCheck8462]

theorem rawRowCheck8463 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form9 = rawRow8463 := by decide +kernel

theorem rowCheck8463 : row8463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8463 := by decide +kernel

theorem rowEval8463 (x : Key → ℝ) : Integer.Sparse.eval row8463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8463, Integer.Sparse.eval_collectBalanced, rawRowCheck8463]

theorem rawRowCheck8464 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form9 = rawRow8464 := by decide +kernel

theorem rowCheck8464 : row8464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8464 := by decide +kernel

theorem rowEval8464 (x : Key → ℝ) : Integer.Sparse.eval row8464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8464, Integer.Sparse.eval_collectBalanced, rawRowCheck8464]

theorem rawRowCheck8465 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form9 = rawRow8465 := by decide +kernel

theorem rowCheck8465 : row8465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8465 := by decide +kernel

theorem rowEval8465 (x : Key → ℝ) : Integer.Sparse.eval row8465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8465, Integer.Sparse.eval_collectBalanced, rawRowCheck8465]

theorem rawRowCheck8466 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form9 = rawRow8466 := by decide +kernel

theorem rowCheck8466 : row8466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8466 := by decide +kernel

theorem rowEval8466 (x : Key → ℝ) : Integer.Sparse.eval row8466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8466, Integer.Sparse.eval_collectBalanced, rawRowCheck8466]

theorem rawRowCheck8473 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow8473 := by decide +kernel

theorem rowCheck8473 : row8473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8473 := by decide +kernel

theorem rowEval8473 (x : Key → ℝ) : Integer.Sparse.eval row8473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8473, Integer.Sparse.eval_collectBalanced, rawRowCheck8473]

theorem rawRowCheck8474 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow8474 := by decide +kernel

theorem rowCheck8474 : row8474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8474 := by decide +kernel

theorem rowEval8474 (x : Key → ℝ) : Integer.Sparse.eval row8474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8474, Integer.Sparse.eval_collectBalanced, rawRowCheck8474]

theorem rawRowCheck8475 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow8475 := by decide +kernel

theorem rowCheck8475 : row8475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8475 := by decide +kernel

theorem rowEval8475 (x : Key → ℝ) : Integer.Sparse.eval row8475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8475, Integer.Sparse.eval_collectBalanced, rawRowCheck8475]

theorem rawRowCheck8476 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow8476 := by decide +kernel

theorem rowCheck8476 : row8476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8476 := by decide +kernel

theorem rowEval8476 (x : Key → ℝ) : Integer.Sparse.eval row8476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8476, Integer.Sparse.eval_collectBalanced, rawRowCheck8476]

theorem rawRowCheck8477 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow8477 := by decide +kernel

theorem rowCheck8477 : row8477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8477 := by decide +kernel

theorem rowEval8477 (x : Key → ℝ) : Integer.Sparse.eval row8477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8477, Integer.Sparse.eval_collectBalanced, rawRowCheck8477]

theorem rawRowCheck8478 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow8478 := by decide +kernel

theorem rowCheck8478 : row8478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8478 := by decide +kernel

theorem rowEval8478 (x : Key → ℝ) : Integer.Sparse.eval row8478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8478, Integer.Sparse.eval_collectBalanced, rawRowCheck8478]

theorem rawRowCheck8479 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form9 = rawRow8479 := by decide +kernel

theorem rowCheck8479 : row8479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8479 := by decide +kernel

theorem rowEval8479 (x : Key → ℝ) : Integer.Sparse.eval row8479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8479, Integer.Sparse.eval_collectBalanced, rawRowCheck8479]

theorem rawRowCheck8480 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form9 = rawRow8480 := by decide +kernel

theorem rowCheck8480 : row8480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8480 := by decide +kernel

theorem rowEval8480 (x : Key → ℝ) : Integer.Sparse.eval row8480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8480, Integer.Sparse.eval_collectBalanced, rawRowCheck8480]

theorem rawRowCheck8481 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form9 = rawRow8481 := by decide +kernel

theorem rowCheck8481 : row8481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8481 := by decide +kernel

theorem rowEval8481 (x : Key → ℝ) : Integer.Sparse.eval row8481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8481, Integer.Sparse.eval_collectBalanced, rawRowCheck8481]

theorem rawRowCheck8482 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form9 = rawRow8482 := by decide +kernel

theorem rowCheck8482 : row8482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8482 := by decide +kernel

theorem rowEval8482 (x : Key → ℝ) : Integer.Sparse.eval row8482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8482, Integer.Sparse.eval_collectBalanced, rawRowCheck8482]

theorem rawRowCheck8483 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form9 = rawRow8483 := by decide +kernel

theorem rowCheck8483 : row8483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8483 := by decide +kernel

theorem rowEval8483 (x : Key → ℝ) : Integer.Sparse.eval row8483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck8483, Integer.Sparse.eval_collectBalanced, rawRowCheck8483]

theorem rawRowCheck8484 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form9 = rawRow8484 := by decide +kernel

theorem rowCheck8484 : row8484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8484 := by decide +kernel

theorem rowEval8484 (x : Key → ℝ) : Integer.Sparse.eval row8484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck8484, Integer.Sparse.eval_collectBalanced, rawRowCheck8484]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound9_9_e_oai (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval8449_e x
  · exact rowEval8450_e x
  · exact rowEval8451_e x
  · exact rowEval8452_e x
  · exact rowEval8453_e x
  · exact rowEval8454_e x
  · exact rowEval8455_e x
  · exact rowEval8456_e x
  · exact rowEval8457 x
  · exact rowEval8458 x
  · exact rowEval8459 x
  · exact rowEval8460 x
  · exact rowEval8461 x
  · exact rowEval8462 x
  · exact rowEval8463 x
  · exact rowEval8464 x
  · exact rowEval8465 x
  · exact rowEval8466 x
  · exact rowEval8467_e x
  · exact rowEval8468_e x
  · exact rowEval8469_e x
  · exact rowEval8470_e x
  · exact rowEval8471_e x
  · exact rowEval8472_e x
  · exact rowEval8473 x
  · exact rowEval8474 x
  · exact rowEval8475 x
  · exact rowEval8476 x
  · exact rowEval8477 x
  · exact rowEval8478 x
  · exact rowEval8479 x
  · exact rowEval8480 x
  · exact rowEval8481 x
  · exact rowEval8482 x
  · exact rowEval8483 x
  · exact rowEval8484 x

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_9_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_9_e_oai
