-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.rowsSound2_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:10:09.190205+00:00
-- url     : https://prove2.me/submissions/30c15985-e3eb-4e3d-993c-396a08b6d603

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E049
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18483_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18484_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18485_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18486_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18487_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18488_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18489_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18490_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18491_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18492_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18493_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18494_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18495_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18496_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18497_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18498_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18499_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18500_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18501_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18502_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18503_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18504_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18505_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18506_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck18459 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18459 := by decide +kernel

theorem rowCheck18459 : row18459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18459 := by decide +kernel

theorem rowEval18459 (x : Key → ℝ) : Integer.Sparse.eval row18459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18459, Integer.Sparse.eval_collectBalanced, rawRowCheck18459]

theorem rawRowCheck18460 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18460 := by decide +kernel

theorem rowCheck18460 : row18460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18460 := by decide +kernel

theorem rowEval18460 (x : Key → ℝ) : Integer.Sparse.eval row18460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18460, Integer.Sparse.eval_collectBalanced, rawRowCheck18460]

theorem rawRowCheck18461 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18461 := by decide +kernel

theorem rowCheck18461 : row18461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18461 := by decide +kernel

theorem rowEval18461 (x : Key → ℝ) : Integer.Sparse.eval row18461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18461, Integer.Sparse.eval_collectBalanced, rawRowCheck18461]

theorem rawRowCheck18462 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow18462 := by decide +kernel

theorem rowCheck18462 : row18462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18462 := by decide +kernel

theorem rowEval18462 (x : Key → ℝ) : Integer.Sparse.eval row18462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18462, Integer.Sparse.eval_collectBalanced, rawRowCheck18462]

theorem rawRowCheck18463 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow18463 := by decide +kernel

theorem rowCheck18463 : row18463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18463 := by decide +kernel

theorem rowEval18463 (x : Key → ℝ) : Integer.Sparse.eval row18463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18463, Integer.Sparse.eval_collectBalanced, rawRowCheck18463]

theorem rawRowCheck18464 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow18464 := by decide +kernel

theorem rowCheck18464 : row18464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18464 := by decide +kernel

theorem rowEval18464 (x : Key → ℝ) : Integer.Sparse.eval row18464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18464, Integer.Sparse.eval_collectBalanced, rawRowCheck18464]

theorem rawRowCheck18465 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow18465 := by decide +kernel

theorem rowCheck18465 : row18465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18465 := by decide +kernel

theorem rowEval18465 (x : Key → ℝ) : Integer.Sparse.eval row18465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18465, Integer.Sparse.eval_collectBalanced, rawRowCheck18465]

theorem rawRowCheck18466 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow18466 := by decide +kernel

theorem rowCheck18466 : row18466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18466 := by decide +kernel

theorem rowEval18466 (x : Key → ℝ) : Integer.Sparse.eval row18466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18466, Integer.Sparse.eval_collectBalanced, rawRowCheck18466]

theorem rawRowCheck18467 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow18467 := by decide +kernel

theorem rowCheck18467 : row18467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18467 := by decide +kernel

theorem rowEval18467 (x : Key → ℝ) : Integer.Sparse.eval row18467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18467, Integer.Sparse.eval_collectBalanced, rawRowCheck18467]

theorem rawRowCheck18468 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18468 := by decide +kernel

theorem rowCheck18468 : row18468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18468 := by decide +kernel

theorem rowEval18468 (x : Key → ℝ) : Integer.Sparse.eval row18468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18468, Integer.Sparse.eval_collectBalanced, rawRowCheck18468]

theorem rawRowCheck18469 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18469 := by decide +kernel

theorem rowCheck18469 : row18469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18469 := by decide +kernel

theorem rowEval18469 (x : Key → ℝ) : Integer.Sparse.eval row18469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18469, Integer.Sparse.eval_collectBalanced, rawRowCheck18469]

theorem rawRowCheck18470 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18470 := by decide +kernel

theorem rowCheck18470 : row18470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18470 := by decide +kernel

theorem rowEval18470 (x : Key → ℝ) : Integer.Sparse.eval row18470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18470, Integer.Sparse.eval_collectBalanced, rawRowCheck18470]

theorem rawRowCheck18471 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18471 := by decide +kernel

theorem rowCheck18471 : row18471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18471 := by decide +kernel

theorem rowEval18471 (x : Key → ℝ) : Integer.Sparse.eval row18471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18471, Integer.Sparse.eval_collectBalanced, rawRowCheck18471]

theorem rawRowCheck18472 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18472 := by decide +kernel

theorem rowCheck18472 : row18472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18472 := by decide +kernel

theorem rowEval18472 (x : Key → ℝ) : Integer.Sparse.eval row18472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18472, Integer.Sparse.eval_collectBalanced, rawRowCheck18472]

theorem rawRowCheck18473 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18473 := by decide +kernel

theorem rowCheck18473 : row18473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18473 := by decide +kernel

theorem rowEval18473 (x : Key → ℝ) : Integer.Sparse.eval row18473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18473, Integer.Sparse.eval_collectBalanced, rawRowCheck18473]

theorem rawRowCheck18474 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow18474 := by decide +kernel

theorem rowCheck18474 : row18474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18474 := by decide +kernel

theorem rowEval18474 (x : Key → ℝ) : Integer.Sparse.eval row18474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18474, Integer.Sparse.eval_collectBalanced, rawRowCheck18474]

theorem rawRowCheck18475 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow18475 := by decide +kernel

theorem rowCheck18475 : row18475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18475 := by decide +kernel

theorem rowEval18475 (x : Key → ℝ) : Integer.Sparse.eval row18475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18475, Integer.Sparse.eval_collectBalanced, rawRowCheck18475]

theorem rawRowCheck18476 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow18476 := by decide +kernel

theorem rowCheck18476 : row18476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18476 := by decide +kernel

theorem rowEval18476 (x : Key → ℝ) : Integer.Sparse.eval row18476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18476, Integer.Sparse.eval_collectBalanced, rawRowCheck18476]

theorem rawRowCheck18477 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow18477 := by decide +kernel

theorem rowCheck18477 : row18477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18477 := by decide +kernel

theorem rowEval18477 (x : Key → ℝ) : Integer.Sparse.eval row18477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18477, Integer.Sparse.eval_collectBalanced, rawRowCheck18477]

theorem rawRowCheck18478 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow18478 := by decide +kernel

theorem rowCheck18478 : row18478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18478 := by decide +kernel

theorem rowEval18478 (x : Key → ℝ) : Integer.Sparse.eval row18478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18478, Integer.Sparse.eval_collectBalanced, rawRowCheck18478]

theorem rawRowCheck18479 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow18479 := by decide +kernel

theorem rowCheck18479 : row18479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18479 := by decide +kernel

theorem rowEval18479 (x : Key → ℝ) : Integer.Sparse.eval row18479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18479, Integer.Sparse.eval_collectBalanced, rawRowCheck18479]

theorem rawRowCheck18480 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18480 := by decide +kernel

theorem rowCheck18480 : row18480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18480 := by decide +kernel

theorem rowEval18480 (x : Key → ℝ) : Integer.Sparse.eval row18480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18480, Integer.Sparse.eval_collectBalanced, rawRowCheck18480]

theorem rawRowCheck18481 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18481 := by decide +kernel

theorem rowCheck18481 : row18481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18481 := by decide +kernel

theorem rowEval18481 (x : Key → ℝ) : Integer.Sparse.eval row18481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18481, Integer.Sparse.eval_collectBalanced, rawRowCheck18481]

theorem rawRowCheck18482 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18482 := by decide +kernel

theorem rowCheck18482 : row18482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18482 := by decide +kernel

theorem rowEval18482 (x : Key → ℝ) : Integer.Sparse.eval row18482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18482, Integer.Sparse.eval_collectBalanced, rawRowCheck18482]

theorem rawRowCheck18507 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow18507 := by decide +kernel

theorem rowCheck18507 : row18507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18507 := by decide +kernel

theorem rowEval18507 (x : Key → ℝ) : Integer.Sparse.eval row18507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18507, Integer.Sparse.eval_collectBalanced, rawRowCheck18507]

theorem rawRowCheck18508 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow18508 := by decide +kernel

theorem rowCheck18508 : row18508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18508 := by decide +kernel

theorem rowEval18508 (x : Key → ℝ) : Integer.Sparse.eval row18508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18508, Integer.Sparse.eval_collectBalanced, rawRowCheck18508]

theorem rawRowCheck18509 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow18509 := by decide +kernel

theorem rowCheck18509 : row18509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18509 := by decide +kernel

theorem rowEval18509 (x : Key → ℝ) : Integer.Sparse.eval row18509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18509, Integer.Sparse.eval_collectBalanced, rawRowCheck18509]

theorem rawRowCheck18510 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow18510 := by decide +kernel

theorem rowCheck18510 : row18510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18510 := by decide +kernel

theorem rowEval18510 (x : Key → ℝ) : Integer.Sparse.eval row18510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18510, Integer.Sparse.eval_collectBalanced, rawRowCheck18510]

theorem rawRowCheck18511 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow18511 := by decide +kernel

theorem rowCheck18511 : row18511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18511 := by decide +kernel

theorem rowEval18511 (x : Key → ℝ) : Integer.Sparse.eval row18511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18511, Integer.Sparse.eval_collectBalanced, rawRowCheck18511]

theorem rawRowCheck18512 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow18512 := by decide +kernel

theorem rowCheck18512 : row18512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18512 := by decide +kernel

theorem rowEval18512 (x : Key → ℝ) : Integer.Sparse.eval row18512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18512, Integer.Sparse.eval_collectBalanced, rawRowCheck18512]

theorem rawRowCheck18513 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow18513 := by decide +kernel

theorem rowCheck18513 : row18513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18513 := by decide +kernel

theorem rowEval18513 (x : Key → ℝ) : Integer.Sparse.eval row18513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18513, Integer.Sparse.eval_collectBalanced, rawRowCheck18513]

theorem rawRowCheck18514 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow18514 := by decide +kernel

theorem rowCheck18514 : row18514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18514 := by decide +kernel

theorem rowEval18514 (x : Key → ℝ) : Integer.Sparse.eval row18514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18514, Integer.Sparse.eval_collectBalanced, rawRowCheck18514]

theorem rawRowCheck18515 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow18515 := by decide +kernel

theorem rowCheck18515 : row18515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18515 := by decide +kernel

theorem rowEval18515 (x : Key → ℝ) : Integer.Sparse.eval row18515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18515, Integer.Sparse.eval_collectBalanced, rawRowCheck18515]

theorem rawRowCheck18516 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow18516 := by decide +kernel

theorem rowCheck18516 : row18516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18516 := by decide +kernel

theorem rowEval18516 (x : Key → ℝ) : Integer.Sparse.eval row18516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18516, Integer.Sparse.eval_collectBalanced, rawRowCheck18516]

theorem rawRowCheck18517 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow18517 := by decide +kernel

theorem rowCheck18517 : row18517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18517 := by decide +kernel

theorem rowEval18517 (x : Key → ℝ) : Integer.Sparse.eval row18517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18517, Integer.Sparse.eval_collectBalanced, rawRowCheck18517]

theorem rawRowCheck18518 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow18518 := by decide +kernel

theorem rowCheck18518 : row18518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18518 := by decide +kernel

theorem rowEval18518 (x : Key → ℝ) : Integer.Sparse.eval row18518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18518, Integer.Sparse.eval_collectBalanced, rawRowCheck18518]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound2_0_e_oai (k : Fin GramFunctions.Block5.form2.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows2_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form2.terms k).tag (GramFunctions.Block5.form2.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval18459 x
  · exact rowEval18460 x
  · exact rowEval18461 x
  · exact rowEval18462 x
  · exact rowEval18463 x
  · exact rowEval18464 x
  · exact rowEval18465 x
  · exact rowEval18466 x
  · exact rowEval18467 x
  · exact rowEval18468 x
  · exact rowEval18469 x
  · exact rowEval18470 x
  · exact rowEval18471 x
  · exact rowEval18472 x
  · exact rowEval18473 x
  · exact rowEval18474 x
  · exact rowEval18475 x
  · exact rowEval18476 x
  · exact rowEval18477 x
  · exact rowEval18478 x
  · exact rowEval18479 x
  · exact rowEval18480 x
  · exact rowEval18481 x
  · exact rowEval18482 x
  · exact rowEval18483_e x
  · exact rowEval18484_e x
  · exact rowEval18485_e x
  · exact rowEval18486_e x
  · exact rowEval18487_e x
  · exact rowEval18488_e x
  · exact rowEval18489_e x
  · exact rowEval18490_e x
  · exact rowEval18491_e x
  · exact rowEval18492_e x
  · exact rowEval18493_e x
  · exact rowEval18494_e x
  · exact rowEval18495_e x
  · exact rowEval18496_e x
  · exact rowEval18497_e x
  · exact rowEval18498_e x
  · exact rowEval18499_e x
  · exact rowEval18500_e x
  · exact rowEval18501_e x
  · exact rowEval18502_e x
  · exact rowEval18503_e x
  · exact rowEval18504_e x
  · exact rowEval18505_e x
  · exact rowEval18506_e x
  · exact rowEval18507 x
  · exact rowEval18508 x
  · exact rowEval18509 x
  · exact rowEval18510 x
  · exact rowEval18511 x
  · exact rowEval18512 x
  · exact rowEval18513 x
  · exact rowEval18514 x
  · exact rowEval18515 x
  · exact rowEval18516 x
  · exact rowEval18517 x
  · exact rowEval18518 x

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.rowsSound2_0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.rowsSound2_0_e_oai
