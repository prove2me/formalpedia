-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:09:11.247226+00:00
-- url     : https://prove2.me/submissions/9196f979-12f4-47a8-98de-a26e2d9edc79

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E033
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E056
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7766_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7767_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7768_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7769_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7770_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7771_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7772_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7773_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7784_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7785_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7786_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7787_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7788_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7789_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8329_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7774 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5 = rawRow7774 := by decide +kernel

theorem rowCheck7774 : row7774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7774 := by decide +kernel

theorem rowEval7774 (x : Key → ℝ) : Integer.Sparse.eval row7774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7774, Integer.Sparse.eval_collectBalanced, rawRowCheck7774]

theorem rawRowCheck7775 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5 = rawRow7775 := by decide +kernel

theorem rowCheck7775 : row7775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7775 := by decide +kernel

theorem rowEval7775 (x : Key → ℝ) : Integer.Sparse.eval row7775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7775, Integer.Sparse.eval_collectBalanced, rawRowCheck7775]

theorem rawRowCheck7776 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5 = rawRow7776 := by decide +kernel

theorem rowCheck7776 : row7776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7776 := by decide +kernel

theorem rowEval7776 (x : Key → ℝ) : Integer.Sparse.eval row7776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck7776, Integer.Sparse.eval_collectBalanced, rawRowCheck7776]

theorem rawRowCheck7777 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5 = rawRow7777 := by decide +kernel

theorem rowCheck7777 : row7777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7777 := by decide +kernel

theorem rowEval7777 (x : Key → ℝ) : Integer.Sparse.eval row7777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7777, Integer.Sparse.eval_collectBalanced, rawRowCheck7777]

theorem rawRowCheck7778 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5 = rawRow7778 := by decide +kernel

theorem rowCheck7778 : row7778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7778 := by decide +kernel

theorem rowEval7778 (x : Key → ℝ) : Integer.Sparse.eval row7778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7778, Integer.Sparse.eval_collectBalanced, rawRowCheck7778]

theorem rawRowCheck7779 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5 = rawRow7779 := by decide +kernel

theorem rowCheck7779 : row7779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7779 := by decide +kernel

theorem rowEval7779 (x : Key → ℝ) : Integer.Sparse.eval row7779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7779, Integer.Sparse.eval_collectBalanced, rawRowCheck7779]

theorem rawRowCheck7780 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5 = rawRow7780 := by decide +kernel

theorem rowCheck7780 : row7780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7780 := by decide +kernel

theorem rowEval7780 (x : Key → ℝ) : Integer.Sparse.eval row7780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7780, Integer.Sparse.eval_collectBalanced, rawRowCheck7780]

theorem rawRowCheck7781 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5 = rawRow7781 := by decide +kernel

theorem rowCheck7781 : row7781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7781 := by decide +kernel

theorem rowEval7781 (x : Key → ℝ) : Integer.Sparse.eval row7781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7781, Integer.Sparse.eval_collectBalanced, rawRowCheck7781]

theorem rawRowCheck7782 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5 = rawRow7782 := by decide +kernel

theorem rowCheck7782 : row7782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7782 := by decide +kernel

theorem rowEval7782 (x : Key → ℝ) : Integer.Sparse.eval row7782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck7782, Integer.Sparse.eval_collectBalanced, rawRowCheck7782]

theorem rawRowCheck7783 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5 = rawRow7783 := by decide +kernel

theorem rowCheck7783 : row7783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7783 := by decide +kernel

theorem rowEval7783 (x : Key → ℝ) : Integer.Sparse.eval row7783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck7783, Integer.Sparse.eval_collectBalanced, rawRowCheck7783]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8330 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow8330 := by decide +kernel

theorem rowCheck8330 : row8330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8330 := by decide +kernel

theorem rowEval8330 (x : Key → ℝ) : Integer.Sparse.eval row8330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8330, Integer.Sparse.eval_collectBalanced, rawRowCheck8330]

theorem rawRowCheck8331 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow8331 := by decide +kernel

theorem rowCheck8331 : row8331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8331 := by decide +kernel

theorem rowEval8331 (x : Key → ℝ) : Integer.Sparse.eval row8331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8331, Integer.Sparse.eval_collectBalanced, rawRowCheck8331]

theorem rawRowCheck8332 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8332 := by decide +kernel

theorem rowCheck8332 : row8332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8332 := by decide +kernel

theorem rowEval8332 (x : Key → ℝ) : Integer.Sparse.eval row8332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8332, Integer.Sparse.eval_collectBalanced, rawRowCheck8332]

theorem rawRowCheck8333 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8333 := by decide +kernel

theorem rowCheck8333 : row8333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8333 := by decide +kernel

theorem rowEval8333 (x : Key → ℝ) : Integer.Sparse.eval row8333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8333, Integer.Sparse.eval_collectBalanced, rawRowCheck8333]

theorem rawRowCheck8334 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8334 := by decide +kernel

theorem rowCheck8334 : row8334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8334 := by decide +kernel

theorem rowEval8334 (x : Key → ℝ) : Integer.Sparse.eval row8334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8334, Integer.Sparse.eval_collectBalanced, rawRowCheck8334]

theorem rawRowCheck8335 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form5 = rawRow8335 := by decide +kernel

theorem rowCheck8335 : row8335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8335 := by decide +kernel

theorem rowEval8335 (x : Key → ℝ) : Integer.Sparse.eval row8335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8335, Integer.Sparse.eval_collectBalanced, rawRowCheck8335]

theorem rawRowCheck8336 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form5 = rawRow8336 := by decide +kernel

theorem rowCheck8336 : row8336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8336 := by decide +kernel

theorem rowEval8336 (x : Key → ℝ) : Integer.Sparse.eval row8336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8336, Integer.Sparse.eval_collectBalanced, rawRowCheck8336]

theorem rawRowCheck8337 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form5 = rawRow8337 := by decide +kernel

theorem rowCheck8337 : row8337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8337 := by decide +kernel

theorem rowEval8337 (x : Key → ℝ) : Integer.Sparse.eval row8337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8337, Integer.Sparse.eval_collectBalanced, rawRowCheck8337]

theorem rawRowCheck8338 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form5 = rawRow8338 := by decide +kernel

theorem rowCheck8338 : row8338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8338 := by decide +kernel

theorem rowEval8338 (x : Key → ℝ) : Integer.Sparse.eval row8338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8338, Integer.Sparse.eval_collectBalanced, rawRowCheck8338]

theorem rawRowCheck8339 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form5 = rawRow8339 := by decide +kernel

theorem rowCheck8339 : row8339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8339 := by decide +kernel

theorem rowEval8339 (x : Key → ℝ) : Integer.Sparse.eval row8339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8339, Integer.Sparse.eval_collectBalanced, rawRowCheck8339]

theorem rawRowCheck8340 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form5 = rawRow8340 := by decide +kernel

theorem rowCheck8340 : row8340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8340 := by decide +kernel

theorem rowEval8340 (x : Key → ℝ) : Integer.Sparse.eval row8340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8340, Integer.Sparse.eval_collectBalanced, rawRowCheck8340]

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

theorem rowsSound9_5_e_oai (k : Fin GramFunctions.Block3.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form9.terms k).tag (GramFunctions.Block3.form9.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval7766_e x
  · exact rowEval7767_e x
  · exact rowEval7768_e x
  · exact rowEval7769_e x
  · exact rowEval7770_e x
  · exact rowEval7771_e x
  · exact rowEval7772_e x
  · exact rowEval7773_e x
  · exact rowEval7774 x
  · exact rowEval7775 x
  · exact rowEval7776 x
  · exact rowEval7777 x
  · exact rowEval7778 x
  · exact rowEval7779 x
  · exact rowEval7780 x
  · exact rowEval7781 x
  · exact rowEval7782 x
  · exact rowEval7783 x
  · exact rowEval7784_e x
  · exact rowEval7785_e x
  · exact rowEval7786_e x
  · exact rowEval7787_e x
  · exact rowEval7788_e x
  · exact rowEval7789_e x
  · exact rowEval8329_e x
  · exact rowEval8330 x
  · exact rowEval8331 x
  · exact rowEval8332 x
  · exact rowEval8333 x
  · exact rowEval8334 x
  · exact rowEval8335 x
  · exact rowEval8336 x
  · exact rowEval8337 x
  · exact rowEval8338 x
  · exact rowEval8339 x
  · exact rowEval8340 x

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_5_e_oai
