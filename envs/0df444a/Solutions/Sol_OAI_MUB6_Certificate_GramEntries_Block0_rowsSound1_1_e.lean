-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.rowsSound1_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:45:16.037668+00:00
-- url     : https://prove2.me/submissions/a5cf2cfb-eddf-4fb7-bd85-45975ca5bd46

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E057

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck84 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1 = rawRow84 := by decide +kernel

theorem rowCheck84 : row84 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow84 := by decide +kernel

theorem rowEval84 (x : Key → ℝ) : Integer.Sparse.eval row84 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck84, Integer.Sparse.eval_collectBalanced, rawRowCheck84]

theorem rawRowCheck85 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1 = rawRow85 := by decide +kernel

theorem rowCheck85 : row85 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow85 := by decide +kernel

theorem rowEval85 (x : Key → ℝ) : Integer.Sparse.eval row85 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck85, Integer.Sparse.eval_collectBalanced, rawRowCheck85]

theorem rawRowCheck86 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1 = rawRow86 := by decide +kernel

theorem rowCheck86 : row86 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow86 := by decide +kernel

theorem rowEval86 (x : Key → ℝ) : Integer.Sparse.eval row86 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck86, Integer.Sparse.eval_collectBalanced, rawRowCheck86]

theorem rawRowCheck87 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1 = rawRow87 := by decide +kernel

theorem rowCheck87 : row87 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow87 := by decide +kernel

theorem rowEval87 (x : Key → ℝ) : Integer.Sparse.eval row87 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck87, Integer.Sparse.eval_collectBalanced, rawRowCheck87]

theorem rawRowCheck88 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1 = rawRow88 := by decide +kernel

theorem rowCheck88 : row88 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow88 := by decide +kernel

theorem rowEval88 (x : Key → ℝ) : Integer.Sparse.eval row88 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck88, Integer.Sparse.eval_collectBalanced, rawRowCheck88]

theorem rawRowCheck89 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1 = rawRow89 := by decide +kernel

theorem rowCheck89 : row89 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow89 := by decide +kernel

theorem rowEval89 (x : Key → ℝ) : Integer.Sparse.eval row89 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck89, Integer.Sparse.eval_collectBalanced, rawRowCheck89]

theorem rawRowCheck90 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1 = rawRow90 := by decide +kernel

theorem rowCheck90 : row90 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow90 := by decide +kernel

theorem rowEval90 (x : Key → ℝ) : Integer.Sparse.eval row90 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck90, Integer.Sparse.eval_collectBalanced, rawRowCheck90]

theorem rawRowCheck91 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1 = rawRow91 := by decide +kernel

theorem rowCheck91 : row91 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow91 := by decide +kernel

theorem rowEval91 (x : Key → ℝ) : Integer.Sparse.eval row91 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck91, Integer.Sparse.eval_collectBalanced, rawRowCheck91]

theorem rawRowCheck92 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1 = rawRow92 := by decide +kernel

theorem rowCheck92 : row92 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow92 := by decide +kernel

theorem rowEval92 (x : Key → ℝ) : Integer.Sparse.eval row92 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck92, Integer.Sparse.eval_collectBalanced, rawRowCheck92]

theorem rawRowCheck93 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1 = rawRow93 := by decide +kernel

theorem rowCheck93 : row93 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow93 := by decide +kernel

theorem rowEval93 (x : Key → ℝ) : Integer.Sparse.eval row93 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck93, Integer.Sparse.eval_collectBalanced, rawRowCheck93]

theorem rawRowCheck94 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1 = rawRow94 := by decide +kernel

theorem rowCheck94 : row94 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow94 := by decide +kernel

theorem rowEval94 (x : Key → ℝ) : Integer.Sparse.eval row94 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck94, Integer.Sparse.eval_collectBalanced, rawRowCheck94]

theorem rawRowCheck95 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1 = rawRow95 := by decide +kernel

theorem rowCheck95 : row95 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow95 := by decide +kernel

theorem rowEval95 (x : Key → ℝ) : Integer.Sparse.eval row95 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck95, Integer.Sparse.eval_collectBalanced, rawRowCheck95]

theorem rawRowCheck96 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1 = rawRow96 := by decide +kernel

theorem rowCheck96 : row96 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow96 := by decide +kernel

theorem rowEval96 (x : Key → ℝ) : Integer.Sparse.eval row96 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck96, Integer.Sparse.eval_collectBalanced, rawRowCheck96]

theorem rawRowCheck97 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1 = rawRow97 := by decide +kernel

theorem rowCheck97 : row97 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow97 := by decide +kernel

theorem rowEval97 (x : Key → ℝ) : Integer.Sparse.eval row97 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck97, Integer.Sparse.eval_collectBalanced, rawRowCheck97]

theorem rawRowCheck98 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1 = rawRow98 := by decide +kernel

theorem rowCheck98 : row98 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow98 := by decide +kernel

theorem rowEval98 (x : Key → ℝ) : Integer.Sparse.eval row98 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck98, Integer.Sparse.eval_collectBalanced, rawRowCheck98]

theorem rawRowCheck99 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1 = rawRow99 := by decide +kernel

theorem rowCheck99 : row99 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow99 := by decide +kernel

theorem rowEval99 (x : Key → ℝ) : Integer.Sparse.eval row99 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck99, Integer.Sparse.eval_collectBalanced, rawRowCheck99]

theorem rawRowCheck100 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow100 := by decide +kernel

theorem rowCheck100 : row100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow100 := by decide +kernel

theorem rowEval100 (x : Key → ℝ) : Integer.Sparse.eval row100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck100, Integer.Sparse.eval_collectBalanced, rawRowCheck100]

theorem rawRowCheck101 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow101 := by decide +kernel

theorem rowCheck101 : row101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow101 := by decide +kernel

theorem rowEval101 (x : Key → ℝ) : Integer.Sparse.eval row101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck101, Integer.Sparse.eval_collectBalanced, rawRowCheck101]

theorem rawRowCheck102 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow102 := by decide +kernel

theorem rowCheck102 : row102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow102 := by decide +kernel

theorem rowEval102 (x : Key → ℝ) : Integer.Sparse.eval row102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck102, Integer.Sparse.eval_collectBalanced, rawRowCheck102]

theorem rawRowCheck103 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow103 := by decide +kernel

theorem rowCheck103 : row103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow103 := by decide +kernel

theorem rowEval103 (x : Key → ℝ) : Integer.Sparse.eval row103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck103, Integer.Sparse.eval_collectBalanced, rawRowCheck103]

theorem rawRowCheck104 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1 = rawRow104 := by decide +kernel

theorem rowCheck104 : row104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow104 := by decide +kernel

theorem rowEval104 (x : Key → ℝ) : Integer.Sparse.eval row104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck104, Integer.Sparse.eval_collectBalanced, rawRowCheck104]

theorem rawRowCheck105 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1 = rawRow105 := by decide +kernel

theorem rowCheck105 : row105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow105 := by decide +kernel

theorem rowEval105 (x : Key → ℝ) : Integer.Sparse.eval row105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck105, Integer.Sparse.eval_collectBalanced, rawRowCheck105]

theorem rawRowCheck106 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1 = rawRow106 := by decide +kernel

theorem rowCheck106 : row106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow106 := by decide +kernel

theorem rowEval106 (x : Key → ℝ) : Integer.Sparse.eval row106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck106, Integer.Sparse.eval_collectBalanced, rawRowCheck106]

theorem rawRowCheck107 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1 = rawRow107 := by decide +kernel

theorem rowCheck107 : row107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow107 := by decide +kernel

theorem rowEval107 (x : Key → ℝ) : Integer.Sparse.eval row107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck107, Integer.Sparse.eval_collectBalanced, rawRowCheck107]

theorem rawRowCheck108 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1 = rawRow108 := by decide +kernel

theorem rowCheck108 : row108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow108 := by decide +kernel

theorem rowEval108 (x : Key → ℝ) : Integer.Sparse.eval row108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck108, Integer.Sparse.eval_collectBalanced, rawRowCheck108]

theorem rawRowCheck109 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1 = rawRow109 := by decide +kernel

theorem rowCheck109 : row109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow109 := by decide +kernel

theorem rowEval109 (x : Key → ℝ) : Integer.Sparse.eval row109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck109, Integer.Sparse.eval_collectBalanced, rawRowCheck109]

theorem rawRowCheck110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1 = rawRow110 := by decide +kernel

theorem rowCheck110 : row110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow110 := by decide +kernel

theorem rowEval110 (x : Key → ℝ) : Integer.Sparse.eval row110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck110, Integer.Sparse.eval_collectBalanced, rawRowCheck110]

theorem rawRowCheck111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1 = rawRow111 := by decide +kernel

theorem rowCheck111 : row111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow111 := by decide +kernel

theorem rowEval111 (x : Key → ℝ) : Integer.Sparse.eval row111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck111, Integer.Sparse.eval_collectBalanced, rawRowCheck111]

theorem rawRowCheck112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1 = rawRow112 := by decide +kernel

theorem rowCheck112 : row112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow112 := by decide +kernel

theorem rowEval112 (x : Key → ℝ) : Integer.Sparse.eval row112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck112, Integer.Sparse.eval_collectBalanced, rawRowCheck112]

theorem rawRowCheck113 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1 = rawRow113 := by decide +kernel

theorem rowCheck113 : row113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow113 := by decide +kernel

theorem rowEval113 (x : Key → ℝ) : Integer.Sparse.eval row113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck113, Integer.Sparse.eval_collectBalanced, rawRowCheck113]

theorem rawRowCheck114 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow114 := by decide +kernel

theorem rowCheck114 : row114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow114 := by decide +kernel

theorem rowEval114 (x : Key → ℝ) : Integer.Sparse.eval row114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck114, Integer.Sparse.eval_collectBalanced, rawRowCheck114]

theorem rawRowCheck115 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow115 := by decide +kernel

theorem rowCheck115 : row115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow115 := by decide +kernel

theorem rowEval115 (x : Key → ℝ) : Integer.Sparse.eval row115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck115, Integer.Sparse.eval_collectBalanced, rawRowCheck115]

theorem rawRowCheck116 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1 = rawRow116 := by decide +kernel

theorem rowCheck116 : row116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow116 := by decide +kernel

theorem rowEval116 (x : Key → ℝ) : Integer.Sparse.eval row116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck116, Integer.Sparse.eval_collectBalanced, rawRowCheck116]

theorem rawRowCheck117 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1 = rawRow117 := by decide +kernel

theorem rowCheck117 : row117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow117 := by decide +kernel

theorem rowEval117 (x : Key → ℝ) : Integer.Sparse.eval row117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck117, Integer.Sparse.eval_collectBalanced, rawRowCheck117]

theorem rawRowCheck118 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow118 := by decide +kernel

theorem rowCheck118 : row118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow118 := by decide +kernel

theorem rowEval118 (x : Key → ℝ) : Integer.Sparse.eval row118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck118, Integer.Sparse.eval_collectBalanced, rawRowCheck118]

theorem rawRowCheck119 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow119 := by decide +kernel

theorem rowCheck119 : row119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow119 := by decide +kernel

theorem rowEval119 (x : Key → ℝ) : Integer.Sparse.eval row119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck119, Integer.Sparse.eval_collectBalanced, rawRowCheck119]

theorem rawRowCheck120 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow120 := by decide +kernel

theorem rowCheck120 : row120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow120 := by decide +kernel

theorem rowEval120 (x : Key → ℝ) : Integer.Sparse.eval row120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck120, Integer.Sparse.eval_collectBalanced, rawRowCheck120]

theorem rawRowCheck121 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow121 := by decide +kernel

theorem rowCheck121 : row121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow121 := by decide +kernel

theorem rowEval121 (x : Key → ℝ) : Integer.Sparse.eval row121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck121, Integer.Sparse.eval_collectBalanced, rawRowCheck121]

theorem rawRowCheck122 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1 = rawRow122 := by decide +kernel

theorem rowCheck122 : row122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow122 := by decide +kernel

theorem rowEval122 (x : Key → ℝ) : Integer.Sparse.eval row122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck122, Integer.Sparse.eval_collectBalanced, rawRowCheck122]

theorem rawRowCheck123 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1 = rawRow123 := by decide +kernel

theorem rowCheck123 : row123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow123 := by decide +kernel

theorem rowEval123 (x : Key → ℝ) : Integer.Sparse.eval row123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck123, Integer.Sparse.eval_collectBalanced, rawRowCheck123]

theorem rawRowCheck124 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1 = rawRow124 := by decide +kernel

theorem rowCheck124 : row124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow124 := by decide +kernel

theorem rowEval124 (x : Key → ℝ) : Integer.Sparse.eval row124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck124, Integer.Sparse.eval_collectBalanced, rawRowCheck124]

theorem rawRowCheck125 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1 = rawRow125 := by decide +kernel

theorem rowCheck125 : row125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow125 := by decide +kernel

theorem rowEval125 (x : Key → ℝ) : Integer.Sparse.eval row125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck125, Integer.Sparse.eval_collectBalanced, rawRowCheck125]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound1_1_e_oai (k : Fin GramFunctions.Block0.form1.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows1_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form1.terms k).tag (GramFunctions.Block0.form1.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval84 x
  · exact rowEval85 x
  · exact rowEval86 x
  · exact rowEval87 x
  · exact rowEval88 x
  · exact rowEval89 x
  · exact rowEval90 x
  · exact rowEval91 x
  · exact rowEval92 x
  · exact rowEval93 x
  · exact rowEval94 x
  · exact rowEval95 x
  · exact rowEval96 x
  · exact rowEval97 x
  · exact rowEval98 x
  · exact rowEval99 x
  · exact rowEval100 x
  · exact rowEval101 x
  · exact rowEval102 x
  · exact rowEval103 x
  · exact rowEval104 x
  · exact rowEval105 x
  · exact rowEval106 x
  · exact rowEval107 x
  · exact rowEval108 x
  · exact rowEval109 x
  · exact rowEval110 x
  · exact rowEval111 x
  · exact rowEval112 x
  · exact rowEval113 x
  · exact rowEval114 x
  · exact rowEval115 x
  · exact rowEval116 x
  · exact rowEval117 x
  · exact rowEval118 x
  · exact rowEval119 x
  · exact rowEval120 x
  · exact rowEval121 x
  · exact rowEval122 x
  · exact rowEval123 x
  · exact rowEval124 x
  · exact rowEval125 x

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound1_1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound1_1_e_oai
