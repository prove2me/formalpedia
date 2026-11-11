-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.rowsSound4_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:45:18.433865+00:00
-- url     : https://prove2.me/submissions/c8eee66d-b91a-4814-8a08-2173dddc6d39

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E052

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck462 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1 = rawRow462 := by decide +kernel

theorem rowCheck462 : row462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow462 := by decide +kernel

theorem rowEval462 (x : Key → ℝ) : Integer.Sparse.eval row462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck462, Integer.Sparse.eval_collectBalanced, rawRowCheck462]

theorem rawRowCheck463 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1 = rawRow463 := by decide +kernel

theorem rowCheck463 : row463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow463 := by decide +kernel

theorem rowEval463 (x : Key → ℝ) : Integer.Sparse.eval row463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck463, Integer.Sparse.eval_collectBalanced, rawRowCheck463]

theorem rawRowCheck464 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1 = rawRow464 := by decide +kernel

theorem rowCheck464 : row464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow464 := by decide +kernel

theorem rowEval464 (x : Key → ℝ) : Integer.Sparse.eval row464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck464, Integer.Sparse.eval_collectBalanced, rawRowCheck464]

theorem rawRowCheck465 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1 = rawRow465 := by decide +kernel

theorem rowCheck465 : row465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow465 := by decide +kernel

theorem rowEval465 (x : Key → ℝ) : Integer.Sparse.eval row465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck465, Integer.Sparse.eval_collectBalanced, rawRowCheck465]

theorem rawRowCheck466 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1 = rawRow466 := by decide +kernel

theorem rowCheck466 : row466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow466 := by decide +kernel

theorem rowEval466 (x : Key → ℝ) : Integer.Sparse.eval row466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck466, Integer.Sparse.eval_collectBalanced, rawRowCheck466]

theorem rawRowCheck467 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1 = rawRow467 := by decide +kernel

theorem rowCheck467 : row467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow467 := by decide +kernel

theorem rowEval467 (x : Key → ℝ) : Integer.Sparse.eval row467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck467, Integer.Sparse.eval_collectBalanced, rawRowCheck467]

theorem rawRowCheck468 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1 = rawRow468 := by decide +kernel

theorem rowCheck468 : row468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow468 := by decide +kernel

theorem rowEval468 (x : Key → ℝ) : Integer.Sparse.eval row468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck468, Integer.Sparse.eval_collectBalanced, rawRowCheck468]

theorem rawRowCheck469 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1 = rawRow469 := by decide +kernel

theorem rowCheck469 : row469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow469 := by decide +kernel

theorem rowEval469 (x : Key → ℝ) : Integer.Sparse.eval row469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck469, Integer.Sparse.eval_collectBalanced, rawRowCheck469]

theorem rawRowCheck470 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1 = rawRow470 := by decide +kernel

theorem rowCheck470 : row470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow470 := by decide +kernel

theorem rowEval470 (x : Key → ℝ) : Integer.Sparse.eval row470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck470, Integer.Sparse.eval_collectBalanced, rawRowCheck470]

theorem rawRowCheck471 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1 = rawRow471 := by decide +kernel

theorem rowCheck471 : row471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow471 := by decide +kernel

theorem rowEval471 (x : Key → ℝ) : Integer.Sparse.eval row471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck471, Integer.Sparse.eval_collectBalanced, rawRowCheck471]

theorem rawRowCheck472 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1 = rawRow472 := by decide +kernel

theorem rowCheck472 : row472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow472 := by decide +kernel

theorem rowEval472 (x : Key → ℝ) : Integer.Sparse.eval row472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck472, Integer.Sparse.eval_collectBalanced, rawRowCheck472]

theorem rawRowCheck473 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1 = rawRow473 := by decide +kernel

theorem rowCheck473 : row473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow473 := by decide +kernel

theorem rowEval473 (x : Key → ℝ) : Integer.Sparse.eval row473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck473, Integer.Sparse.eval_collectBalanced, rawRowCheck473]

theorem rawRowCheck474 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1 = rawRow474 := by decide +kernel

theorem rowCheck474 : row474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow474 := by decide +kernel

theorem rowEval474 (x : Key → ℝ) : Integer.Sparse.eval row474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck474, Integer.Sparse.eval_collectBalanced, rawRowCheck474]

theorem rawRowCheck475 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1 = rawRow475 := by decide +kernel

theorem rowCheck475 : row475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow475 := by decide +kernel

theorem rowEval475 (x : Key → ℝ) : Integer.Sparse.eval row475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck475, Integer.Sparse.eval_collectBalanced, rawRowCheck475]

theorem rawRowCheck476 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1 = rawRow476 := by decide +kernel

theorem rowCheck476 : row476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow476 := by decide +kernel

theorem rowEval476 (x : Key → ℝ) : Integer.Sparse.eval row476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck476, Integer.Sparse.eval_collectBalanced, rawRowCheck476]

theorem rawRowCheck477 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1 = rawRow477 := by decide +kernel

theorem rowCheck477 : row477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow477 := by decide +kernel

theorem rowEval477 (x : Key → ℝ) : Integer.Sparse.eval row477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck477, Integer.Sparse.eval_collectBalanced, rawRowCheck477]

theorem rawRowCheck478 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1 = rawRow478 := by decide +kernel

theorem rowCheck478 : row478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow478 := by decide +kernel

theorem rowEval478 (x : Key → ℝ) : Integer.Sparse.eval row478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck478, Integer.Sparse.eval_collectBalanced, rawRowCheck478]

theorem rawRowCheck479 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow479 := by decide +kernel

theorem rowCheck479 : row479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow479 := by decide +kernel

theorem rowEval479 (x : Key → ℝ) : Integer.Sparse.eval row479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck479, Integer.Sparse.eval_collectBalanced, rawRowCheck479]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck480 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow480 := by decide +kernel

theorem rowCheck480 : row480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow480 := by decide +kernel

theorem rowEval480 (x : Key → ℝ) : Integer.Sparse.eval row480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck480, Integer.Sparse.eval_collectBalanced, rawRowCheck480]

theorem rawRowCheck481 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow481 := by decide +kernel

theorem rowCheck481 : row481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow481 := by decide +kernel

theorem rowEval481 (x : Key → ℝ) : Integer.Sparse.eval row481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck481, Integer.Sparse.eval_collectBalanced, rawRowCheck481]

theorem rawRowCheck482 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow482 := by decide +kernel

theorem rowCheck482 : row482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow482 := by decide +kernel

theorem rowEval482 (x : Key → ℝ) : Integer.Sparse.eval row482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck482, Integer.Sparse.eval_collectBalanced, rawRowCheck482]

theorem rawRowCheck483 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow483 := by decide +kernel

theorem rowCheck483 : row483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow483 := by decide +kernel

theorem rowEval483 (x : Key → ℝ) : Integer.Sparse.eval row483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck483, Integer.Sparse.eval_collectBalanced, rawRowCheck483]

theorem rawRowCheck484 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1 = rawRow484 := by decide +kernel

theorem rowCheck484 : row484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow484 := by decide +kernel

theorem rowEval484 (x : Key → ℝ) : Integer.Sparse.eval row484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck484, Integer.Sparse.eval_collectBalanced, rawRowCheck484]

theorem rawRowCheck485 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1 = rawRow485 := by decide +kernel

theorem rowCheck485 : row485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow485 := by decide +kernel

theorem rowEval485 (x : Key → ℝ) : Integer.Sparse.eval row485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck485, Integer.Sparse.eval_collectBalanced, rawRowCheck485]

theorem rawRowCheck486 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow486 := by decide +kernel

theorem rowCheck486 : row486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow486 := by decide +kernel

theorem rowEval486 (x : Key → ℝ) : Integer.Sparse.eval row486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck486, Integer.Sparse.eval_collectBalanced, rawRowCheck486]

theorem rawRowCheck487 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow487 := by decide +kernel

theorem rowCheck487 : row487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow487 := by decide +kernel

theorem rowEval487 (x : Key → ℝ) : Integer.Sparse.eval row487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck487, Integer.Sparse.eval_collectBalanced, rawRowCheck487]

theorem rawRowCheck488 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1 = rawRow488 := by decide +kernel

theorem rowCheck488 : row488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow488 := by decide +kernel

theorem rowEval488 (x : Key → ℝ) : Integer.Sparse.eval row488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck488, Integer.Sparse.eval_collectBalanced, rawRowCheck488]

theorem rawRowCheck489 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1 = rawRow489 := by decide +kernel

theorem rowCheck489 : row489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow489 := by decide +kernel

theorem rowEval489 (x : Key → ℝ) : Integer.Sparse.eval row489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck489, Integer.Sparse.eval_collectBalanced, rawRowCheck489]

theorem rawRowCheck490 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1 = rawRow490 := by decide +kernel

theorem rowCheck490 : row490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow490 := by decide +kernel

theorem rowEval490 (x : Key → ℝ) : Integer.Sparse.eval row490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck490, Integer.Sparse.eval_collectBalanced, rawRowCheck490]

theorem rawRowCheck491 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1 = rawRow491 := by decide +kernel

theorem rowCheck491 : row491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow491 := by decide +kernel

theorem rowEval491 (x : Key → ℝ) : Integer.Sparse.eval row491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck491, Integer.Sparse.eval_collectBalanced, rawRowCheck491]

theorem rawRowCheck492 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1 = rawRow492 := by decide +kernel

theorem rowCheck492 : row492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow492 := by decide +kernel

theorem rowEval492 (x : Key → ℝ) : Integer.Sparse.eval row492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck492, Integer.Sparse.eval_collectBalanced, rawRowCheck492]

theorem rawRowCheck493 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1 = rawRow493 := by decide +kernel

theorem rowCheck493 : row493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow493 := by decide +kernel

theorem rowEval493 (x : Key → ℝ) : Integer.Sparse.eval row493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck493, Integer.Sparse.eval_collectBalanced, rawRowCheck493]

theorem rawRowCheck494 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1 = rawRow494 := by decide +kernel

theorem rowCheck494 : row494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow494 := by decide +kernel

theorem rowEval494 (x : Key → ℝ) : Integer.Sparse.eval row494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck494, Integer.Sparse.eval_collectBalanced, rawRowCheck494]

theorem rawRowCheck495 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1 = rawRow495 := by decide +kernel

theorem rowCheck495 : row495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow495 := by decide +kernel

theorem rowEval495 (x : Key → ℝ) : Integer.Sparse.eval row495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck495, Integer.Sparse.eval_collectBalanced, rawRowCheck495]

theorem rawRowCheck496 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1 = rawRow496 := by decide +kernel

theorem rowCheck496 : row496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow496 := by decide +kernel

theorem rowEval496 (x : Key → ℝ) : Integer.Sparse.eval row496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck496, Integer.Sparse.eval_collectBalanced, rawRowCheck496]

theorem rawRowCheck497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow497 := by decide +kernel

theorem rowCheck497 : row497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow497 := by decide +kernel

theorem rowEval497 (x : Key → ℝ) : Integer.Sparse.eval row497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck497, Integer.Sparse.eval_collectBalanced, rawRowCheck497]

theorem rawRowCheck498 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow498 := by decide +kernel

theorem rowCheck498 : row498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow498 := by decide +kernel

theorem rowEval498 (x : Key → ℝ) : Integer.Sparse.eval row498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck498, Integer.Sparse.eval_collectBalanced, rawRowCheck498]

theorem rawRowCheck499 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow499 := by decide +kernel

theorem rowCheck499 : row499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow499 := by decide +kernel

theorem rowEval499 (x : Key → ℝ) : Integer.Sparse.eval row499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck499, Integer.Sparse.eval_collectBalanced, rawRowCheck499]

theorem rawRowCheck500 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1 = rawRow500 := by decide +kernel

theorem rowCheck500 : row500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow500 := by decide +kernel

theorem rowEval500 (x : Key → ℝ) : Integer.Sparse.eval row500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck500, Integer.Sparse.eval_collectBalanced, rawRowCheck500]

theorem rawRowCheck501 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1 = rawRow501 := by decide +kernel

theorem rowCheck501 : row501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow501 := by decide +kernel

theorem rowEval501 (x : Key → ℝ) : Integer.Sparse.eval row501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck501, Integer.Sparse.eval_collectBalanced, rawRowCheck501]

theorem rawRowCheck502 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1 = rawRow502 := by decide +kernel

theorem rowCheck502 : row502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow502 := by decide +kernel

theorem rowEval502 (x : Key → ℝ) : Integer.Sparse.eval row502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck502, Integer.Sparse.eval_collectBalanced, rawRowCheck502]

theorem rawRowCheck503 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1 = rawRow503 := by decide +kernel

theorem rowCheck503 : row503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow503 := by decide +kernel

theorem rowEval503 (x : Key → ℝ) : Integer.Sparse.eval row503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck503, Integer.Sparse.eval_collectBalanced, rawRowCheck503]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound4_1_e_oai (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval462 x
  · exact rowEval463 x
  · exact rowEval464 x
  · exact rowEval465 x
  · exact rowEval466 x
  · exact rowEval467 x
  · exact rowEval468 x
  · exact rowEval469 x
  · exact rowEval470 x
  · exact rowEval471 x
  · exact rowEval472 x
  · exact rowEval473 x
  · exact rowEval474 x
  · exact rowEval475 x
  · exact rowEval476 x
  · exact rowEval477 x
  · exact rowEval478 x
  · exact rowEval479 x
  · exact rowEval480 x
  · exact rowEval481 x
  · exact rowEval482 x
  · exact rowEval483 x
  · exact rowEval484 x
  · exact rowEval485 x
  · exact rowEval486 x
  · exact rowEval487 x
  · exact rowEval488 x
  · exact rowEval489 x
  · exact rowEval490 x
  · exact rowEval491 x
  · exact rowEval492 x
  · exact rowEval493 x
  · exact rowEval494 x
  · exact rowEval495 x
  · exact rowEval496 x
  · exact rowEval497 x
  · exact rowEval498 x
  · exact rowEval499 x
  · exact rowEval500 x
  · exact rowEval501 x
  · exact rowEval502 x
  · exact rowEval503 x

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound4_1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound4_1_e_oai
