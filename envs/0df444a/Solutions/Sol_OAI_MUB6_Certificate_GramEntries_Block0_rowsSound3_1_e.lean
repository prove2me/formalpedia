-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.rowsSound3_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:45:17.181642+00:00
-- url     : https://prove2.me/submissions/3301f686-4f10-4365-b31c-aeb42cc3ea18

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E014
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E051

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck294 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1 = rawRow294 := by decide +kernel

theorem rowCheck294 : row294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow294 := by decide +kernel

theorem rowEval294 (x : Key → ℝ) : Integer.Sparse.eval row294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck294, Integer.Sparse.eval_collectBalanced, rawRowCheck294]

theorem rawRowCheck295 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1 = rawRow295 := by decide +kernel

theorem rowCheck295 : row295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow295 := by decide +kernel

theorem rowEval295 (x : Key → ℝ) : Integer.Sparse.eval row295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck295, Integer.Sparse.eval_collectBalanced, rawRowCheck295]

theorem rawRowCheck296 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1 = rawRow296 := by decide +kernel

theorem rowCheck296 : row296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow296 := by decide +kernel

theorem rowEval296 (x : Key → ℝ) : Integer.Sparse.eval row296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck296, Integer.Sparse.eval_collectBalanced, rawRowCheck296]

theorem rawRowCheck297 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1 = rawRow297 := by decide +kernel

theorem rowCheck297 : row297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow297 := by decide +kernel

theorem rowEval297 (x : Key → ℝ) : Integer.Sparse.eval row297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck297, Integer.Sparse.eval_collectBalanced, rawRowCheck297]

theorem rawRowCheck298 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1 = rawRow298 := by decide +kernel

theorem rowCheck298 : row298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow298 := by decide +kernel

theorem rowEval298 (x : Key → ℝ) : Integer.Sparse.eval row298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck298, Integer.Sparse.eval_collectBalanced, rawRowCheck298]

theorem rawRowCheck299 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1 = rawRow299 := by decide +kernel

theorem rowCheck299 : row299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow299 := by decide +kernel

theorem rowEval299 (x : Key → ℝ) : Integer.Sparse.eval row299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck299, Integer.Sparse.eval_collectBalanced, rawRowCheck299]

theorem rawRowCheck300 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1 = rawRow300 := by decide +kernel

theorem rowCheck300 : row300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow300 := by decide +kernel

theorem rowEval300 (x : Key → ℝ) : Integer.Sparse.eval row300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck300, Integer.Sparse.eval_collectBalanced, rawRowCheck300]

theorem rawRowCheck301 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1 = rawRow301 := by decide +kernel

theorem rowCheck301 : row301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow301 := by decide +kernel

theorem rowEval301 (x : Key → ℝ) : Integer.Sparse.eval row301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck301, Integer.Sparse.eval_collectBalanced, rawRowCheck301]

theorem rawRowCheck302 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1 = rawRow302 := by decide +kernel

theorem rowCheck302 : row302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow302 := by decide +kernel

theorem rowEval302 (x : Key → ℝ) : Integer.Sparse.eval row302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck302, Integer.Sparse.eval_collectBalanced, rawRowCheck302]

theorem rawRowCheck303 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1 = rawRow303 := by decide +kernel

theorem rowCheck303 : row303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow303 := by decide +kernel

theorem rowEval303 (x : Key → ℝ) : Integer.Sparse.eval row303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck303, Integer.Sparse.eval_collectBalanced, rawRowCheck303]

theorem rawRowCheck304 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1 = rawRow304 := by decide +kernel

theorem rowCheck304 : row304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow304 := by decide +kernel

theorem rowEval304 (x : Key → ℝ) : Integer.Sparse.eval row304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck304, Integer.Sparse.eval_collectBalanced, rawRowCheck304]

theorem rawRowCheck305 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1 = rawRow305 := by decide +kernel

theorem rowCheck305 : row305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow305 := by decide +kernel

theorem rowEval305 (x : Key → ℝ) : Integer.Sparse.eval row305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck305, Integer.Sparse.eval_collectBalanced, rawRowCheck305]

theorem rawRowCheck306 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1 = rawRow306 := by decide +kernel

theorem rowCheck306 : row306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow306 := by decide +kernel

theorem rowEval306 (x : Key → ℝ) : Integer.Sparse.eval row306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck306, Integer.Sparse.eval_collectBalanced, rawRowCheck306]

theorem rawRowCheck307 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1 = rawRow307 := by decide +kernel

theorem rowCheck307 : row307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow307 := by decide +kernel

theorem rowEval307 (x : Key → ℝ) : Integer.Sparse.eval row307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck307, Integer.Sparse.eval_collectBalanced, rawRowCheck307]

theorem rawRowCheck308 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1 = rawRow308 := by decide +kernel

theorem rowCheck308 : row308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow308 := by decide +kernel

theorem rowEval308 (x : Key → ℝ) : Integer.Sparse.eval row308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck308, Integer.Sparse.eval_collectBalanced, rawRowCheck308]

theorem rawRowCheck309 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1 = rawRow309 := by decide +kernel

theorem rowCheck309 : row309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow309 := by decide +kernel

theorem rowEval309 (x : Key → ℝ) : Integer.Sparse.eval row309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck309, Integer.Sparse.eval_collectBalanced, rawRowCheck309]

theorem rawRowCheck310 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow310 := by decide +kernel

theorem rowCheck310 : row310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow310 := by decide +kernel

theorem rowEval310 (x : Key → ℝ) : Integer.Sparse.eval row310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck310, Integer.Sparse.eval_collectBalanced, rawRowCheck310]

theorem rawRowCheck311 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow311 := by decide +kernel

theorem rowCheck311 : row311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow311 := by decide +kernel

theorem rowEval311 (x : Key → ℝ) : Integer.Sparse.eval row311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck311, Integer.Sparse.eval_collectBalanced, rawRowCheck311]

theorem rawRowCheck312 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow312 := by decide +kernel

theorem rowCheck312 : row312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow312 := by decide +kernel

theorem rowEval312 (x : Key → ℝ) : Integer.Sparse.eval row312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck312, Integer.Sparse.eval_collectBalanced, rawRowCheck312]

theorem rawRowCheck313 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow313 := by decide +kernel

theorem rowCheck313 : row313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow313 := by decide +kernel

theorem rowEval313 (x : Key → ℝ) : Integer.Sparse.eval row313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck313, Integer.Sparse.eval_collectBalanced, rawRowCheck313]

theorem rawRowCheck314 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1 = rawRow314 := by decide +kernel

theorem rowCheck314 : row314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow314 := by decide +kernel

theorem rowEval314 (x : Key → ℝ) : Integer.Sparse.eval row314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck314, Integer.Sparse.eval_collectBalanced, rawRowCheck314]

theorem rawRowCheck315 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1 = rawRow315 := by decide +kernel

theorem rowCheck315 : row315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow315 := by decide +kernel

theorem rowEval315 (x : Key → ℝ) : Integer.Sparse.eval row315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck315, Integer.Sparse.eval_collectBalanced, rawRowCheck315]

theorem rawRowCheck316 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1 = rawRow316 := by decide +kernel

theorem rowCheck316 : row316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow316 := by decide +kernel

theorem rowEval316 (x : Key → ℝ) : Integer.Sparse.eval row316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck316, Integer.Sparse.eval_collectBalanced, rawRowCheck316]

theorem rawRowCheck317 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1 = rawRow317 := by decide +kernel

theorem rowCheck317 : row317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow317 := by decide +kernel

theorem rowEval317 (x : Key → ℝ) : Integer.Sparse.eval row317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck317, Integer.Sparse.eval_collectBalanced, rawRowCheck317]

theorem rawRowCheck318 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1 = rawRow318 := by decide +kernel

theorem rowCheck318 : row318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow318 := by decide +kernel

theorem rowEval318 (x : Key → ℝ) : Integer.Sparse.eval row318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck318, Integer.Sparse.eval_collectBalanced, rawRowCheck318]

theorem rawRowCheck319 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1 = rawRow319 := by decide +kernel

theorem rowCheck319 : row319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow319 := by decide +kernel

theorem rowEval319 (x : Key → ℝ) : Integer.Sparse.eval row319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck319, Integer.Sparse.eval_collectBalanced, rawRowCheck319]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck320 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1 = rawRow320 := by decide +kernel

theorem rowCheck320 : row320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow320 := by decide +kernel

theorem rowEval320 (x : Key → ℝ) : Integer.Sparse.eval row320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck320, Integer.Sparse.eval_collectBalanced, rawRowCheck320]

theorem rawRowCheck321 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1 = rawRow321 := by decide +kernel

theorem rowCheck321 : row321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow321 := by decide +kernel

theorem rowEval321 (x : Key → ℝ) : Integer.Sparse.eval row321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck321, Integer.Sparse.eval_collectBalanced, rawRowCheck321]

theorem rawRowCheck322 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1 = rawRow322 := by decide +kernel

theorem rowCheck322 : row322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow322 := by decide +kernel

theorem rowEval322 (x : Key → ℝ) : Integer.Sparse.eval row322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck322, Integer.Sparse.eval_collectBalanced, rawRowCheck322]

theorem rawRowCheck323 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1 = rawRow323 := by decide +kernel

theorem rowCheck323 : row323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow323 := by decide +kernel

theorem rowEval323 (x : Key → ℝ) : Integer.Sparse.eval row323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck323, Integer.Sparse.eval_collectBalanced, rawRowCheck323]

theorem rawRowCheck324 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow324 := by decide +kernel

theorem rowCheck324 : row324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow324 := by decide +kernel

theorem rowEval324 (x : Key → ℝ) : Integer.Sparse.eval row324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck324, Integer.Sparse.eval_collectBalanced, rawRowCheck324]

theorem rawRowCheck325 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow325 := by decide +kernel

theorem rowCheck325 : row325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow325 := by decide +kernel

theorem rowEval325 (x : Key → ℝ) : Integer.Sparse.eval row325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck325, Integer.Sparse.eval_collectBalanced, rawRowCheck325]

theorem rawRowCheck326 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1 = rawRow326 := by decide +kernel

theorem rowCheck326 : row326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow326 := by decide +kernel

theorem rowEval326 (x : Key → ℝ) : Integer.Sparse.eval row326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck326, Integer.Sparse.eval_collectBalanced, rawRowCheck326]

theorem rawRowCheck327 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1 = rawRow327 := by decide +kernel

theorem rowCheck327 : row327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow327 := by decide +kernel

theorem rowEval327 (x : Key → ℝ) : Integer.Sparse.eval row327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck327, Integer.Sparse.eval_collectBalanced, rawRowCheck327]

theorem rawRowCheck328 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow328 := by decide +kernel

theorem rowCheck328 : row328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow328 := by decide +kernel

theorem rowEval328 (x : Key → ℝ) : Integer.Sparse.eval row328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck328, Integer.Sparse.eval_collectBalanced, rawRowCheck328]

theorem rawRowCheck329 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow329 := by decide +kernel

theorem rowCheck329 : row329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow329 := by decide +kernel

theorem rowEval329 (x : Key → ℝ) : Integer.Sparse.eval row329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck329, Integer.Sparse.eval_collectBalanced, rawRowCheck329]

theorem rawRowCheck330 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow330 := by decide +kernel

theorem rowCheck330 : row330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow330 := by decide +kernel

theorem rowEval330 (x : Key → ℝ) : Integer.Sparse.eval row330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck330, Integer.Sparse.eval_collectBalanced, rawRowCheck330]

theorem rawRowCheck331 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow331 := by decide +kernel

theorem rowCheck331 : row331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow331 := by decide +kernel

theorem rowEval331 (x : Key → ℝ) : Integer.Sparse.eval row331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck331, Integer.Sparse.eval_collectBalanced, rawRowCheck331]

theorem rawRowCheck332 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1 = rawRow332 := by decide +kernel

theorem rowCheck332 : row332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow332 := by decide +kernel

theorem rowEval332 (x : Key → ℝ) : Integer.Sparse.eval row332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck332, Integer.Sparse.eval_collectBalanced, rawRowCheck332]

theorem rawRowCheck333 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1 = rawRow333 := by decide +kernel

theorem rowCheck333 : row333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow333 := by decide +kernel

theorem rowEval333 (x : Key → ℝ) : Integer.Sparse.eval row333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck333, Integer.Sparse.eval_collectBalanced, rawRowCheck333]

theorem rawRowCheck334 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1 = rawRow334 := by decide +kernel

theorem rowCheck334 : row334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow334 := by decide +kernel

theorem rowEval334 (x : Key → ℝ) : Integer.Sparse.eval row334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck334, Integer.Sparse.eval_collectBalanced, rawRowCheck334]

theorem rawRowCheck335 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1 = rawRow335 := by decide +kernel

theorem rowCheck335 : row335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow335 := by decide +kernel

theorem rowEval335 (x : Key → ℝ) : Integer.Sparse.eval row335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck335, Integer.Sparse.eval_collectBalanced, rawRowCheck335]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem rowsSound3_1_e_oai (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval294 x
  · exact rowEval295 x
  · exact rowEval296 x
  · exact rowEval297 x
  · exact rowEval298 x
  · exact rowEval299 x
  · exact rowEval300 x
  · exact rowEval301 x
  · exact rowEval302 x
  · exact rowEval303 x
  · exact rowEval304 x
  · exact rowEval305 x
  · exact rowEval306 x
  · exact rowEval307 x
  · exact rowEval308 x
  · exact rowEval309 x
  · exact rowEval310 x
  · exact rowEval311 x
  · exact rowEval312 x
  · exact rowEval313 x
  · exact rowEval314 x
  · exact rowEval315 x
  · exact rowEval316 x
  · exact rowEval317 x
  · exact rowEval318 x
  · exact rowEval319 x
  · exact rowEval320 x
  · exact rowEval321 x
  · exact rowEval322 x
  · exact rowEval323 x
  · exact rowEval324 x
  · exact rowEval325 x
  · exact rowEval326 x
  · exact rowEval327 x
  · exact rowEval328 x
  · exact rowEval329 x
  · exact rowEval330 x
  · exact rowEval331 x
  · exact rowEval332 x
  · exact rowEval333 x
  · exact rowEval334 x
  · exact rowEval335 x

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound3_1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.rowsSound3_1_e_oai
