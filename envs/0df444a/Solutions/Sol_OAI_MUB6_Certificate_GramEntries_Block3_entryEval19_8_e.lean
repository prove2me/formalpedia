-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEval19_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:58:50.997959+00:00
-- url     : https://prove2.me/submissions/f5ec2de3-7f35-455b-8ef8-bdc9711f09cd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E151
import Theorems.Thm_OAI_MUB6_GramNormalization_eval_normalize_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramPolynomial
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite auxiliary Gram products interpreted as sparse normalized keys. -/
namespace MUB6.Certificate.GramPolynomial

open GramFunctions GramNormalization
open scoped BigOperators

theorem normalizedRow_eval (s : Fin 2) (a : Charge) (Q : LinearForm)
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (normalizedRow s a Q) (GramNormalization.eval B) =
      ∑ j, ((Q.terms j).coefficient : ℝ) *
        auxiliaryMixedEntry B s (Q.terms j).tag a (Q.terms j).charge := by
  simp [normalizedRow, Integer.Sparse.eval, List.map_ofFn, List.sum_ofFn,
    GramNormalization.eval_normalize_e B hB]

theorem mixedGram_eq_rows (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    P.mixedGram Q B = ∑ i, ((P.terms i).coefficient : ℝ) *
      Integer.Sparse.eval (normalizedRow (P.terms i).tag (P.terms i).charge Q)
        (GramNormalization.eval B) := by
  simp_rw [normalizedRow_eval _ _ _ B hB, Finset.mul_sum]
  unfold LinearForm.mixedGram
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem collectWeightedRows_eval {n : ℕ} (rows : Fin n → Integer.Sparse Key)
    (weights : Fin n → ℤ) (x : Key → ℝ) :
    Integer.Sparse.eval
      (Integer.Sparse.collectLevels keyLess n
        (List.ofFn fun i => Integer.Sparse.scale (weights i) (rows i))) x =
      ∑ i, (weights i : ℝ) * Integer.Sparse.eval (rows i) x := by
  rw [Integer.Sparse.eval_collectLevels]
  simp [List.map_ofFn, List.sum_ofFn]

end MUB6.Certificate.GramPolynomial

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck10469 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8 = rawRow10469 := by decide +kernel

theorem rowCheck10469 : row10469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10469 := by decide +kernel

theorem rowEval10469 (x : Key → ℝ) : Integer.Sparse.eval row10469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10469, Integer.Sparse.eval_collectBalanced, rawRowCheck10469]

theorem rawRowCheck10470 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8 = rawRow10470 := by decide +kernel

theorem rowCheck10470 : row10470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10470 := by decide +kernel

theorem rowEval10470 (x : Key → ℝ) : Integer.Sparse.eval row10470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10470, Integer.Sparse.eval_collectBalanced, rawRowCheck10470]

theorem rawRowCheck10471 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8 = rawRow10471 := by decide +kernel

theorem rowCheck10471 : row10471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10471 := by decide +kernel

theorem rowEval10471 (x : Key → ℝ) : Integer.Sparse.eval row10471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10471, Integer.Sparse.eval_collectBalanced, rawRowCheck10471]

theorem rawRowCheck10472 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10472 := by decide +kernel

theorem rowCheck10472 : row10472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10472 := by decide +kernel

theorem rowEval10472 (x : Key → ℝ) : Integer.Sparse.eval row10472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10472, Integer.Sparse.eval_collectBalanced, rawRowCheck10472]

theorem rawRowCheck10473 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10473 := by decide +kernel

theorem rowCheck10473 : row10473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10473 := by decide +kernel

theorem rowEval10473 (x : Key → ℝ) : Integer.Sparse.eval row10473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10473, Integer.Sparse.eval_collectBalanced, rawRowCheck10473]

theorem rawRowCheck10474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10474 := by decide +kernel

theorem rowCheck10474 : row10474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10474 := by decide +kernel

theorem rowEval10474 (x : Key → ℝ) : Integer.Sparse.eval row10474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10474, Integer.Sparse.eval_collectBalanced, rawRowCheck10474]

theorem rawRowCheck10475 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10475 := by decide +kernel

theorem rowCheck10475 : row10475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10475 := by decide +kernel

theorem rowEval10475 (x : Key → ℝ) : Integer.Sparse.eval row10475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10475, Integer.Sparse.eval_collectBalanced, rawRowCheck10475]

theorem rawRowCheck10476 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10476 := by decide +kernel

theorem rowCheck10476 : row10476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10476 := by decide +kernel

theorem rowEval10476 (x : Key → ℝ) : Integer.Sparse.eval row10476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10476, Integer.Sparse.eval_collectBalanced, rawRowCheck10476]

theorem rawRowCheck10477 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10477 := by decide +kernel

theorem rowCheck10477 : row10477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10477 := by decide +kernel

theorem rowEval10477 (x : Key → ℝ) : Integer.Sparse.eval row10477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10477, Integer.Sparse.eval_collectBalanced, rawRowCheck10477]

theorem rawRowCheck10478 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8 = rawRow10478 := by decide +kernel

theorem rowCheck10478 : row10478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10478 := by decide +kernel

theorem rowEval10478 (x : Key → ℝ) : Integer.Sparse.eval row10478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10478, Integer.Sparse.eval_collectBalanced, rawRowCheck10478]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck19_8 : entry19_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_8 k)) := by decide +kernel

theorem rowsSound19_8 (k : Fin GramFunctions.Block3.form19.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows19_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form19.terms k).tag (GramFunctions.Block3.form19.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval10469 x
  · exact rowEval10470 x
  · exact rowEval10471 x
  · exact rowEval10472 x
  · exact rowEval10473 x
  · exact rowEval10474 x
  · exact rowEval10475 x
  · exact rowEval10476 x
  · exact rowEval10477 x
  · exact rowEval10478 x

theorem entryEval19_8_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry19_8 (GramNormalization.eval B) = GramFunctions.Block3.form19.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck19_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form19 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound19_8]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEval19_8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEval19_8_e_oai
