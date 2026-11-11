-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:09:07.859688+00:00
-- url     : https://prove2.me/submissions/0b1fb8fb-be55-42a5-85f5-754a06ef8ff0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E034
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E056
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8245_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8246_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8247_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8248_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8249_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8250_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8251_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8252_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8263_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8264_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8265_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8266_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8267_e
import Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval8268_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck8233 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8233 := by decide +kernel

theorem rowCheck8233 : row8233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8233 := by decide +kernel

theorem rowEval8233 (x : Key → ℝ) : Integer.Sparse.eval row8233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8233, Integer.Sparse.eval_collectBalanced, rawRowCheck8233]

theorem rawRowCheck8234 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8234 := by decide +kernel

theorem rowCheck8234 : row8234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8234 := by decide +kernel

theorem rowEval8234 (x : Key → ℝ) : Integer.Sparse.eval row8234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8234, Integer.Sparse.eval_collectBalanced, rawRowCheck8234]

theorem rawRowCheck8235 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8235 := by decide +kernel

theorem rowCheck8235 : row8235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8235 := by decide +kernel

theorem rowEval8235 (x : Key → ℝ) : Integer.Sparse.eval row8235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8235, Integer.Sparse.eval_collectBalanced, rawRowCheck8235]

theorem rawRowCheck8236 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form8 = rawRow8236 := by decide +kernel

theorem rowCheck8236 : row8236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8236 := by decide +kernel

theorem rowEval8236 (x : Key → ℝ) : Integer.Sparse.eval row8236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8236, Integer.Sparse.eval_collectBalanced, rawRowCheck8236]

theorem rawRowCheck8237 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form8 = rawRow8237 := by decide +kernel

theorem rowCheck8237 : row8237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8237 := by decide +kernel

theorem rowEval8237 (x : Key → ℝ) : Integer.Sparse.eval row8237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8237, Integer.Sparse.eval_collectBalanced, rawRowCheck8237]

theorem rawRowCheck8238 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form8 = rawRow8238 := by decide +kernel

theorem rowCheck8238 : row8238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8238 := by decide +kernel

theorem rowEval8238 (x : Key → ℝ) : Integer.Sparse.eval row8238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8238, Integer.Sparse.eval_collectBalanced, rawRowCheck8238]

theorem rawRowCheck8239 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form8 = rawRow8239 := by decide +kernel

theorem rowCheck8239 : row8239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8239 := by decide +kernel

theorem rowEval8239 (x : Key → ℝ) : Integer.Sparse.eval row8239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8239, Integer.Sparse.eval_collectBalanced, rawRowCheck8239]

theorem rawRowCheck8240 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form8 = rawRow8240 := by decide +kernel

theorem rowCheck8240 : row8240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8240 := by decide +kernel

theorem rowEval8240 (x : Key → ℝ) : Integer.Sparse.eval row8240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8240, Integer.Sparse.eval_collectBalanced, rawRowCheck8240]

theorem rawRowCheck8241 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form8 = rawRow8241 := by decide +kernel

theorem rowCheck8241 : row8241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8241 := by decide +kernel

theorem rowEval8241 (x : Key → ℝ) : Integer.Sparse.eval row8241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8241, Integer.Sparse.eval_collectBalanced, rawRowCheck8241]

theorem rawRowCheck8242 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8242 := by decide +kernel

theorem rowCheck8242 : row8242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8242 := by decide +kernel

theorem rowEval8242 (x : Key → ℝ) : Integer.Sparse.eval row8242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8242, Integer.Sparse.eval_collectBalanced, rawRowCheck8242]

theorem rawRowCheck8243 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8243 := by decide +kernel

theorem rowCheck8243 : row8243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8243 := by decide +kernel

theorem rowEval8243 (x : Key → ℝ) : Integer.Sparse.eval row8243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8243, Integer.Sparse.eval_collectBalanced, rawRowCheck8243]

theorem rawRowCheck8244 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8244 := by decide +kernel

theorem rowCheck8244 : row8244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8244 := by decide +kernel

theorem rowEval8244 (x : Key → ℝ) : Integer.Sparse.eval row8244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8244, Integer.Sparse.eval_collectBalanced, rawRowCheck8244]

theorem rawRowCheck8253 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8 = rawRow8253 := by decide +kernel

theorem rowCheck8253 : row8253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8253 := by decide +kernel

theorem rowEval8253 (x : Key → ℝ) : Integer.Sparse.eval row8253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8253, Integer.Sparse.eval_collectBalanced, rawRowCheck8253]

theorem rawRowCheck8254 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8 = rawRow8254 := by decide +kernel

theorem rowCheck8254 : row8254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8254 := by decide +kernel

theorem rowEval8254 (x : Key → ℝ) : Integer.Sparse.eval row8254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8254, Integer.Sparse.eval_collectBalanced, rawRowCheck8254]

theorem rawRowCheck8255 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8 = rawRow8255 := by decide +kernel

theorem rowCheck8255 : row8255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8255 := by decide +kernel

theorem rowEval8255 (x : Key → ℝ) : Integer.Sparse.eval row8255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8255, Integer.Sparse.eval_collectBalanced, rawRowCheck8255]

theorem rawRowCheck8256 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8 = rawRow8256 := by decide +kernel

theorem rowCheck8256 : row8256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8256 := by decide +kernel

theorem rowEval8256 (x : Key → ℝ) : Integer.Sparse.eval row8256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8256, Integer.Sparse.eval_collectBalanced, rawRowCheck8256]

theorem rawRowCheck8257 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8 = rawRow8257 := by decide +kernel

theorem rowCheck8257 : row8257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8257 := by decide +kernel

theorem rowEval8257 (x : Key → ℝ) : Integer.Sparse.eval row8257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8257, Integer.Sparse.eval_collectBalanced, rawRowCheck8257]

theorem rawRowCheck8258 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8 = rawRow8258 := by decide +kernel

theorem rowCheck8258 : row8258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8258 := by decide +kernel

theorem rowEval8258 (x : Key → ℝ) : Integer.Sparse.eval row8258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8258, Integer.Sparse.eval_collectBalanced, rawRowCheck8258]

theorem rawRowCheck8259 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8 = rawRow8259 := by decide +kernel

theorem rowCheck8259 : row8259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8259 := by decide +kernel

theorem rowEval8259 (x : Key → ℝ) : Integer.Sparse.eval row8259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8259, Integer.Sparse.eval_collectBalanced, rawRowCheck8259]

theorem rawRowCheck8260 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8 = rawRow8260 := by decide +kernel

theorem rowCheck8260 : row8260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8260 := by decide +kernel

theorem rowEval8260 (x : Key → ℝ) : Integer.Sparse.eval row8260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8260, Integer.Sparse.eval_collectBalanced, rawRowCheck8260]

theorem rawRowCheck8261 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8 = rawRow8261 := by decide +kernel

theorem rowCheck8261 : row8261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8261 := by decide +kernel

theorem rowEval8261 (x : Key → ℝ) : Integer.Sparse.eval row8261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8261, Integer.Sparse.eval_collectBalanced, rawRowCheck8261]

theorem rawRowCheck8262 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8 = rawRow8262 := by decide +kernel

theorem rowCheck8262 : row8262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8262 := by decide +kernel

theorem rowEval8262 (x : Key → ℝ) : Integer.Sparse.eval row8262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8262, Integer.Sparse.eval_collectBalanced, rawRowCheck8262]

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

theorem rowsSound8_8_e_oai (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8233 x
  · exact rowEval8234 x
  · exact rowEval8235 x
  · exact rowEval8236 x
  · exact rowEval8237 x
  · exact rowEval8238 x
  · exact rowEval8239 x
  · exact rowEval8240 x
  · exact rowEval8241 x
  · exact rowEval8242 x
  · exact rowEval8243 x
  · exact rowEval8244 x
  · exact rowEval8245_e x
  · exact rowEval8246_e x
  · exact rowEval8247_e x
  · exact rowEval8248_e x
  · exact rowEval8249_e x
  · exact rowEval8250_e x
  · exact rowEval8251_e x
  · exact rowEval8252_e x
  · exact rowEval8253 x
  · exact rowEval8254 x
  · exact rowEval8255 x
  · exact rowEval8256 x
  · exact rowEval8257 x
  · exact rowEval8258 x
  · exact rowEval8259 x
  · exact rowEval8260 x
  · exact rowEval8261 x
  · exact rowEval8262 x
  · exact rowEval8263_e x
  · exact rowEval8264_e x
  · exact rowEval8265_e x
  · exact rowEval8266_e x
  · exact rowEval8267_e x
  · exact rowEval8268_e x

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.rowsSound8_8_e_oai
