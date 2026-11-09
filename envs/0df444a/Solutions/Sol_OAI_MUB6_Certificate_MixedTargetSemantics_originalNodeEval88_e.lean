-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:09.501211+00:00
-- url     : https://prove2.me/submissions/f3931591-8138-4d99-acaf-137c686424b7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E134
import Definitions.Def_OAIQ106E135

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedTargetBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.Integer.Sparse

variable {ι κ : Type*}

theorem eval_substitute (v : Sparse κ) (rows : κ → Sparse ι) (x : ι → ℝ) :
    eval (substitute v rows) x = eval v (fun k => eval (rows k) x) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_scale, eval_cons] at *
    rw [ih]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck45 : originalBlock45 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock45 keyMomentRows) := by decide +kernel

theorem originalBlockEval45 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock45 x =
      Integer.Sparse.eval keyPolynomialBlock45 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck45, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck46 : originalBlock46 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock46 keyMomentRows) := by decide +kernel

theorem originalBlockEval46 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock46 x =
      Integer.Sparse.eval keyPolynomialBlock46 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck46, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck47 : originalBlock47 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock47 keyMomentRows) := by decide +kernel

theorem originalBlockEval47 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock47 x =
      Integer.Sparse.eval keyPolynomialBlock47 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck47, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck48 : originalBlock48 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock48 keyMomentRows) := by decide +kernel

theorem originalBlockEval48 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock48 x =
      Integer.Sparse.eval keyPolynomialBlock48 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck48, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck49 : originalBlock49 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock49 keyMomentRows) := by decide +kernel

theorem originalBlockEval49 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock49 x =
      Integer.Sparse.eval keyPolynomialBlock49 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck49, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck50 : originalBlock50 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock50 keyMomentRows) := by decide +kernel

theorem originalBlockEval50 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock50 x =
      Integer.Sparse.eval keyPolynomialBlock50 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck50, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck51 : originalBlock51 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock51 keyMomentRows) := by decide +kernel

theorem originalBlockEval51 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock51 x =
      Integer.Sparse.eval keyPolynomialBlock51 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck51, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck52 : originalBlock52 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock52 keyMomentRows) := by decide +kernel

theorem originalBlockEval52 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock52 x =
      Integer.Sparse.eval keyPolynomialBlock52 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck52, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck53 : originalBlock53 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock53 keyMomentRows) := by decide +kernel

theorem originalBlockEval53 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock53 x =
      Integer.Sparse.eval keyPolynomialBlock53 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck53, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck54 : originalBlock54 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock54 keyMomentRows) := by decide +kernel

theorem originalBlockEval54 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock54 x =
      Integer.Sparse.eval keyPolynomialBlock54 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck54, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck55 : originalBlock55 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock55 keyMomentRows) := by decide +kernel

theorem originalBlockEval55 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock55 x =
      Integer.Sparse.eval keyPolynomialBlock55 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck55, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck56 : originalBlock56 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock56 keyMomentRows) := by decide +kernel

theorem originalBlockEval56 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock56 x =
      Integer.Sparse.eval keyPolynomialBlock56 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck56, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck57 : originalBlock57 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock57 keyMomentRows) := by decide +kernel

theorem originalBlockEval57 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock57 x =
      Integer.Sparse.eval keyPolynomialBlock57 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck57, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck58 : originalBlock58 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock58 keyMomentRows) := by decide +kernel

theorem originalBlockEval58 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock58 x =
      Integer.Sparse.eval keyPolynomialBlock58 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck58, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck59 : originalBlock59 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock59 keyMomentRows) := by decide +kernel

theorem originalBlockEval59 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock59 x =
      Integer.Sparse.eval keyPolynomialBlock59 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck59, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck60 : originalBlock60 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock60 keyMomentRows) := by decide +kernel

theorem originalBlockEval60 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock60 x =
      Integer.Sparse.eval keyPolynomialBlock60 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck60, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck61 : originalBlock61 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock61 keyMomentRows) := by decide +kernel

theorem originalBlockEval61 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock61 x =
      Integer.Sparse.eval keyPolynomialBlock61 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck61, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck62 : originalBlock62 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock62 keyMomentRows) := by decide +kernel

theorem originalBlockEval62 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock62 x =
      Integer.Sparse.eval keyPolynomialBlock62 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck62, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck63 : originalBlock63 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock63 keyMomentRows) := by decide +kernel

theorem originalBlockEval63 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock63 x =
      Integer.Sparse.eval keyPolynomialBlock63 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck63, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck64 : originalBlock64 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock64 keyMomentRows) := by decide +kernel

theorem originalBlockEval64 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock64 x =
      Integer.Sparse.eval keyPolynomialBlock64 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck64, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck65 : originalBlock65 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock65 keyMomentRows) := by decide +kernel

theorem originalBlockEval65 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock65 x =
      Integer.Sparse.eval keyPolynomialBlock65 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck65, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck66 : originalBlock66 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock66 keyMomentRows) := by decide +kernel

theorem originalBlockEval66 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock66 x =
      Integer.Sparse.eval keyPolynomialBlock66 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck66, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck67 : originalBlock67 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock67 keyMomentRows) := by decide +kernel

theorem originalBlockEval67 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock67 x =
      Integer.Sparse.eval keyPolynomialBlock67 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck67, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck68 : originalBlock68 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock68 keyMomentRows) := by decide +kernel

theorem originalBlockEval68 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock68 x =
      Integer.Sparse.eval keyPolynomialBlock68 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck68, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck69 : originalBlock69 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock69 keyMomentRows) := by decide +kernel

theorem originalBlockEval69 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock69 x =
      Integer.Sparse.eval keyPolynomialBlock69 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck69, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck70 : originalBlock70 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock70 keyMomentRows) := by decide +kernel

theorem originalBlockEval70 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock70 x =
      Integer.Sparse.eval keyPolynomialBlock70 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck70, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck71 : originalBlock71 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock71 keyMomentRows) := by decide +kernel

theorem originalBlockEval71 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock71 x =
      Integer.Sparse.eval keyPolynomialBlock71 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck71, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck72 : originalBlock72 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock72 keyMomentRows) := by decide +kernel

theorem originalBlockEval72 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock72 x =
      Integer.Sparse.eval keyPolynomialBlock72 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck72, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck73 : originalBlock73 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock73 keyMomentRows) := by decide +kernel

theorem originalBlockEval73 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock73 x =
      Integer.Sparse.eval keyPolynomialBlock73 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck73, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck74 : originalBlock74 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock74 keyMomentRows) := by decide +kernel

theorem originalBlockEval74 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock74 x =
      Integer.Sparse.eval keyPolynomialBlock74 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck74, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck75 : originalBlock75 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock75 keyMomentRows) := by decide +kernel

theorem originalBlockEval75 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock75 x =
      Integer.Sparse.eval keyPolynomialBlock75 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck75, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck76 : originalBlock76 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock76 keyMomentRows) := by decide +kernel

theorem originalBlockEval76 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock76 x =
      Integer.Sparse.eval keyPolynomialBlock76 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck76, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck77 : originalBlock77 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock77 keyMomentRows) := by decide +kernel

theorem originalBlockEval77 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock77 x =
      Integer.Sparse.eval keyPolynomialBlock77 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck77, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck78 : originalBlock78 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock78 keyMomentRows) := by decide +kernel

theorem originalBlockEval78 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock78 x =
      Integer.Sparse.eval keyPolynomialBlock78 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck78, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck79 : originalBlock79 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock79 keyMomentRows) := by decide +kernel

theorem originalBlockEval79 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock79 x =
      Integer.Sparse.eval keyPolynomialBlock79 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck79, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck80 : originalBlock80 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock80 keyMomentRows) := by decide +kernel

theorem originalBlockEval80 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock80 x =
      Integer.Sparse.eval keyPolynomialBlock80 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck80, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck81 : originalBlock81 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock81 keyMomentRows) := by decide +kernel

theorem originalBlockEval81 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock81 x =
      Integer.Sparse.eval keyPolynomialBlock81 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck81, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck82 : originalBlock82 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock82 keyMomentRows) := by decide +kernel

theorem originalBlockEval82 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock82 x =
      Integer.Sparse.eval keyPolynomialBlock82 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck82, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck83 : originalBlock83 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock83 keyMomentRows) := by decide +kernel

theorem originalBlockEval83 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock83 x =
      Integer.Sparse.eval keyPolynomialBlock83 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck83, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck84 : originalBlock84 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock84 keyMomentRows) := by decide +kernel

theorem originalBlockEval84 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock84 x =
      Integer.Sparse.eval keyPolynomialBlock84 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck84, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck85 : originalBlock85 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock85 keyMomentRows) := by decide +kernel

theorem originalBlockEval85 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock85 x =
      Integer.Sparse.eval keyPolynomialBlock85 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck85, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck86 : originalBlock86 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock86 keyMomentRows) := by decide +kernel

theorem originalBlockEval86 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock86 x =
      Integer.Sparse.eval keyPolynomialBlock86 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck86, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck87 : originalBlock87 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock87 keyMomentRows) := by decide +kernel

theorem originalBlockEval87 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock87 x =
      Integer.Sparse.eval keyPolynomialBlock87 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck87, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck88 : originalBlock88 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock88 keyMomentRows) := by decide +kernel

theorem originalBlockEval88 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock88 x =
      Integer.Sparse.eval keyPolynomialBlock88 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck88, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck89 : originalBlock89 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock89 keyMomentRows) := by decide +kernel

theorem originalBlockEval89 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock89 x =
      Integer.Sparse.eval keyPolynomialBlock89 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck89, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockCheck90 : originalBlock90 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock90 keyMomentRows) := by decide +kernel

theorem originalBlockEval90 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock90 x =
      Integer.Sparse.eval keyPolynomialBlock90 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck90, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode44Check : originalNode44 = Integer.Sparse.mergeBy originalLess originalBlock45 originalBlock46 := by decide +kernel

theorem originalNodeEval44 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode44 x =
      Integer.Sparse.eval keyPolynomialNode44 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode44Check, Integer.Sparse.eval_mergeBy, originalBlockEval45, originalBlockEval46]
  rw [keyPolynomialNode44, Integer.Sparse.eval_append]

theorem originalNode45Check : originalNode45 = Integer.Sparse.mergeBy originalLess originalBlock48 originalBlock49 := by decide +kernel

theorem originalNodeEval45 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode45 x =
      Integer.Sparse.eval keyPolynomialNode45 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode45Check, Integer.Sparse.eval_mergeBy, originalBlockEval48, originalBlockEval49]
  rw [keyPolynomialNode45, Integer.Sparse.eval_append]

theorem originalNode46Check : originalNode46 = Integer.Sparse.mergeBy originalLess originalBlock47 originalNode45 := by decide +kernel

theorem originalNodeEval46 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode46 x =
      Integer.Sparse.eval keyPolynomialNode46 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode46Check, Integer.Sparse.eval_mergeBy, originalBlockEval47, originalNodeEval45]
  rw [keyPolynomialNode46, Integer.Sparse.eval_append]

theorem originalNode47Check : originalNode47 = Integer.Sparse.mergeBy originalLess originalNode44 originalNode46 := by decide +kernel

theorem originalNodeEval47 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode47 x =
      Integer.Sparse.eval keyPolynomialNode47 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode47Check, Integer.Sparse.eval_mergeBy, originalNodeEval44, originalNodeEval46]
  rw [keyPolynomialNode47, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode48Check : originalNode48 = Integer.Sparse.mergeBy originalLess originalBlock51 originalBlock52 := by decide +kernel

theorem originalNodeEval48 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode48 x =
      Integer.Sparse.eval keyPolynomialNode48 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode48Check, Integer.Sparse.eval_mergeBy, originalBlockEval51, originalBlockEval52]
  rw [keyPolynomialNode48, Integer.Sparse.eval_append]

theorem originalNode49Check : originalNode49 = Integer.Sparse.mergeBy originalLess originalBlock50 originalNode48 := by decide +kernel

theorem originalNodeEval49 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode49 x =
      Integer.Sparse.eval keyPolynomialNode49 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode49Check, Integer.Sparse.eval_mergeBy, originalBlockEval50, originalNodeEval48]
  rw [keyPolynomialNode49, Integer.Sparse.eval_append]

theorem originalNode50Check : originalNode50 = Integer.Sparse.mergeBy originalLess originalBlock54 originalBlock55 := by decide +kernel

theorem originalNodeEval50 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode50 x =
      Integer.Sparse.eval keyPolynomialNode50 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode50Check, Integer.Sparse.eval_mergeBy, originalBlockEval54, originalBlockEval55]
  rw [keyPolynomialNode50, Integer.Sparse.eval_append]

theorem originalNode51Check : originalNode51 = Integer.Sparse.mergeBy originalLess originalBlock53 originalNode50 := by decide +kernel

theorem originalNodeEval51 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode51 x =
      Integer.Sparse.eval keyPolynomialNode51 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode51Check, Integer.Sparse.eval_mergeBy, originalBlockEval53, originalNodeEval50]
  rw [keyPolynomialNode51, Integer.Sparse.eval_append]

theorem originalNode52Check : originalNode52 = Integer.Sparse.mergeBy originalLess originalNode49 originalNode51 := by decide +kernel

theorem originalNodeEval52 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode52 x =
      Integer.Sparse.eval keyPolynomialNode52 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode52Check, Integer.Sparse.eval_mergeBy, originalNodeEval49, originalNodeEval51]
  rw [keyPolynomialNode52, Integer.Sparse.eval_append]

theorem originalNode53Check : originalNode53 = Integer.Sparse.mergeBy originalLess originalNode47 originalNode52 := by decide +kernel

theorem originalNodeEval53 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode53 x =
      Integer.Sparse.eval keyPolynomialNode53 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode53Check, Integer.Sparse.eval_mergeBy, originalNodeEval47, originalNodeEval52]
  rw [keyPolynomialNode53, Integer.Sparse.eval_append]

theorem originalNode54Check : originalNode54 = Integer.Sparse.mergeBy originalLess originalBlock57 originalBlock58 := by decide +kernel

theorem originalNodeEval54 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode54 x =
      Integer.Sparse.eval keyPolynomialNode54 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode54Check, Integer.Sparse.eval_mergeBy, originalBlockEval57, originalBlockEval58]
  rw [keyPolynomialNode54, Integer.Sparse.eval_append]

theorem originalNode55Check : originalNode55 = Integer.Sparse.mergeBy originalLess originalBlock56 originalNode54 := by decide +kernel

theorem originalNodeEval55 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode55 x =
      Integer.Sparse.eval keyPolynomialNode55 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode55Check, Integer.Sparse.eval_mergeBy, originalBlockEval56, originalNodeEval54]
  rw [keyPolynomialNode55, Integer.Sparse.eval_append]

theorem originalNode56Check : originalNode56 = Integer.Sparse.mergeBy originalLess originalBlock60 originalBlock61 := by decide +kernel

theorem originalNodeEval56 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode56 x =
      Integer.Sparse.eval keyPolynomialNode56 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode56Check, Integer.Sparse.eval_mergeBy, originalBlockEval60, originalBlockEval61]
  rw [keyPolynomialNode56, Integer.Sparse.eval_append]

theorem originalNode57Check : originalNode57 = Integer.Sparse.mergeBy originalLess originalBlock59 originalNode56 := by decide +kernel

theorem originalNodeEval57 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode57 x =
      Integer.Sparse.eval keyPolynomialNode57 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode57Check, Integer.Sparse.eval_mergeBy, originalBlockEval59, originalNodeEval56]
  rw [keyPolynomialNode57, Integer.Sparse.eval_append]

theorem originalNode58Check : originalNode58 = Integer.Sparse.mergeBy originalLess originalNode55 originalNode57 := by decide +kernel

theorem originalNodeEval58 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode58 x =
      Integer.Sparse.eval keyPolynomialNode58 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode58Check, Integer.Sparse.eval_mergeBy, originalNodeEval55, originalNodeEval57]
  rw [keyPolynomialNode58, Integer.Sparse.eval_append]

theorem originalNode59Check : originalNode59 = Integer.Sparse.mergeBy originalLess originalBlock63 originalBlock64 := by decide +kernel

theorem originalNodeEval59 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode59 x =
      Integer.Sparse.eval keyPolynomialNode59 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode59Check, Integer.Sparse.eval_mergeBy, originalBlockEval63, originalBlockEval64]
  rw [keyPolynomialNode59, Integer.Sparse.eval_append]

theorem originalNode60Check : originalNode60 = Integer.Sparse.mergeBy originalLess originalBlock62 originalNode59 := by decide +kernel

theorem originalNodeEval60 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode60 x =
      Integer.Sparse.eval keyPolynomialNode60 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode60Check, Integer.Sparse.eval_mergeBy, originalBlockEval62, originalNodeEval59]
  rw [keyPolynomialNode60, Integer.Sparse.eval_append]

theorem originalNode61Check : originalNode61 = Integer.Sparse.mergeBy originalLess originalBlock66 originalBlock67 := by decide +kernel

theorem originalNodeEval61 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode61 x =
      Integer.Sparse.eval keyPolynomialNode61 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode61Check, Integer.Sparse.eval_mergeBy, originalBlockEval66, originalBlockEval67]
  rw [keyPolynomialNode61, Integer.Sparse.eval_append]

theorem originalNode62Check : originalNode62 = Integer.Sparse.mergeBy originalLess originalBlock65 originalNode61 := by decide +kernel

theorem originalNodeEval62 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode62 x =
      Integer.Sparse.eval keyPolynomialNode62 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode62Check, Integer.Sparse.eval_mergeBy, originalBlockEval65, originalNodeEval61]
  rw [keyPolynomialNode62, Integer.Sparse.eval_append]

theorem originalNode63Check : originalNode63 = Integer.Sparse.mergeBy originalLess originalNode60 originalNode62 := by decide +kernel

theorem originalNodeEval63 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode63 x =
      Integer.Sparse.eval keyPolynomialNode63 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode63Check, Integer.Sparse.eval_mergeBy, originalNodeEval60, originalNodeEval62]
  rw [keyPolynomialNode63, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode64Check : originalNode64 = Integer.Sparse.mergeBy originalLess originalNode58 originalNode63 := by decide +kernel

theorem originalNodeEval64 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode64 x =
      Integer.Sparse.eval keyPolynomialNode64 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode64Check, Integer.Sparse.eval_mergeBy, originalNodeEval58, originalNodeEval63]
  rw [keyPolynomialNode64, Integer.Sparse.eval_append]

theorem originalNode65Check : originalNode65 = Integer.Sparse.mergeBy originalLess originalNode53 originalNode64 := by decide +kernel

theorem originalNodeEval65 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode65 x =
      Integer.Sparse.eval keyPolynomialNode65 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode65Check, Integer.Sparse.eval_mergeBy, originalNodeEval53, originalNodeEval64]
  rw [keyPolynomialNode65, Integer.Sparse.eval_append]

theorem originalNode66Check : originalNode66 = Integer.Sparse.mergeBy originalLess originalBlock68 originalBlock69 := by decide +kernel

theorem originalNodeEval66 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode66 x =
      Integer.Sparse.eval keyPolynomialNode66 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode66Check, Integer.Sparse.eval_mergeBy, originalBlockEval68, originalBlockEval69]
  rw [keyPolynomialNode66, Integer.Sparse.eval_append]

theorem originalNode67Check : originalNode67 = Integer.Sparse.mergeBy originalLess originalBlock71 originalBlock72 := by decide +kernel

theorem originalNodeEval67 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode67 x =
      Integer.Sparse.eval keyPolynomialNode67 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode67Check, Integer.Sparse.eval_mergeBy, originalBlockEval71, originalBlockEval72]
  rw [keyPolynomialNode67, Integer.Sparse.eval_append]

theorem originalNode68Check : originalNode68 = Integer.Sparse.mergeBy originalLess originalBlock70 originalNode67 := by decide +kernel

theorem originalNodeEval68 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode68 x =
      Integer.Sparse.eval keyPolynomialNode68 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode68Check, Integer.Sparse.eval_mergeBy, originalBlockEval70, originalNodeEval67]
  rw [keyPolynomialNode68, Integer.Sparse.eval_append]

theorem originalNode69Check : originalNode69 = Integer.Sparse.mergeBy originalLess originalNode66 originalNode68 := by decide +kernel

theorem originalNodeEval69 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode69 x =
      Integer.Sparse.eval keyPolynomialNode69 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode69Check, Integer.Sparse.eval_mergeBy, originalNodeEval66, originalNodeEval68]
  rw [keyPolynomialNode69, Integer.Sparse.eval_append]

theorem originalNode70Check : originalNode70 = Integer.Sparse.mergeBy originalLess originalBlock74 originalBlock75 := by decide +kernel

theorem originalNodeEval70 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode70 x =
      Integer.Sparse.eval keyPolynomialNode70 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode70Check, Integer.Sparse.eval_mergeBy, originalBlockEval74, originalBlockEval75]
  rw [keyPolynomialNode70, Integer.Sparse.eval_append]

theorem originalNode71Check : originalNode71 = Integer.Sparse.mergeBy originalLess originalBlock73 originalNode70 := by decide +kernel

theorem originalNodeEval71 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode71 x =
      Integer.Sparse.eval keyPolynomialNode71 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode71Check, Integer.Sparse.eval_mergeBy, originalBlockEval73, originalNodeEval70]
  rw [keyPolynomialNode71, Integer.Sparse.eval_append]

theorem originalNode72Check : originalNode72 = Integer.Sparse.mergeBy originalLess originalBlock77 originalBlock78 := by decide +kernel

theorem originalNodeEval72 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode72 x =
      Integer.Sparse.eval keyPolynomialNode72 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode72Check, Integer.Sparse.eval_mergeBy, originalBlockEval77, originalBlockEval78]
  rw [keyPolynomialNode72, Integer.Sparse.eval_append]

theorem originalNode73Check : originalNode73 = Integer.Sparse.mergeBy originalLess originalBlock76 originalNode72 := by decide +kernel

theorem originalNodeEval73 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode73 x =
      Integer.Sparse.eval keyPolynomialNode73 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode73Check, Integer.Sparse.eval_mergeBy, originalBlockEval76, originalNodeEval72]
  rw [keyPolynomialNode73, Integer.Sparse.eval_append]

theorem originalNode74Check : originalNode74 = Integer.Sparse.mergeBy originalLess originalNode71 originalNode73 := by decide +kernel

theorem originalNodeEval74 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode74 x =
      Integer.Sparse.eval keyPolynomialNode74 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode74Check, Integer.Sparse.eval_mergeBy, originalNodeEval71, originalNodeEval73]
  rw [keyPolynomialNode74, Integer.Sparse.eval_append]

theorem originalNode75Check : originalNode75 = Integer.Sparse.mergeBy originalLess originalNode69 originalNode74 := by decide +kernel

theorem originalNodeEval75 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode75 x =
      Integer.Sparse.eval keyPolynomialNode75 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode75Check, Integer.Sparse.eval_mergeBy, originalNodeEval69, originalNodeEval74]
  rw [keyPolynomialNode75, Integer.Sparse.eval_append]

theorem originalNode76Check : originalNode76 = Integer.Sparse.mergeBy originalLess originalBlock80 originalBlock81 := by decide +kernel

theorem originalNodeEval76 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode76 x =
      Integer.Sparse.eval keyPolynomialNode76 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode76Check, Integer.Sparse.eval_mergeBy, originalBlockEval80, originalBlockEval81]
  rw [keyPolynomialNode76, Integer.Sparse.eval_append]

theorem originalNode77Check : originalNode77 = Integer.Sparse.mergeBy originalLess originalBlock79 originalNode76 := by decide +kernel

theorem originalNodeEval77 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode77 x =
      Integer.Sparse.eval keyPolynomialNode77 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode77Check, Integer.Sparse.eval_mergeBy, originalBlockEval79, originalNodeEval76]
  rw [keyPolynomialNode77, Integer.Sparse.eval_append]

theorem originalNode78Check : originalNode78 = Integer.Sparse.mergeBy originalLess originalBlock83 originalBlock84 := by decide +kernel

theorem originalNodeEval78 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode78 x =
      Integer.Sparse.eval keyPolynomialNode78 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode78Check, Integer.Sparse.eval_mergeBy, originalBlockEval83, originalBlockEval84]
  rw [keyPolynomialNode78, Integer.Sparse.eval_append]

theorem originalNode79Check : originalNode79 = Integer.Sparse.mergeBy originalLess originalBlock82 originalNode78 := by decide +kernel

theorem originalNodeEval79 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode79 x =
      Integer.Sparse.eval keyPolynomialNode79 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode79Check, Integer.Sparse.eval_mergeBy, originalBlockEval82, originalNodeEval78]
  rw [keyPolynomialNode79, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalMerge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNode80Check : originalNode80 = Integer.Sparse.mergeBy originalLess originalNode77 originalNode79 := by decide +kernel

theorem originalNodeEval80 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode80 x =
      Integer.Sparse.eval keyPolynomialNode80 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode80Check, Integer.Sparse.eval_mergeBy, originalNodeEval77, originalNodeEval79]
  rw [keyPolynomialNode80, Integer.Sparse.eval_append]

theorem originalNode81Check : originalNode81 = Integer.Sparse.mergeBy originalLess originalBlock86 originalBlock87 := by decide +kernel

theorem originalNodeEval81 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode81 x =
      Integer.Sparse.eval keyPolynomialNode81 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode81Check, Integer.Sparse.eval_mergeBy, originalBlockEval86, originalBlockEval87]
  rw [keyPolynomialNode81, Integer.Sparse.eval_append]

theorem originalNode82Check : originalNode82 = Integer.Sparse.mergeBy originalLess originalBlock85 originalNode81 := by decide +kernel

theorem originalNodeEval82 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode82 x =
      Integer.Sparse.eval keyPolynomialNode82 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode82Check, Integer.Sparse.eval_mergeBy, originalBlockEval85, originalNodeEval81]
  rw [keyPolynomialNode82, Integer.Sparse.eval_append]

theorem originalNode83Check : originalNode83 = Integer.Sparse.mergeBy originalLess originalBlock89 originalBlock90 := by decide +kernel

theorem originalNodeEval83 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode83 x =
      Integer.Sparse.eval keyPolynomialNode83 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode83Check, Integer.Sparse.eval_mergeBy, originalBlockEval89, originalBlockEval90]
  rw [keyPolynomialNode83, Integer.Sparse.eval_append]

theorem originalNode84Check : originalNode84 = Integer.Sparse.mergeBy originalLess originalBlock88 originalNode83 := by decide +kernel

theorem originalNodeEval84 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode84 x =
      Integer.Sparse.eval keyPolynomialNode84 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode84Check, Integer.Sparse.eval_mergeBy, originalBlockEval88, originalNodeEval83]
  rw [keyPolynomialNode84, Integer.Sparse.eval_append]

theorem originalNode85Check : originalNode85 = Integer.Sparse.mergeBy originalLess originalNode82 originalNode84 := by decide +kernel

theorem originalNodeEval85 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode85 x =
      Integer.Sparse.eval keyPolynomialNode85 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode85Check, Integer.Sparse.eval_mergeBy, originalNodeEval82, originalNodeEval84]
  rw [keyPolynomialNode85, Integer.Sparse.eval_append]

theorem originalNode86Check : originalNode86 = Integer.Sparse.mergeBy originalLess originalNode80 originalNode85 := by decide +kernel

theorem originalNodeEval86 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode86 x =
      Integer.Sparse.eval keyPolynomialNode86 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode86Check, Integer.Sparse.eval_mergeBy, originalNodeEval80, originalNodeEval85]
  rw [keyPolynomialNode86, Integer.Sparse.eval_append]

theorem originalNode87Check : originalNode87 = Integer.Sparse.mergeBy originalLess originalNode75 originalNode86 := by decide +kernel

theorem originalNodeEval87 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode87 x =
      Integer.Sparse.eval keyPolynomialNode87 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode87Check, Integer.Sparse.eval_mergeBy, originalNodeEval75, originalNodeEval86]
  rw [keyPolynomialNode87, Integer.Sparse.eval_append]

theorem originalNode88Check : originalNode88 = Integer.Sparse.mergeBy originalLess originalNode65 originalNode87 := by decide +kernel

theorem originalNodeEval88_e_oai (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode88 x =
      Integer.Sparse.eval keyPolynomialNode88 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNode88Check, Integer.Sparse.eval_mergeBy, originalNodeEval65, originalNodeEval87]
  rw [keyPolynomialNode88, Integer.Sparse.eval_append]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e_oai
