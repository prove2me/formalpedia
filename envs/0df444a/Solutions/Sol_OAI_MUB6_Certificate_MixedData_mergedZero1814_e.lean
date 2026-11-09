-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1814_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:22:51.965067+00:00
-- url     : https://prove2.me/submissions/ffb7b9f7-43c8-49b3-810d-fb2e9ae9c2ac

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E059
import Definitions.Def_OAIQ106E061
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1813_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
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

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1513 : merged1513 = Integer.Sparse.merge (Integer.Sparse.scale (80363240853613804800) (sourceRows 1515)) (Integer.Sparse.scale (-2603790458716962816000) (sourceRows 1516)) := by decide +kernel

theorem mergedZero1513 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1513 x = 0 := by
  rw [mergeCheck1513, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1514 : merged1514 = Integer.Sparse.merge (Integer.Sparse.scale (-18961544043302313600) (sourceRows 1517)) (Integer.Sparse.scale (-2604000023533375488000) (sourceRows 1518)) := by decide +kernel

theorem mergedZero1514 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1514 x = 0 := by
  rw [mergeCheck1514, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1515 : merged1515 = Integer.Sparse.merge merged1513 merged1514 := by decide +kernel

theorem mergedZero1515 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1515 x = 0 := by
  rw [mergeCheck1515, Integer.Sparse.eval_merge]
  rw [mergedZero1513 x h, mergedZero1514 x h]
  simp only [add_zero]

theorem mergeCheck1516 : merged1516 = Integer.Sparse.merge (Integer.Sparse.scale (4917134486854430668800) (sourceRows 1519)) (Integer.Sparse.scale (54427654494778702233600) (sourceRows 1520)) := by decide +kernel

theorem mergedZero1516 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1516 x = 0 := by
  rw [mergeCheck1516, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1517 : merged1517 = Integer.Sparse.merge (Integer.Sparse.scale (-8928265284108172800) (sourceRows 1522)) (Integer.Sparse.scale (-38961695158831893571200) (sourceRows 1523)) := by decide +kernel

theorem mergedZero1517 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1517 x = 0 := by
  rw [mergeCheck1517, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1518 : merged1518 = Integer.Sparse.merge (Integer.Sparse.scale (-16407406491924188160) (sourceRows 1521)) merged1517 := by decide +kernel

theorem mergedZero1518 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1518 x = 0 := by
  rw [mergeCheck1518, Integer.Sparse.eval_merge]
  rw [mergedZero1517 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1519 : merged1519 = Integer.Sparse.merge merged1516 merged1518 := by decide +kernel

theorem mergedZero1519 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1519 x = 0 := by
  rw [mergeCheck1519, Integer.Sparse.eval_merge]
  rw [mergedZero1516 x h, mergedZero1518 x h]
  simp only [add_zero]

theorem mergeCheck1520 : merged1520 = Integer.Sparse.merge merged1515 merged1519 := by decide +kernel

theorem mergedZero1520 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1520 x = 0 := by
  rw [mergeCheck1520, Integer.Sparse.eval_merge]
  rw [mergedZero1515 x h, mergedZero1519 x h]
  simp only [add_zero]

theorem mergeCheck1521 : merged1521 = Integer.Sparse.merge (Integer.Sparse.scale (-4331062165789900800) (sourceRows 1524)) (Integer.Sparse.scale (4331062165789900800) (sourceRows 1525)) := by decide +kernel

theorem mergedZero1521 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1521 x = 0 := by
  rw [mergeCheck1521, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1522 : merged1522 = Integer.Sparse.merge (Integer.Sparse.scale (92484420800200712035200) (sourceRows 1526)) (Integer.Sparse.scale (430806396733900185600) (sourceRows 1527)) := by decide +kernel

theorem mergedZero1522 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1522 x = 0 := by
  rw [mergeCheck1522, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1523 : merged1523 = Integer.Sparse.merge merged1521 merged1522 := by decide +kernel

theorem mergedZero1523 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1523 x = 0 := by
  rw [mergeCheck1523, Integer.Sparse.eval_merge]
  rw [mergedZero1521 x h, mergedZero1522 x h]
  simp only [add_zero]

theorem mergeCheck1524 : merged1524 = Integer.Sparse.merge (Integer.Sparse.scale (2362326196295520000) (sourceRows 1528)) (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1529)) := by decide +kernel

theorem mergedZero1524 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1524 x = 0 := by
  rw [mergeCheck1524, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1525 : merged1525 = Integer.Sparse.merge (Integer.Sparse.scale (-104826661514432529033600) (sourceRows 1531)) (Integer.Sparse.scale (-34023519891808531660800) (sourceRows 1532)) := by decide +kernel

theorem mergedZero1525 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1525 x = 0 := by
  rw [mergeCheck1525, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1526 : merged1526 = Integer.Sparse.merge (Integer.Sparse.scale (-11199360213194227200) (sourceRows 1530)) merged1525 := by decide +kernel

theorem mergedZero1526 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1526 x = 0 := by
  rw [mergeCheck1526, Integer.Sparse.eval_merge]
  rw [mergedZero1525 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1527 : merged1527 = Integer.Sparse.merge merged1524 merged1526 := by decide +kernel

theorem mergedZero1527 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1527 x = 0 := by
  rw [mergeCheck1527, Integer.Sparse.eval_merge]
  rw [mergedZero1524 x h, mergedZero1526 x h]
  simp only [add_zero]

theorem mergeCheck1528 : merged1528 = Integer.Sparse.merge merged1523 merged1527 := by decide +kernel

theorem mergedZero1528 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1528 x = 0 := by
  rw [mergeCheck1528, Integer.Sparse.eval_merge]
  rw [mergedZero1523 x h, mergedZero1527 x h]
  simp only [add_zero]

theorem mergeCheck1529 : merged1529 = Integer.Sparse.merge merged1520 merged1528 := by decide +kernel

theorem mergedZero1529 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1529 x = 0 := by
  rw [mergeCheck1529, Integer.Sparse.eval_merge]
  rw [mergedZero1520 x h, mergedZero1528 x h]
  simp only [add_zero]

theorem mergeCheck1530 : merged1530 = Integer.Sparse.merge (Integer.Sparse.scale (34026631875017949081600) (sourceRows 1533)) (Integer.Sparse.scale (-18718760543941132214400) (sourceRows 1534)) := by decide +kernel

theorem mergedZero1530 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1530 x = 0 := by
  rw [mergeCheck1530, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1531 : merged1531 = Integer.Sparse.merge (Integer.Sparse.scale (388765687467543556665600) (sourceRows 1535)) (Integer.Sparse.scale (320712423717507658502400) (sourceRows 1536)) := by decide +kernel

theorem mergedZero1531 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1531 x = 0 := by
  rw [mergeCheck1531, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1532 : merged1532 = Integer.Sparse.merge merged1530 merged1531 := by decide +kernel

theorem mergedZero1532 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1532 x = 0 := by
  rw [mergeCheck1532, Integer.Sparse.eval_merge]
  rw [mergedZero1530 x h, mergedZero1531 x h]
  simp only [add_zero]

theorem mergeCheck1533 : merged1533 = Integer.Sparse.merge (Integer.Sparse.scale (320712423717507658502400) (sourceRows 1537)) (Integer.Sparse.scale (29344377410039804313600) (sourceRows 1538)) := by decide +kernel

theorem mergedZero1533 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1533 x = 0 := by
  rw [mergeCheck1533, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1534 : merged1534 = Integer.Sparse.merge (Integer.Sparse.scale (296323474341888000) (sourceRows 1540)) (Integer.Sparse.scale (-21449490579864345600) (sourceRows 1541)) := by decide +kernel

theorem mergedZero1534 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1534 x = 0 := by
  rw [mergeCheck1534, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1535 : merged1535 = Integer.Sparse.merge (Integer.Sparse.scale (350565446568960000) (sourceRows 1539)) merged1534 := by decide +kernel

theorem mergedZero1535 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1535 x = 0 := by
  rw [mergeCheck1535, Integer.Sparse.eval_merge]
  rw [mergedZero1534 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1536 : merged1536 = Integer.Sparse.merge merged1533 merged1535 := by decide +kernel

theorem mergedZero1536 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1536 x = 0 := by
  rw [mergeCheck1536, Integer.Sparse.eval_merge]
  rw [mergedZero1533 x h, mergedZero1535 x h]
  simp only [add_zero]

theorem mergeCheck1537 : merged1537 = Integer.Sparse.merge merged1532 merged1536 := by decide +kernel

theorem mergedZero1537 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1537 x = 0 := by
  rw [mergeCheck1537, Integer.Sparse.eval_merge]
  rw [mergedZero1532 x h, mergedZero1536 x h]
  simp only [add_zero]

theorem mergeCheck1538 : merged1538 = Integer.Sparse.merge (Integer.Sparse.scale (160373465356572427276800) (sourceRows 1542)) (Integer.Sparse.scale (64825273481497811251200) (sourceRows 1543)) := by decide +kernel

theorem mergedZero1538 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1538 x = 0 := by
  rw [mergeCheck1538, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1539 : merged1539 = Integer.Sparse.merge (Integer.Sparse.scale (-33720599657027846304000) (sourceRows 1545)) (Integer.Sparse.scale (-5965826691967030425600) (sourceRows 1546)) := by decide +kernel

theorem mergedZero1539 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1539 x = 0 := by
  rw [mergeCheck1539, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1540 : merged1540 = Integer.Sparse.merge (Integer.Sparse.scale (-20866656050240716800) (sourceRows 1544)) merged1539 := by decide +kernel

theorem mergedZero1540 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1540 x = 0 := by
  rw [mergeCheck1540, Integer.Sparse.eval_merge]
  rw [mergedZero1539 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1541 : merged1541 = Integer.Sparse.merge merged1538 merged1540 := by decide +kernel

theorem mergedZero1541 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1541 x = 0 := by
  rw [mergeCheck1541, Integer.Sparse.eval_merge]
  rw [mergedZero1538 x h, mergedZero1540 x h]
  simp only [add_zero]

theorem mergeCheck1542 : merged1542 = Integer.Sparse.merge (Integer.Sparse.scale (170381854992384000) (sourceRows 1547)) (Integer.Sparse.scale (-412452674631244800) (sourceRows 1548)) := by decide +kernel

theorem mergedZero1542 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1542 x = 0 := by
  rw [mergeCheck1542, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1543 : merged1543 = Integer.Sparse.merge (Integer.Sparse.scale (67099630318257445171200) (sourceRows 1550)) (Integer.Sparse.scale (-650533445636626944000) (sourceRows 1551)) := by decide +kernel

theorem mergedZero1543 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1543 x = 0 := by
  rw [mergeCheck1543, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1544 : merged1544 = Integer.Sparse.merge (Integer.Sparse.scale (21426832097196825600) (sourceRows 1549)) merged1543 := by decide +kernel

theorem mergedZero1544 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1544 x = 0 := by
  rw [mergeCheck1544, Integer.Sparse.eval_merge]
  rw [mergedZero1543 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1545 : merged1545 = Integer.Sparse.merge merged1542 merged1544 := by decide +kernel

theorem mergedZero1545 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1545 x = 0 := by
  rw [mergeCheck1545, Integer.Sparse.eval_merge]
  rw [mergedZero1542 x h, mergedZero1544 x h]
  simp only [add_zero]

theorem mergeCheck1546 : merged1546 = Integer.Sparse.merge merged1541 merged1545 := by decide +kernel

theorem mergedZero1546 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1546 x = 0 := by
  rw [mergeCheck1546, Integer.Sparse.eval_merge]
  rw [mergedZero1541 x h, mergedZero1545 x h]
  simp only [add_zero]

theorem mergeCheck1547 : merged1547 = Integer.Sparse.merge merged1537 merged1546 := by decide +kernel

theorem mergedZero1547 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1547 x = 0 := by
  rw [mergeCheck1547, Integer.Sparse.eval_merge]
  rw [mergedZero1537 x h, mergedZero1546 x h]
  simp only [add_zero]

theorem mergeCheck1548 : merged1548 = Integer.Sparse.merge merged1529 merged1547 := by decide +kernel

theorem mergedZero1548 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1548 x = 0 := by
  rw [mergeCheck1548, Integer.Sparse.eval_merge]
  rw [mergedZero1529 x h, mergedZero1547 x h]
  simp only [add_zero]

theorem mergeCheck1549 : merged1549 = Integer.Sparse.merge (Integer.Sparse.scale (-67766135660137248768000) (sourceRows 1552)) (Integer.Sparse.scale (126340380231110067657600) (sourceRows 1553)) := by decide +kernel

theorem mergedZero1549 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1549 x = 0 := by
  rw [mergeCheck1549, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1550 : merged1550 = Integer.Sparse.merge (Integer.Sparse.scale (12342092738466282422400) (sourceRows 1554)) (Integer.Sparse.scale (4260031649436326400) (sourceRows 1555)) := by decide +kernel

theorem mergedZero1550 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1550 x = 0 := by
  rw [mergeCheck1550, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1551 : merged1551 = Integer.Sparse.merge merged1549 merged1550 := by decide +kernel

theorem mergedZero1551 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1551 x = 0 := by
  rw [mergeCheck1551, Integer.Sparse.eval_merge]
  rw [mergedZero1549 x h, mergedZero1550 x h]
  simp only [add_zero]

theorem mergeCheck1552 : merged1552 = Integer.Sparse.merge (Integer.Sparse.scale (172582021837378221667200) (sourceRows 1556)) (Integer.Sparse.scale (64280496291590476800) (sourceRows 1557)) := by decide +kernel

theorem mergedZero1552 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1552 x = 0 := by
  rw [mergeCheck1552, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1553 : merged1553 = Integer.Sparse.merge (Integer.Sparse.scale (236641465267200) (sourceRows 1559)) (Integer.Sparse.scale (-129317107046400) (sourceRows 1560)) := by decide +kernel

theorem mergedZero1553 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1553 x = 0 := by
  rw [mergeCheck1553, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1554 : merged1554 = Integer.Sparse.merge (Integer.Sparse.scale (252942965060264817004800) (sourceRows 1558)) merged1553 := by decide +kernel

theorem mergedZero1554 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1554 x = 0 := by
  rw [mergeCheck1554, Integer.Sparse.eval_merge]
  rw [mergedZero1553 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1555 : merged1555 = Integer.Sparse.merge merged1552 merged1554 := by decide +kernel

theorem mergedZero1555 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1555 x = 0 := by
  rw [mergeCheck1555, Integer.Sparse.eval_merge]
  rw [mergedZero1552 x h, mergedZero1554 x h]
  simp only [add_zero]

theorem mergeCheck1556 : merged1556 = Integer.Sparse.merge merged1551 merged1555 := by decide +kernel

theorem mergedZero1556 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1556 x = 0 := by
  rw [mergeCheck1556, Integer.Sparse.eval_merge]
  rw [mergedZero1551 x h, mergedZero1555 x h]
  simp only [add_zero]

theorem mergeCheck1557 : merged1557 = Integer.Sparse.merge (Integer.Sparse.scale (5207659294497472512000) (sourceRows 1561)) (Integer.Sparse.scale (-29750890494670168320) (sourceRows 1562)) := by decide +kernel

theorem mergedZero1557 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1557 x = 0 := by
  rw [mergeCheck1557, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1558 : merged1558 = Integer.Sparse.merge (Integer.Sparse.scale (32090593027101509376000) (sourceRows 1564)) (Integer.Sparse.scale (-271068188428800) (sourceRows 1565)) := by decide +kernel

theorem mergedZero1558 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1558 x = 0 := by
  rw [mergeCheck1558, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1559 : merged1559 = Integer.Sparse.merge (Integer.Sparse.scale (5208115452598259712000) (sourceRows 1563)) merged1558 := by decide +kernel

theorem mergedZero1559 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1559 x = 0 := by
  rw [mergeCheck1559, Integer.Sparse.eval_merge]
  rw [mergedZero1558 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1560 : merged1560 = Integer.Sparse.merge merged1557 merged1559 := by decide +kernel

theorem mergedZero1560 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1560 x = 0 := by
  rw [mergeCheck1560, Integer.Sparse.eval_merge]
  rw [mergedZero1557 x h, mergedZero1559 x h]
  simp only [add_zero]

theorem mergeCheck1561 : merged1561 = Integer.Sparse.merge (Integer.Sparse.scale (34010568904742853696000) (sourceRows 1566)) (Integer.Sparse.scale (-630385309209600) (sourceRows 1567)) := by decide +kernel

theorem mergedZero1561 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1561 x = 0 := by
  rw [mergeCheck1561, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1562 : merged1562 = Integer.Sparse.merge (Integer.Sparse.scale (-70351342387200) (sourceRows 1569)) (Integer.Sparse.scale (-1171014574012416000) (sourceRows 1570)) := by decide +kernel

theorem mergedZero1562 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1562 x = 0 := by
  rw [mergeCheck1562, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1563 : merged1563 = Integer.Sparse.merge (Integer.Sparse.scale (-27318004298485367040) (sourceRows 1568)) merged1562 := by decide +kernel

theorem mergedZero1563 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1563 x = 0 := by
  rw [mergeCheck1563, Integer.Sparse.eval_merge]
  rw [mergedZero1562 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1564 : merged1564 = Integer.Sparse.merge merged1561 merged1563 := by decide +kernel

theorem mergedZero1564 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1564 x = 0 := by
  rw [mergeCheck1564, Integer.Sparse.eval_merge]
  rw [mergedZero1561 x h, mergedZero1563 x h]
  simp only [add_zero]

theorem mergeCheck1565 : merged1565 = Integer.Sparse.merge merged1560 merged1564 := by decide +kernel

theorem mergedZero1565 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1565 x = 0 := by
  rw [mergeCheck1565, Integer.Sparse.eval_merge]
  rw [mergedZero1560 x h, mergedZero1564 x h]
  simp only [add_zero]

theorem mergeCheck1566 : merged1566 = Integer.Sparse.merge merged1556 merged1565 := by decide +kernel

theorem mergedZero1566 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1566 x = 0 := by
  rw [mergeCheck1566, Integer.Sparse.eval_merge]
  rw [mergedZero1556 x h, mergedZero1565 x h]
  simp only [add_zero]

theorem mergeCheck1567 : merged1567 = Integer.Sparse.merge (Integer.Sparse.scale (-2382617232595353600000) (sourceRows 1571)) (Integer.Sparse.scale (-137012015185920000) (sourceRows 1572)) := by decide +kernel

theorem mergedZero1567 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1567 x = 0 := by
  rw [mergeCheck1567, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1568 : merged1568 = Integer.Sparse.merge (Integer.Sparse.scale (-2382471576252536832000) (sourceRows 1573)) (Integer.Sparse.scale (-26416229767151922432000) (sourceRows 1574)) := by decide +kernel

theorem mergedZero1568 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1568 x = 0 := by
  rw [mergeCheck1568, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1569 : merged1569 = Integer.Sparse.merge merged1567 merged1568 := by decide +kernel

theorem mergedZero1569 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1569 x = 0 := by
  rw [mergeCheck1569, Integer.Sparse.eval_merge]
  rw [mergedZero1567 x h, mergedZero1568 x h]
  simp only [add_zero]

theorem mergeCheck1570 : merged1570 = Integer.Sparse.merge (Integer.Sparse.scale (118320732633600) (sourceRows 1575)) (Integer.Sparse.scale (-64658553523200) (sourceRows 1576)) := by decide +kernel

theorem mergedZero1570 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1570 x = 0 := by
  rw [mergeCheck1570, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1571 : merged1571 = Integer.Sparse.merge (Integer.Sparse.scale (-802790865968716800) (sourceRows 1578)) (Integer.Sparse.scale (263490172065792000) (sourceRows 1579)) := by decide +kernel

theorem mergedZero1571 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1571 x = 0 := by
  rw [mergeCheck1571, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1572 : merged1572 = Integer.Sparse.merge (Integer.Sparse.scale (-140698179836928000) (sourceRows 1577)) merged1571 := by decide +kernel

theorem mergedZero1572 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1572 x = 0 := by
  rw [mergeCheck1572, Integer.Sparse.eval_merge]
  rw [mergedZero1571 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1573 : merged1573 = Integer.Sparse.merge merged1570 merged1572 := by decide +kernel

theorem mergedZero1573 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1573 x = 0 := by
  rw [mergeCheck1573, Integer.Sparse.eval_merge]
  rw [mergedZero1570 x h, mergedZero1572 x h]
  simp only [add_zero]

theorem mergeCheck1574 : merged1574 = Integer.Sparse.merge merged1569 merged1573 := by decide +kernel

theorem mergedZero1574 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1574 x = 0 := by
  rw [mergeCheck1574, Integer.Sparse.eval_merge]
  rw [mergedZero1569 x h, mergedZero1573 x h]
  simp only [add_zero]

theorem mergeCheck1575 : merged1575 = Integer.Sparse.merge (Integer.Sparse.scale (-6102383671574697024000) (sourceRows 1580)) (Integer.Sparse.scale (197207225629442190086400) (sourceRows 1581)) := by decide +kernel

theorem mergedZero1575 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1575 x = 0 := by
  rw [mergeCheck1575, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1576 : merged1576 = Integer.Sparse.merge (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1583)) (Integer.Sparse.scale (1519783569733976064000) (sourceRows 1584)) := by decide +kernel

theorem mergedZero1576 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1576 x = 0 := by
  rw [mergeCheck1576, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1577 : merged1577 = Integer.Sparse.merge (Integer.Sparse.scale (-33725897799731092972800) (sourceRows 1582)) merged1576 := by decide +kernel

theorem mergedZero1577 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1577 x = 0 := by
  rw [mergeCheck1577, Integer.Sparse.eval_merge]
  rw [mergedZero1576 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1578 : merged1578 = Integer.Sparse.merge merged1575 merged1577 := by decide +kernel

theorem mergedZero1578 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1578 x = 0 := by
  rw [mergeCheck1578, Integer.Sparse.eval_merge]
  rw [mergedZero1575 x h, mergedZero1577 x h]
  simp only [add_zero]

theorem mergeCheck1579 : merged1579 = Integer.Sparse.merge (Integer.Sparse.scale (1519736738724707328000) (sourceRows 1585)) (Integer.Sparse.scale (39645255870290475417600) (sourceRows 1586)) := by decide +kernel

theorem mergedZero1579 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1579 x = 0 := by
  rw [mergeCheck1579, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1580 : merged1580 = Integer.Sparse.merge (Integer.Sparse.scale (-7876535156254154880) (sourceRows 1588)) (Integer.Sparse.scale (28864578355200) (sourceRows 1589)) := by decide +kernel

theorem mergedZero1580 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1580 x = 0 := by
  rw [mergeCheck1580, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1581 : merged1581 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 1587)) merged1580 := by decide +kernel

theorem mergedZero1581 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1581 x = 0 := by
  rw [mergeCheck1581, Integer.Sparse.eval_merge]
  rw [mergedZero1580 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1582 : merged1582 = Integer.Sparse.merge merged1579 merged1581 := by decide +kernel

theorem mergedZero1582 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1582 x = 0 := by
  rw [mergeCheck1582, Integer.Sparse.eval_merge]
  rw [mergedZero1579 x h, mergedZero1581 x h]
  simp only [add_zero]

theorem mergeCheck1583 : merged1583 = Integer.Sparse.merge merged1578 merged1582 := by decide +kernel

theorem mergedZero1583 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1583 x = 0 := by
  rw [mergeCheck1583, Integer.Sparse.eval_merge]
  rw [mergedZero1578 x h, mergedZero1582 x h]
  simp only [add_zero]

theorem mergeCheck1584 : merged1584 = Integer.Sparse.merge merged1574 merged1583 := by decide +kernel

theorem mergedZero1584 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1584 x = 0 := by
  rw [mergeCheck1584, Integer.Sparse.eval_merge]
  rw [mergedZero1574 x h, mergedZero1583 x h]
  simp only [add_zero]

theorem mergeCheck1585 : merged1585 = Integer.Sparse.merge merged1566 merged1584 := by decide +kernel

theorem mergedZero1585 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1585 x = 0 := by
  rw [mergeCheck1585, Integer.Sparse.eval_merge]
  rw [mergedZero1566 x h, mergedZero1584 x h]
  simp only [add_zero]

theorem mergeCheck1586 : merged1586 = Integer.Sparse.merge merged1548 merged1585 := by decide +kernel

theorem mergedZero1586 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1586 x = 0 := by
  rw [mergeCheck1586, Integer.Sparse.eval_merge]
  rw [mergedZero1548 x h, mergedZero1585 x h]
  simp only [add_zero]

theorem mergeCheck1587 : merged1587 = Integer.Sparse.merge (Integer.Sparse.scale (-6398639975804196556800) (sourceRows 1590)) (Integer.Sparse.scale (24419781344301190041600) (sourceRows 1591)) := by decide +kernel

theorem mergedZero1587 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1587 x = 0 := by
  rw [mergeCheck1587, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1588 : merged1588 = Integer.Sparse.merge (Integer.Sparse.scale (34044878707093568160000) (sourceRows 1592)) (Integer.Sparse.scale (-4248206971730362368000) (sourceRows 1593)) := by decide +kernel

theorem mergedZero1588 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1588 x = 0 := by
  rw [mergeCheck1588, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1589 : merged1589 = Integer.Sparse.merge merged1587 merged1588 := by decide +kernel

theorem mergedZero1589 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1589 x = 0 := by
  rw [mergeCheck1589, Integer.Sparse.eval_merge]
  rw [mergedZero1587 x h, mergedZero1588 x h]
  simp only [add_zero]

theorem mergeCheck1590 : merged1590 = Integer.Sparse.merge (Integer.Sparse.scale (-4248625115358425088000) (sourceRows 1594)) (Integer.Sparse.scale (-280453282163712000) (sourceRows 1595)) := by decide +kernel

theorem mergedZero1590 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1590 x = 0 := by
  rw [mergeCheck1590, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1591 : merged1591 = Integer.Sparse.merge (Integer.Sparse.scale (12207153031565877504000) (sourceRows 1597)) (Integer.Sparse.scale (-263490172065792000) (sourceRows 1598)) := by decide +kernel

theorem mergedZero1591 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1591 x = 0 := by
  rw [mergeCheck1591, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1592 : merged1592 = Integer.Sparse.merge (Integer.Sparse.scale (-3199211311789220313600) (sourceRows 1596)) merged1591 := by decide +kernel

theorem mergedZero1592 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1592 x = 0 := by
  rw [mergeCheck1592, Integer.Sparse.eval_merge]
  rw [mergedZero1591 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1593 : merged1593 = Integer.Sparse.merge merged1590 merged1592 := by decide +kernel

theorem mergedZero1593 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1593 x = 0 := by
  rw [mergeCheck1593, Integer.Sparse.eval_merge]
  rw [mergedZero1590 x h, mergedZero1592 x h]
  simp only [add_zero]

theorem mergeCheck1594 : merged1594 = Integer.Sparse.merge merged1589 merged1593 := by decide +kernel

theorem mergedZero1594 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1594 x = 0 := by
  rw [mergeCheck1594, Integer.Sparse.eval_merge]
  rw [mergedZero1589 x h, mergedZero1593 x h]
  simp only [add_zero]

theorem mergeCheck1595 : merged1595 = Integer.Sparse.merge (Integer.Sparse.scale (350565446568960000) (sourceRows 1599)) (Integer.Sparse.scale (-242748815791104000) (sourceRows 1600)) := by decide +kernel

theorem mergedZero1595 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1595 x = 0 := by
  rw [mergeCheck1595, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1596 : merged1596 = Integer.Sparse.merge (Integer.Sparse.scale (62519616250595056828800) (sourceRows 1602)) (Integer.Sparse.scale (2241235474277990400000) (sourceRows 1603)) := by decide +kernel

theorem mergedZero1596 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1596 x = 0 := by
  rw [mergeCheck1596, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1597 : merged1597 = Integer.Sparse.merge (Integer.Sparse.scale (1555112456522956800000) (sourceRows 1601)) merged1596 := by decide +kernel

theorem mergedZero1597 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1597 x = 0 := by
  rw [mergeCheck1597, Integer.Sparse.eval_merge]
  rw [mergedZero1596 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1598 : merged1598 = Integer.Sparse.merge merged1595 merged1597 := by decide +kernel

theorem mergedZero1598 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1598 x = 0 := by
  rw [mergeCheck1598, Integer.Sparse.eval_merge]
  rw [mergedZero1595 x h, mergedZero1597 x h]
  simp only [add_zero]

theorem mergeCheck1599 : merged1599 = Integer.Sparse.merge (Integer.Sparse.scale (-478232461800898560000) (sourceRows 1604)) (Integer.Sparse.scale (-5408603378203821465600) (sourceRows 1605)) := by decide +kernel

theorem mergedZero1599 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1599 x = 0 := by
  rw [mergeCheck1599, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1600 : merged1600 = Integer.Sparse.merge (Integer.Sparse.scale (-5211529733795354726400) (sourceRows 1607)) (Integer.Sparse.scale (44661678105475262361600) (sourceRows 1608)) := by decide +kernel

theorem mergedZero1600 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1600 x = 0 := by
  rw [mergeCheck1600, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1601 : merged1601 = Integer.Sparse.merge (Integer.Sparse.scale (-3200294249547499238400) (sourceRows 1606)) merged1600 := by decide +kernel

theorem mergedZero1601 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1601 x = 0 := by
  rw [mergeCheck1601, Integer.Sparse.eval_merge]
  rw [mergedZero1600 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1602 : merged1602 = Integer.Sparse.merge merged1599 merged1601 := by decide +kernel

theorem mergedZero1602 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1602 x = 0 := by
  rw [mergeCheck1602, Integer.Sparse.eval_merge]
  rw [mergedZero1599 x h, mergedZero1601 x h]
  simp only [add_zero]

theorem mergeCheck1603 : merged1603 = Integer.Sparse.merge merged1598 merged1602 := by decide +kernel

theorem mergedZero1603 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1603 x = 0 := by
  rw [mergeCheck1603, Integer.Sparse.eval_merge]
  rw [mergedZero1598 x h, mergedZero1602 x h]
  simp only [add_zero]

theorem mergeCheck1604 : merged1604 = Integer.Sparse.merge merged1594 merged1603 := by decide +kernel

theorem mergedZero1604 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1604 x = 0 := by
  rw [mergeCheck1604, Integer.Sparse.eval_merge]
  rw [mergedZero1594 x h, mergedZero1603 x h]
  simp only [add_zero]

theorem mergeCheck1605 : merged1605 = Integer.Sparse.merge (Integer.Sparse.scale (208377015638914002686400) (sourceRows 1609)) (Integer.Sparse.scale (-9662719411699200) (sourceRows 1610)) := by decide +kernel

theorem mergedZero1605 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1605 x = 0 := by
  rw [mergeCheck1605, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1606 : merged1606 = Integer.Sparse.merge (Integer.Sparse.scale (-192793368371474655187200) (sourceRows 1611)) (Integer.Sparse.scale (-15909199041323137536000) (sourceRows 1612)) := by decide +kernel

theorem mergedZero1606 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1606 x = 0 := by
  rw [mergeCheck1606, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1607 : merged1607 = Integer.Sparse.merge merged1605 merged1606 := by decide +kernel

theorem mergedZero1607 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1607 x = 0 := by
  rw [mergeCheck1607, Integer.Sparse.eval_merge]
  rw [mergedZero1605 x h, mergedZero1606 x h]
  simp only [add_zero]

theorem mergeCheck1608 : merged1608 = Integer.Sparse.merge (Integer.Sparse.scale (-25448372267670729216000) (sourceRows 1613)) (Integer.Sparse.scale (38478708437494662741600) (sourceRows 1614)) := by decide +kernel

theorem mergedZero1608 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1608 x = 0 := by
  rw [mergeCheck1608, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1609 : merged1609 = Integer.Sparse.merge (Integer.Sparse.scale (-9662719411699200) (sourceRows 1616)) (Integer.Sparse.scale (2908153221987041280000) (sourceRows 1617)) := by decide +kernel

theorem mergedZero1609 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1609 x = 0 := by
  rw [mergeCheck1609, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1610 : merged1610 = Integer.Sparse.merge (Integer.Sparse.scale (7461133972307772825600) (sourceRows 1615)) merged1609 := by decide +kernel

theorem mergedZero1610 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1610 x = 0 := by
  rw [mergeCheck1610, Integer.Sparse.eval_merge]
  rw [mergedZero1609 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1611 : merged1611 = Integer.Sparse.merge merged1608 merged1610 := by decide +kernel

theorem mergedZero1611 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1611 x = 0 := by
  rw [mergeCheck1611, Integer.Sparse.eval_merge]
  rw [mergedZero1608 x h, mergedZero1610 x h]
  simp only [add_zero]

theorem mergeCheck1612 : merged1612 = Integer.Sparse.merge merged1607 merged1611 := by decide +kernel

theorem mergedZero1612 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1612 x = 0 := by
  rw [mergeCheck1612, Integer.Sparse.eval_merge]
  rw [mergedZero1607 x h, mergedZero1611 x h]
  simp only [add_zero]

theorem mergeCheck1613 : merged1613 = Integer.Sparse.merge (Integer.Sparse.scale (19584169193485564416000) (sourceRows 1618)) (Integer.Sparse.scale (-24024559542116184576000) (sourceRows 1619)) := by decide +kernel

theorem mergedZero1613 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1613 x = 0 := by
  rw [mergeCheck1613, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1614 : merged1614 = Integer.Sparse.merge (Integer.Sparse.scale (-96487962399710369308800) (sourceRows 1621)) (Integer.Sparse.scale (-9662719411699200) (sourceRows 1622)) := by decide +kernel

theorem mergedZero1614 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1614 x = 0 := by
  rw [mergeCheck1614, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1615 : merged1615 = Integer.Sparse.merge (Integer.Sparse.scale (76968335901252152145600) (sourceRows 1620)) merged1614 := by decide +kernel

theorem mergedZero1615 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1615 x = 0 := by
  rw [mergeCheck1615, Integer.Sparse.eval_merge]
  rw [mergedZero1614 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1616 : merged1616 = Integer.Sparse.merge merged1613 merged1615 := by decide +kernel

theorem mergedZero1616 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1616 x = 0 := by
  rw [mergeCheck1616, Integer.Sparse.eval_merge]
  rw [mergedZero1613 x h, mergedZero1615 x h]
  simp only [add_zero]

theorem mergeCheck1617 : merged1617 = Integer.Sparse.merge (Integer.Sparse.scale (42181971804222721228800) (sourceRows 1623)) (Integer.Sparse.scale (104193967332588414674400) (sourceRows 1624)) := by decide +kernel

theorem mergedZero1617 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1617 x = 0 := by
  rw [mergeCheck1617, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1618 : merged1618 = Integer.Sparse.merge (Integer.Sparse.scale (17350219930668710400) (sourceRows 1626)) (Integer.Sparse.scale (17128446791049216000) (sourceRows 1627)) := by decide +kernel

theorem mergedZero1618 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1618 x = 0 := by
  rw [mergeCheck1618, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1619 : merged1619 = Integer.Sparse.merge (Integer.Sparse.scale (-65930063312981500416000) (sourceRows 1625)) merged1618 := by decide +kernel

theorem mergedZero1619 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1619 x = 0 := by
  rw [mergeCheck1619, Integer.Sparse.eval_merge]
  rw [mergedZero1618 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1620 : merged1620 = Integer.Sparse.merge merged1617 merged1619 := by decide +kernel

theorem mergedZero1620 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1620 x = 0 := by
  rw [mergeCheck1620, Integer.Sparse.eval_merge]
  rw [mergedZero1617 x h, mergedZero1619 x h]
  simp only [add_zero]

theorem mergeCheck1621 : merged1621 = Integer.Sparse.merge merged1616 merged1620 := by decide +kernel

theorem mergedZero1621 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1621 x = 0 := by
  rw [mergeCheck1621, Integer.Sparse.eval_merge]
  rw [mergedZero1616 x h, mergedZero1620 x h]
  simp only [add_zero]

theorem mergeCheck1622 : merged1622 = Integer.Sparse.merge merged1612 merged1621 := by decide +kernel

theorem mergedZero1622 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1622 x = 0 := by
  rw [mergeCheck1622, Integer.Sparse.eval_merge]
  rw [mergedZero1612 x h, mergedZero1621 x h]
  simp only [add_zero]

theorem mergeCheck1623 : merged1623 = Integer.Sparse.merge merged1604 merged1622 := by decide +kernel

theorem mergedZero1623 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1623 x = 0 := by
  rw [mergeCheck1623, Integer.Sparse.eval_merge]
  rw [mergedZero1604 x h, mergedZero1622 x h]
  simp only [add_zero]

theorem mergeCheck1624 : merged1624 = Integer.Sparse.merge (Integer.Sparse.scale (-45582100249500057600000) (sourceRows 1628)) (Integer.Sparse.scale (17350219930668710400) (sourceRows 1629)) := by decide +kernel

theorem mergedZero1624 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1624 x = 0 := by
  rw [mergeCheck1624, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1625 : merged1625 = Integer.Sparse.merge (Integer.Sparse.scale (-124076748593445529190400) (sourceRows 1630)) (Integer.Sparse.scale (-173045828282394641817600) (sourceRows 1631)) := by decide +kernel

theorem mergedZero1625 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1625 x = 0 := by
  rw [mergeCheck1625, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1626 : merged1626 = Integer.Sparse.merge merged1624 merged1625 := by decide +kernel

theorem mergedZero1626 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1626 x = 0 := by
  rw [mergeCheck1626, Integer.Sparse.eval_merge]
  rw [mergedZero1624 x h, mergedZero1625 x h]
  simp only [add_zero]

theorem mergeCheck1627 : merged1627 = Integer.Sparse.merge (Integer.Sparse.scale (4167404634193920000000) (sourceRows 1632)) (Integer.Sparse.scale (-17350219930668710400) (sourceRows 1633)) := by decide +kernel

theorem mergedZero1627 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1627 x = 0 := by
  rw [mergeCheck1627, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1628 : merged1628 = Integer.Sparse.merge (Integer.Sparse.scale (46173205774623471364800) (sourceRows 1635)) (Integer.Sparse.scale (-17350219930668710400) (sourceRows 1636)) := by decide +kernel

theorem mergedZero1628 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1628 x = 0 := by
  rw [mergeCheck1628, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1629 : merged1629 = Integer.Sparse.merge (Integer.Sparse.scale (38957798484739620662400) (sourceRows 1634)) merged1628 := by decide +kernel

theorem mergedZero1629 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1629 x = 0 := by
  rw [mergeCheck1629, Integer.Sparse.eval_merge]
  rw [mergedZero1628 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1630 : merged1630 = Integer.Sparse.merge merged1627 merged1629 := by decide +kernel

theorem mergedZero1630 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1630 x = 0 := by
  rw [mergeCheck1630, Integer.Sparse.eval_merge]
  rw [mergedZero1627 x h, mergedZero1629 x h]
  simp only [add_zero]

theorem mergeCheck1631 : merged1631 = Integer.Sparse.merge merged1626 merged1630 := by decide +kernel

theorem mergedZero1631 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1631 x = 0 := by
  rw [mergeCheck1631, Integer.Sparse.eval_merge]
  rw [mergedZero1626 x h, mergedZero1630 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1632 : merged1632 = Integer.Sparse.merge (Integer.Sparse.scale (-92199818708304836860800) (sourceRows 1637)) (Integer.Sparse.scale (289658132310823866777600) (sourceRows 1638)) := by decide +kernel

theorem mergedZero1632 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1632 x = 0 := by
  rw [mergeCheck1632, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1633 : merged1633 = Integer.Sparse.merge (Integer.Sparse.scale (21681282096458611200) (sourceRows 1640)) (Integer.Sparse.scale (-17350219930668710400) (sourceRows 1641)) := by decide +kernel

theorem mergedZero1633 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1633 x = 0 := by
  rw [mergeCheck1633, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1634 : merged1634 = Integer.Sparse.merge (Integer.Sparse.scale (26784795852324518400) (sourceRows 1639)) merged1633 := by decide +kernel

theorem mergedZero1634 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1634 x = 0 := by
  rw [mergeCheck1634, Integer.Sparse.eval_merge]
  rw [mergedZero1633 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1635 : merged1635 = Integer.Sparse.merge merged1632 merged1634 := by decide +kernel

theorem mergedZero1635 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1635 x = 0 := by
  rw [mergeCheck1635, Integer.Sparse.eval_merge]
  rw [mergedZero1632 x h, mergedZero1634 x h]
  simp only [add_zero]

theorem mergeCheck1636 : merged1636 = Integer.Sparse.merge (Integer.Sparse.scale (-180325079944624742400) (sourceRows 1642)) (Integer.Sparse.scale (-280557301130864371353600) (sourceRows 1643)) := by decide +kernel

theorem mergedZero1636 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1636 x = 0 := by
  rw [mergeCheck1636, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1637 : merged1637 = Integer.Sparse.merge (Integer.Sparse.scale (316404265876691731200) (sourceRows 1645)) (Integer.Sparse.scale (4262782372319923200) (sourceRows 1646)) := by decide +kernel

theorem mergedZero1637 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1637 x = 0 := by
  rw [mergeCheck1637, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1638 : merged1638 = Integer.Sparse.merge (Integer.Sparse.scale (-84012156868546893772800) (sourceRows 1644)) merged1637 := by decide +kernel

theorem mergedZero1638 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1638 x = 0 := by
  rw [mergeCheck1638, Integer.Sparse.eval_merge]
  rw [mergedZero1637 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1639 : merged1639 = Integer.Sparse.merge merged1636 merged1638 := by decide +kernel

theorem mergedZero1639 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1639 x = 0 := by
  rw [mergeCheck1639, Integer.Sparse.eval_merge]
  rw [mergedZero1636 x h, mergedZero1638 x h]
  simp only [add_zero]

theorem mergeCheck1640 : merged1640 = Integer.Sparse.merge merged1635 merged1639 := by decide +kernel

theorem mergedZero1640 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1640 x = 0 := by
  rw [mergeCheck1640, Integer.Sparse.eval_merge]
  rw [mergedZero1635 x h, mergedZero1639 x h]
  simp only [add_zero]

theorem mergeCheck1641 : merged1641 = Integer.Sparse.merge merged1631 merged1640 := by decide +kernel

theorem mergedZero1641 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1641 x = 0 := by
  rw [mergeCheck1641, Integer.Sparse.eval_merge]
  rw [mergedZero1631 x h, mergedZero1640 x h]
  simp only [add_zero]

theorem mergeCheck1642 : merged1642 = Integer.Sparse.merge (Integer.Sparse.scale (-92486549828885749488000) (sourceRows 1647)) (Integer.Sparse.scale (-671660606131200) (sourceRows 1648)) := by decide +kernel

theorem mergedZero1642 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1642 x = 0 := by
  rw [mergeCheck1642, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1643 : merged1643 = Integer.Sparse.merge (Integer.Sparse.scale (-102349994062866278400) (sourceRows 1649)) (Integer.Sparse.scale (15744414801024000) (sourceRows 1650)) := by decide +kernel

theorem mergedZero1643 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1643 x = 0 := by
  rw [mergeCheck1643, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1644 : merged1644 = Integer.Sparse.merge merged1642 merged1643 := by decide +kernel

theorem mergedZero1644 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1644 x = 0 := by
  rw [mergeCheck1644, Integer.Sparse.eval_merge]
  rw [mergedZero1642 x h, mergedZero1643 x h]
  simp only [add_zero]

theorem mergeCheck1645 : merged1645 = Integer.Sparse.merge (Integer.Sparse.scale (-93618937927626854400) (sourceRows 1651)) (Integer.Sparse.scale (1471964064076800) (sourceRows 1652)) := by decide +kernel

theorem mergedZero1645 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1645 x = 0 := by
  rw [mergeCheck1645, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1646 : merged1646 = Integer.Sparse.merge (Integer.Sparse.scale (105672281702400) (sourceRows 1654)) (Integer.Sparse.scale (81149408928000) (sourceRows 1655)) := by decide +kernel

theorem mergedZero1646 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1646 x = 0 := by
  rw [mergeCheck1646, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1647 : merged1647 = Integer.Sparse.merge (Integer.Sparse.scale (222286495540032806400) (sourceRows 1653)) merged1646 := by decide +kernel

theorem mergedZero1647 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1647 x = 0 := by
  rw [mergeCheck1647, Integer.Sparse.eval_merge]
  rw [mergedZero1646 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1648 : merged1648 = Integer.Sparse.merge merged1645 merged1647 := by decide +kernel

theorem mergedZero1648 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1648 x = 0 := by
  rw [mergeCheck1648, Integer.Sparse.eval_merge]
  rw [mergedZero1645 x h, mergedZero1647 x h]
  simp only [add_zero]

theorem mergeCheck1649 : merged1649 = Integer.Sparse.merge merged1644 merged1648 := by decide +kernel

theorem mergedZero1649 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1649 x = 0 := by
  rw [mergeCheck1649, Integer.Sparse.eval_merge]
  rw [mergedZero1644 x h, mergedZero1648 x h]
  simp only [add_zero]

theorem mergeCheck1650 : merged1650 = Integer.Sparse.merge (Integer.Sparse.scale (-14669215112281887360) (sourceRows 1656)) (Integer.Sparse.scale (-5183040372586610688000) (sourceRows 1657)) := by decide +kernel

theorem mergedZero1650 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1650 x = 0 := by
  rw [mergeCheck1650, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1651 : merged1651 = Integer.Sparse.merge (Integer.Sparse.scale (23640635139841552896000) (sourceRows 1659)) (Integer.Sparse.scale (3315545158816235520000) (sourceRows 1660)) := by decide +kernel

theorem mergedZero1651 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1651 x = 0 := by
  rw [mergeCheck1651, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1652 : merged1652 = Integer.Sparse.merge (Integer.Sparse.scale (-5182971931313906688000) (sourceRows 1658)) merged1651 := by decide +kernel

theorem mergedZero1652 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1652 x = 0 := by
  rw [mergeCheck1652, Integer.Sparse.eval_merge]
  rw [mergedZero1651 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1653 : merged1653 = Integer.Sparse.merge merged1650 merged1652 := by decide +kernel

theorem mergedZero1653 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1653 x = 0 := by
  rw [mergeCheck1653, Integer.Sparse.eval_merge]
  rw [mergedZero1650 x h, mergedZero1652 x h]
  simp only [add_zero]

theorem mergeCheck1654 : merged1654 = Integer.Sparse.merge (Integer.Sparse.scale (28864578355200) (sourceRows 1661)) (Integer.Sparse.scale (-33160084906959360) (sourceRows 1662)) := by decide +kernel

theorem mergedZero1654 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1654 x = 0 := by
  rw [mergeCheck1654, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1655 : merged1655 = Integer.Sparse.merge (Integer.Sparse.scale (2857134787342895001600) (sourceRows 1664)) (Integer.Sparse.scale (40024159959104152473600) (sourceRows 1665)) := by decide +kernel

theorem mergedZero1655 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1655 x = 0 := by
  rw [mergeCheck1655, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1656 : merged1656 = Integer.Sparse.merge (Integer.Sparse.scale (180363883102710760857600) (sourceRows 1663)) merged1655 := by decide +kernel

theorem mergedZero1656 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1656 x = 0 := by
  rw [mergeCheck1656, Integer.Sparse.eval_merge]
  rw [mergedZero1655 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1657 : merged1657 = Integer.Sparse.merge merged1654 merged1656 := by decide +kernel

theorem mergedZero1657 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1657 x = 0 := by
  rw [mergeCheck1657, Integer.Sparse.eval_merge]
  rw [mergedZero1654 x h, mergedZero1656 x h]
  simp only [add_zero]

theorem mergeCheck1658 : merged1658 = Integer.Sparse.merge merged1653 merged1657 := by decide +kernel

theorem mergedZero1658 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1658 x = 0 := by
  rw [mergeCheck1658, Integer.Sparse.eval_merge]
  rw [mergedZero1653 x h, mergedZero1657 x h]
  simp only [add_zero]

theorem mergeCheck1659 : merged1659 = Integer.Sparse.merge merged1649 merged1658 := by decide +kernel

theorem mergedZero1659 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1659 x = 0 := by
  rw [mergeCheck1659, Integer.Sparse.eval_merge]
  rw [mergedZero1649 x h, mergedZero1658 x h]
  simp only [add_zero]

theorem mergeCheck1660 : merged1660 = Integer.Sparse.merge merged1641 merged1659 := by decide +kernel

theorem mergedZero1660 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1660 x = 0 := by
  rw [mergeCheck1660, Integer.Sparse.eval_merge]
  rw [mergedZero1641 x h, mergedZero1659 x h]
  simp only [add_zero]

theorem mergeCheck1661 : merged1661 = Integer.Sparse.merge merged1623 merged1660 := by decide +kernel

theorem mergedZero1661 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1661 x = 0 := by
  rw [mergeCheck1661, Integer.Sparse.eval_merge]
  rw [mergedZero1623 x h, mergedZero1660 x h]
  simp only [add_zero]

theorem mergeCheck1662 : merged1662 = Integer.Sparse.merge merged1586 merged1661 := by decide +kernel

theorem mergedZero1662 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1662 x = 0 := by
  rw [mergeCheck1662, Integer.Sparse.eval_merge]
  rw [mergedZero1586 x h, mergedZero1661 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1814 : merged1814 = Integer.Sparse.merge merged1662 merged1813 := by decide +kernel

theorem mergedZero1814_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1814 x = 0 := by
  rw [mergeCheck1814, Integer.Sparse.eval_merge]
  rw [mergedZero1662 x h, mergedZero1813_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1814_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1814_e_oai
