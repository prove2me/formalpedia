-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1813_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:22:50.651077+00:00
-- url     : https://prove2.me/submissions/bc1918b8-c78c-4bc8-98fd-701b76beefce

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E061
import Definitions.Def_OAIQ106E077

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1663 : merged1663 = Integer.Sparse.merge (Integer.Sparse.scale (162396952993474214400) (sourceRows 1666)) (Integer.Sparse.scale (-143251566798064435200) (sourceRows 1667)) := by decide +kernel

theorem mergedZero1663 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1663 x = 0 := by
  rw [mergeCheck1663, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1664 : merged1664 = Integer.Sparse.merge (Integer.Sparse.scale (-12908069061538775040000) (sourceRows 1668)) (Integer.Sparse.scale (12653140241238003360) (sourceRows 1669)) := by decide +kernel

theorem mergedZero1664 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1664 x = 0 := by
  rw [mergeCheck1664, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1665 : merged1665 = Integer.Sparse.merge merged1663 merged1664 := by decide +kernel

theorem mergedZero1665 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1665 x = 0 := by
  rw [mergeCheck1665, Integer.Sparse.eval_merge]
  rw [mergedZero1663 x h, mergedZero1664 x h]
  simp only [add_zero]

theorem mergeCheck1666 : merged1666 = Integer.Sparse.merge (Integer.Sparse.scale (-12908654721487945728000) (sourceRows 1670)) (Integer.Sparse.scale (24959254190333537894400) (sourceRows 1671)) := by decide +kernel

theorem mergedZero1666 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1666 x = 0 := by
  rw [mergeCheck1666, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1667 : merged1667 = Integer.Sparse.merge (Integer.Sparse.scale (4054107019128864768000) (sourceRows 1673)) (Integer.Sparse.scale (11262088147888085760) (sourceRows 1674)) := by decide +kernel

theorem mergedZero1667 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1667 x = 0 := by
  rw [mergeCheck1667, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1668 : merged1668 = Integer.Sparse.merge (Integer.Sparse.scale (81149408928000) (sourceRows 1672)) merged1667 := by decide +kernel

theorem mergedZero1668 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1668 x = 0 := by
  rw [mergeCheck1668, Integer.Sparse.eval_merge]
  rw [mergedZero1667 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1669 : merged1669 = Integer.Sparse.merge merged1666 merged1668 := by decide +kernel

theorem mergedZero1669 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1669 x = 0 := by
  rw [mergeCheck1669, Integer.Sparse.eval_merge]
  rw [mergedZero1666 x h, mergedZero1668 x h]
  simp only [add_zero]

theorem mergeCheck1670 : merged1670 = Integer.Sparse.merge merged1665 merged1669 := by decide +kernel

theorem mergedZero1670 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1670 x = 0 := by
  rw [mergeCheck1670, Integer.Sparse.eval_merge]
  rw [mergedZero1665 x h, mergedZero1669 x h]
  simp only [add_zero]

theorem mergeCheck1671 : merged1671 = Integer.Sparse.merge (Integer.Sparse.scale (4054055565463271424000) (sourceRows 1675)) (Integer.Sparse.scale (-44840760549461517312000) (sourceRows 1676)) := by decide +kernel

theorem mergedZero1671 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1671 x = 0 := by
  rw [mergeCheck1671, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1672 : merged1672 = Integer.Sparse.merge (Integer.Sparse.scale (-87204332889389153894400) (sourceRows 1678)) (Integer.Sparse.scale (57729156710400) (sourceRows 1679)) := by decide +kernel

theorem mergedZero1672 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1672 x = 0 := by
  rw [mergeCheck1672, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1673 : merged1673 = Integer.Sparse.merge (Integer.Sparse.scale (44840760549461517312000) (sourceRows 1677)) merged1672 := by decide +kernel

theorem mergedZero1673 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1673 x = 0 := by
  rw [mergeCheck1673, Integer.Sparse.eval_merge]
  rw [mergedZero1672 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1674 : merged1674 = Integer.Sparse.merge merged1671 merged1673 := by decide +kernel

theorem mergedZero1674 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1674 x = 0 := by
  rw [mergeCheck1674, Integer.Sparse.eval_merge]
  rw [mergedZero1671 x h, mergedZero1673 x h]
  simp only [add_zero]

theorem mergeCheck1675 : merged1675 = Integer.Sparse.merge (Integer.Sparse.scale (26784795852324518400) (sourceRows 1680)) (Integer.Sparse.scale (16745732405022499200) (sourceRows 1681)) := by decide +kernel

theorem mergedZero1675 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1675 x = 0 := by
  rw [mergeCheck1675, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1676 : merged1676 = Integer.Sparse.merge (Integer.Sparse.scale (1758380531024994508800) (sourceRows 1683)) (Integer.Sparse.scale (-4053417038859976704000) (sourceRows 1684)) := by decide +kernel

theorem mergedZero1676 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1676 x = 0 := by
  rw [mergeCheck1676, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1677 : merged1677 = Integer.Sparse.merge (Integer.Sparse.scale (286503133596128870400) (sourceRows 1682)) merged1676 := by decide +kernel

theorem mergedZero1677 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1677 x = 0 := by
  rw [mergeCheck1677, Integer.Sparse.eval_merge]
  rw [mergedZero1676 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1678 : merged1678 = Integer.Sparse.merge merged1675 merged1677 := by decide +kernel

theorem mergedZero1678 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1678 x = 0 := by
  rw [mergeCheck1678, Integer.Sparse.eval_merge]
  rw [mergedZero1675 x h, mergedZero1677 x h]
  simp only [add_zero]

theorem mergeCheck1679 : merged1679 = Integer.Sparse.merge merged1674 merged1678 := by decide +kernel

theorem mergedZero1679 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1679 x = 0 := by
  rw [mergeCheck1679, Integer.Sparse.eval_merge]
  rw [mergedZero1674 x h, mergedZero1678 x h]
  simp only [add_zero]

theorem mergeCheck1680 : merged1680 = Integer.Sparse.merge merged1670 merged1679 := by decide +kernel

theorem mergedZero1680 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1680 x = 0 := by
  rw [mergeCheck1680, Integer.Sparse.eval_merge]
  rw [mergedZero1670 x h, mergedZero1679 x h]
  simp only [add_zero]

theorem mergeCheck1681 : merged1681 = Integer.Sparse.merge (Integer.Sparse.scale (-4054054198176718848000) (sourceRows 1685)) (Integer.Sparse.scale (-162298817856000) (sourceRows 1686)) := by decide +kernel

theorem mergedZero1681 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1681 x = 0 := by
  rw [mergeCheck1681, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1682 : merged1682 = Integer.Sparse.merge (Integer.Sparse.scale (6266376544982335488000) (sourceRows 1687)) (Integer.Sparse.scale (6266356043255755776000) (sourceRows 1688)) := by decide +kernel

theorem mergedZero1682 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1682 x = 0 := by
  rw [mergeCheck1682, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1683 : merged1683 = Integer.Sparse.merge merged1681 merged1682 := by decide +kernel

theorem mergedZero1683 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1683 x = 0 := by
  rw [mergeCheck1683, Integer.Sparse.eval_merge]
  rw [mergedZero1681 x h, mergedZero1682 x h]
  simp only [add_zero]

theorem mergeCheck1684 : merged1684 = Integer.Sparse.merge (Integer.Sparse.scale (-1198126345399819315200) (sourceRows 1689)) (Integer.Sparse.scale (5211529733795354726400) (sourceRows 1690)) := by decide +kernel

theorem mergedZero1684 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1684 x = 0 := by
  rw [mergeCheck1684, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1685 : merged1685 = Integer.Sparse.merge (Integer.Sparse.scale (130887815827482201600) (sourceRows 1692)) (Integer.Sparse.scale (17921366125916198400) (sourceRows 1693)) := by decide +kernel

theorem mergedZero1685 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1685 x = 0 := by
  rw [mergeCheck1685, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1686 : merged1686 = Integer.Sparse.merge (Integer.Sparse.scale (66127907512390147200) (sourceRows 1691)) merged1685 := by decide +kernel

theorem mergedZero1686 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1686 x = 0 := by
  rw [mergeCheck1686, Integer.Sparse.eval_merge]
  rw [mergedZero1685 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1687 : merged1687 = Integer.Sparse.merge merged1684 merged1686 := by decide +kernel

theorem mergedZero1687 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1687 x = 0 := by
  rw [mergeCheck1687, Integer.Sparse.eval_merge]
  rw [mergedZero1684 x h, mergedZero1686 x h]
  simp only [add_zero]

theorem mergeCheck1688 : merged1688 = Integer.Sparse.merge merged1683 merged1687 := by decide +kernel

theorem mergedZero1688 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1688 x = 0 := by
  rw [mergeCheck1688, Integer.Sparse.eval_merge]
  rw [mergedZero1683 x h, mergedZero1687 x h]
  simp only [add_zero]

theorem mergeCheck1689 : merged1689 = Integer.Sparse.merge (Integer.Sparse.scale (-11041068738619180800) (sourceRows 1694)) (Integer.Sparse.scale (6403435625374905600) (sourceRows 1695)) := by decide +kernel

theorem mergedZero1689 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1689 x = 0 := by
  rw [mergeCheck1689, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1690 : merged1690 = Integer.Sparse.merge (Integer.Sparse.scale (132565670573972025600) (sourceRows 1697)) (Integer.Sparse.scale (141456400533323366400) (sourceRows 1698)) := by decide +kernel

theorem mergedZero1690 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1690 x = 0 := by
  rw [mergeCheck1690, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1691 : merged1691 = Integer.Sparse.merge (Integer.Sparse.scale (-6181875485291116800) (sourceRows 1696)) merged1690 := by decide +kernel

theorem mergedZero1691 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1691 x = 0 := by
  rw [mergeCheck1691, Integer.Sparse.eval_merge]
  rw [mergedZero1690 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1692 : merged1692 = Integer.Sparse.merge merged1689 merged1691 := by decide +kernel

theorem mergedZero1692 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1692 x = 0 := by
  rw [mergeCheck1692, Integer.Sparse.eval_merge]
  rw [mergedZero1689 x h, mergedZero1691 x h]
  simp only [add_zero]

theorem mergeCheck1693 : merged1693 = Integer.Sparse.merge (Integer.Sparse.scale (2131391186159961600) (sourceRows 1699)) (Integer.Sparse.scale (17954076864746534400) (sourceRows 1700)) := by decide +kernel

theorem mergedZero1693 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1693 x = 0 := by
  rw [mergeCheck1693, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1694 : merged1694 = Integer.Sparse.merge (Integer.Sparse.scale (-360878208647233536000) (sourceRows 1702)) (Integer.Sparse.scale (12103008558444195840) (sourceRows 1703)) := by decide +kernel

theorem mergedZero1694 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1694 x = 0 := by
  rw [mergeCheck1694, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1695 : merged1695 = Integer.Sparse.merge (Integer.Sparse.scale (-15264022358538374400) (sourceRows 1701)) merged1694 := by decide +kernel

theorem mergedZero1695 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1695 x = 0 := by
  rw [mergeCheck1695, Integer.Sparse.eval_merge]
  rw [mergedZero1694 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1696 : merged1696 = Integer.Sparse.merge merged1693 merged1695 := by decide +kernel

theorem mergedZero1696 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1696 x = 0 := by
  rw [mergeCheck1696, Integer.Sparse.eval_merge]
  rw [mergedZero1693 x h, mergedZero1695 x h]
  simp only [add_zero]

theorem mergeCheck1697 : merged1697 = Integer.Sparse.merge merged1692 merged1696 := by decide +kernel

theorem mergedZero1697 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1697 x = 0 := by
  rw [mergeCheck1697, Integer.Sparse.eval_merge]
  rw [mergedZero1692 x h, mergedZero1696 x h]
  simp only [add_zero]

theorem mergeCheck1698 : merged1698 = Integer.Sparse.merge merged1688 merged1697 := by decide +kernel

theorem mergedZero1698 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1698 x = 0 := by
  rw [mergeCheck1698, Integer.Sparse.eval_merge]
  rw [mergedZero1688 x h, mergedZero1697 x h]
  simp only [add_zero]

theorem mergeCheck1699 : merged1699 = Integer.Sparse.merge merged1680 merged1698 := by decide +kernel

theorem mergedZero1699 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1699 x = 0 := by
  rw [mergeCheck1699, Integer.Sparse.eval_merge]
  rw [mergedZero1680 x h, mergedZero1698 x h]
  simp only [add_zero]

theorem mergeCheck1700 : merged1700 = Integer.Sparse.merge (Integer.Sparse.scale (-360940079557757952000) (sourceRows 1704)) (Integer.Sparse.scale (-7502822010310572288000) (sourceRows 1705)) := by decide +kernel

theorem mergedZero1700 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1700 x = 0 := by
  rw [mergeCheck1700, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1701 : merged1701 = Integer.Sparse.merge (Integer.Sparse.scale (-2991677648014540800000) (sourceRows 1706)) (Integer.Sparse.scale (2337368765255516160000) (sourceRows 1707)) := by decide +kernel

theorem mergedZero1701 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1701 x = 0 := by
  rw [mergeCheck1701, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1702 : merged1702 = Integer.Sparse.merge merged1700 merged1701 := by decide +kernel

theorem mergedZero1702 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1702 x = 0 := by
  rw [mergeCheck1702, Integer.Sparse.eval_merge]
  rw [mergedZero1700 x h, mergedZero1701 x h]
  simp only [add_zero]

theorem mergeCheck1703 : merged1703 = Integer.Sparse.merge (Integer.Sparse.scale (361768959417600) (sourceRows 1708)) (Integer.Sparse.scale (26795651459404504320) (sourceRows 1709)) := by decide +kernel

theorem mergedZero1703 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1703 x = 0 := by
  rw [mergeCheck1703, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1704 : merged1704 = Integer.Sparse.merge (Integer.Sparse.scale (12294971860790513664000) (sourceRows 1711)) (Integer.Sparse.scale (-169319626499124528537600) (sourceRows 1712)) := by decide +kernel

theorem mergedZero1704 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1704 x = 0 := by
  rw [mergeCheck1704, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1705 : merged1705 = Integer.Sparse.merge (Integer.Sparse.scale (12294112822142828544000) (sourceRows 1710)) merged1704 := by decide +kernel

theorem mergedZero1705 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1705 x = 0 := by
  rw [mergeCheck1705, Integer.Sparse.eval_merge]
  rw [mergedZero1704 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1706 : merged1706 = Integer.Sparse.merge merged1703 merged1705 := by decide +kernel

theorem mergedZero1706 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1706 x = 0 := by
  rw [mergeCheck1706, Integer.Sparse.eval_merge]
  rw [mergedZero1703 x h, mergedZero1705 x h]
  simp only [add_zero]

theorem mergeCheck1707 : merged1707 = Integer.Sparse.merge merged1702 merged1706 := by decide +kernel

theorem mergedZero1707 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1707 x = 0 := by
  rw [mergeCheck1707, Integer.Sparse.eval_merge]
  rw [mergedZero1702 x h, mergedZero1706 x h]
  simp only [add_zero]

theorem mergeCheck1708 : merged1708 = Integer.Sparse.merge (Integer.Sparse.scale (-180363883102710760857600) (sourceRows 1713)) (Integer.Sparse.scale (-265389610048280292556800) (sourceRows 1714)) := by decide +kernel

theorem mergedZero1708 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1708 x = 0 := by
  rw [mergeCheck1708, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1709 : merged1709 = Integer.Sparse.merge (Integer.Sparse.scale (-4309661791672860672000) (sourceRows 1716)) (Integer.Sparse.scale (8457598802903040000) (sourceRows 1717)) := by decide +kernel

theorem mergedZero1709 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1709 x = 0 := by
  rw [mergeCheck1709, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1710 : merged1710 = Integer.Sparse.merge (Integer.Sparse.scale (-118320732633600) (sourceRows 1715)) merged1709 := by decide +kernel

theorem mergedZero1710 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1710 x = 0 := by
  rw [mergeCheck1710, Integer.Sparse.eval_merge]
  rw [mergedZero1709 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1711 : merged1711 = Integer.Sparse.merge merged1708 merged1710 := by decide +kernel

theorem mergedZero1711 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1711 x = 0 := by
  rw [mergeCheck1711, Integer.Sparse.eval_merge]
  rw [mergedZero1708 x h, mergedZero1710 x h]
  simp only [add_zero]

theorem mergeCheck1712 : merged1712 = Integer.Sparse.merge (Integer.Sparse.scale (-4309576940907915264000) (sourceRows 1718)) (Integer.Sparse.scale (22956946401111077376000) (sourceRows 1719)) := by decide +kernel

theorem mergedZero1712 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1712 x = 0 := by
  rw [mergeCheck1712, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1713 : merged1713 = Integer.Sparse.merge (Integer.Sparse.scale (654308882759024640000) (sourceRows 1721)) (Integer.Sparse.scale (-26381106583336860364800) (sourceRows 1722)) := by decide +kernel

theorem mergedZero1713 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1713 x = 0 := by
  rw [mergeCheck1713, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1714 : merged1714 = Integer.Sparse.merge (Integer.Sparse.scale (-22956946401111077376000) (sourceRows 1720)) merged1713 := by decide +kernel

theorem mergedZero1714 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1714 x = 0 := by
  rw [mergeCheck1714, Integer.Sparse.eval_merge]
  rw [mergedZero1713 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1715 : merged1715 = Integer.Sparse.merge merged1712 merged1714 := by decide +kernel

theorem mergedZero1715 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1715 x = 0 := by
  rw [mergeCheck1715, Integer.Sparse.eval_merge]
  rw [mergedZero1712 x h, mergedZero1714 x h]
  simp only [add_zero]

theorem mergeCheck1716 : merged1716 = Integer.Sparse.merge merged1711 merged1715 := by decide +kernel

theorem mergedZero1716 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1716 x = 0 := by
  rw [mergeCheck1716, Integer.Sparse.eval_merge]
  rw [mergedZero1711 x h, mergedZero1715 x h]
  simp only [add_zero]

theorem mergeCheck1717 : merged1717 = Integer.Sparse.merge merged1707 merged1716 := by decide +kernel

theorem mergedZero1717 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1717 x = 0 := by
  rw [mergeCheck1717, Integer.Sparse.eval_merge]
  rw [mergedZero1707 x h, mergedZero1716 x h]
  simp only [add_zero]

theorem mergeCheck1718 : merged1718 = Integer.Sparse.merge (Integer.Sparse.scale (361768959417600) (sourceRows 1723)) (Integer.Sparse.scale (15391910745476697600) (sourceRows 1724)) := by decide +kernel

theorem mergedZero1718 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1718 x = 0 := by
  rw [mergeCheck1718, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1719 : merged1719 = Integer.Sparse.merge (Integer.Sparse.scale (9604260928155694752000) (sourceRows 1725)) (Integer.Sparse.scale (-18423936167248281600) (sourceRows 1726)) := by decide +kernel

theorem mergedZero1719 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1719 x = 0 := by
  rw [mergeCheck1719, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1720 : merged1720 = Integer.Sparse.merge merged1718 merged1719 := by decide +kernel

theorem mergedZero1720 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1720 x = 0 := by
  rw [mergeCheck1720, Integer.Sparse.eval_merge]
  rw [mergedZero1718 x h, mergedZero1719 x h]
  simp only [add_zero]

theorem mergeCheck1721 : merged1721 = Integer.Sparse.merge (Integer.Sparse.scale (-1901921925786624000) (sourceRows 1727)) (Integer.Sparse.scale (15162872287972953600) (sourceRows 1728)) := by decide +kernel

theorem mergedZero1721 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1721 x = 0 := by
  rw [mergeCheck1721, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1722 : merged1722 = Integer.Sparse.merge (Integer.Sparse.scale (-92031197827063270809600) (sourceRows 1730)) (Integer.Sparse.scale (-27977735565765464371200) (sourceRows 1731)) := by decide +kernel

theorem mergedZero1722 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1722 x = 0 := by
  rw [mergeCheck1722, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1723 : merged1723 = Integer.Sparse.merge (Integer.Sparse.scale (-9211968083624140800) (sourceRows 1729)) merged1722 := by decide +kernel

theorem mergedZero1723 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1723 x = 0 := by
  rw [mergeCheck1723, Integer.Sparse.eval_merge]
  rw [mergedZero1722 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1724 : merged1724 = Integer.Sparse.merge merged1721 merged1723 := by decide +kernel

theorem mergedZero1724 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1724 x = 0 := by
  rw [mergeCheck1724, Integer.Sparse.eval_merge]
  rw [mergedZero1721 x h, mergedZero1723 x h]
  simp only [add_zero]

theorem mergeCheck1725 : merged1725 = Integer.Sparse.merge merged1720 merged1724 := by decide +kernel

theorem mergedZero1725 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1725 x = 0 := by
  rw [mergeCheck1725, Integer.Sparse.eval_merge]
  rw [mergedZero1720 x h, mergedZero1724 x h]
  simp only [add_zero]

theorem mergeCheck1726 : merged1726 = Integer.Sparse.merge (Integer.Sparse.scale (-24408469453804240896000) (sourceRows 1732)) (Integer.Sparse.scale (-7308073462294886400) (sourceRows 1733)) := by decide +kernel

theorem mergedZero1726 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1726 x = 0 := by
  rw [mergeCheck1726, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1727 : merged1727 = Integer.Sparse.merge (Integer.Sparse.scale (1497118266153345024000) (sourceRows 1735)) (Integer.Sparse.scale (-2193578587128499200) (sourceRows 1736)) := by decide +kernel

theorem mergedZero1727 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1727 x = 0 := by
  rw [mergeCheck1727, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1728 : merged1728 = Integer.Sparse.merge (Integer.Sparse.scale (1495698641158256640000) (sourceRows 1734)) merged1727 := by decide +kernel

theorem mergedZero1728 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1728 x = 0 := by
  rw [mergeCheck1728, Integer.Sparse.eval_merge]
  rw [mergedZero1727 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1729 : merged1729 = Integer.Sparse.merge merged1726 merged1728 := by decide +kernel

theorem mergedZero1729 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1729 x = 0 := by
  rw [mergeCheck1729, Integer.Sparse.eval_merge]
  rw [mergedZero1726 x h, mergedZero1728 x h]
  simp only [add_zero]

theorem mergeCheck1730 : merged1730 = Integer.Sparse.merge (Integer.Sparse.scale (15473992049975692800) (sourceRows 1737)) (Integer.Sparse.scale (-701130893137920000) (sourceRows 1738)) := by decide +kernel

theorem mergedZero1730 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1730 x = 0 := by
  rw [mergeCheck1730, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1731 : merged1731 = Integer.Sparse.merge (Integer.Sparse.scale (473232744051863040000) (sourceRows 1740)) (Integer.Sparse.scale (473313643939325952000) (sourceRows 1741)) := by decide +kernel

theorem mergedZero1731 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1731 x = 0 := by
  rw [mergeCheck1731, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1732 : merged1732 = Integer.Sparse.merge (Integer.Sparse.scale (175282723284480000) (sourceRows 1739)) merged1731 := by decide +kernel

theorem mergedZero1732 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1732 x = 0 := by
  rw [mergeCheck1732, Integer.Sparse.eval_merge]
  rw [mergedZero1731 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1733 : merged1733 = Integer.Sparse.merge merged1730 merged1732 := by decide +kernel

theorem mergedZero1733 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1733 x = 0 := by
  rw [mergeCheck1733, Integer.Sparse.eval_merge]
  rw [mergedZero1730 x h, mergedZero1732 x h]
  simp only [add_zero]

theorem mergeCheck1734 : merged1734 = Integer.Sparse.merge merged1729 merged1733 := by decide +kernel

theorem mergedZero1734 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1734 x = 0 := by
  rw [mergeCheck1734, Integer.Sparse.eval_merge]
  rw [mergedZero1729 x h, mergedZero1733 x h]
  simp only [add_zero]

theorem mergeCheck1735 : merged1735 = Integer.Sparse.merge merged1725 merged1734 := by decide +kernel

theorem mergedZero1735 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1735 x = 0 := by
  rw [mergeCheck1735, Integer.Sparse.eval_merge]
  rw [mergedZero1725 x h, mergedZero1734 x h]
  simp only [add_zero]

theorem mergeCheck1736 : merged1736 = Integer.Sparse.merge merged1717 merged1735 := by decide +kernel

theorem mergedZero1736 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1736 x = 0 := by
  rw [mergeCheck1736, Integer.Sparse.eval_merge]
  rw [mergedZero1717 x h, mergedZero1735 x h]
  simp only [add_zero]

theorem mergeCheck1737 : merged1737 = Integer.Sparse.merge merged1699 merged1736 := by decide +kernel

theorem mergedZero1737 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1737 x = 0 := by
  rw [mergeCheck1737, Integer.Sparse.eval_merge]
  rw [mergedZero1699 x h, mergedZero1736 x h]
  simp only [add_zero]

theorem mergeCheck1738 : merged1738 = Integer.Sparse.merge (Integer.Sparse.scale (294105661149159014400) (sourceRows 1742)) (Integer.Sparse.scale (-701130893137920000) (sourceRows 1743)) := by decide +kernel

theorem mergedZero1738 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1738 x = 0 := by
  rw [mergeCheck1738, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1739 : merged1739 = Integer.Sparse.merge (Integer.Sparse.scale (57054795103272960) (sourceRows 1744)) (Integer.Sparse.scale (-22686231812929122816000) (sourceRows 1745)) := by decide +kernel

theorem mergedZero1739 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1739 x = 0 := by
  rw [mergeCheck1739, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1740 : merged1740 = Integer.Sparse.merge merged1738 merged1739 := by decide +kernel

theorem mergedZero1740 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1740 x = 0 := by
  rw [mergeCheck1740, Integer.Sparse.eval_merge]
  rw [mergedZero1738 x h, mergedZero1739 x h]
  simp only [add_zero]

theorem mergeCheck1741 : merged1741 = Integer.Sparse.merge (Integer.Sparse.scale (3496865910938265600) (sourceRows 1746)) (Integer.Sparse.scale (41568524487981266227200) (sourceRows 1747)) := by decide +kernel

theorem mergedZero1741 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1741 x = 0 := by
  rw [mergeCheck1741, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1742 : merged1742 = Integer.Sparse.merge (Integer.Sparse.scale (3773693393876448000) (sourceRows 1749)) (Integer.Sparse.scale (-1770709794526310400) (sourceRows 1750)) := by decide +kernel

theorem mergedZero1742 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1742 x = 0 := by
  rw [mergeCheck1742, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1743 : merged1743 = Integer.Sparse.merge (Integer.Sparse.scale (-25534112982752457216000) (sourceRows 1748)) merged1742 := by decide +kernel

theorem mergedZero1743 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1743 x = 0 := by
  rw [mergeCheck1743, Integer.Sparse.eval_merge]
  rw [mergedZero1742 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1744 : merged1744 = Integer.Sparse.merge merged1741 merged1743 := by decide +kernel

theorem mergedZero1744 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1744 x = 0 := by
  rw [mergeCheck1744, Integer.Sparse.eval_merge]
  rw [mergedZero1741 x h, mergedZero1743 x h]
  simp only [add_zero]

theorem mergeCheck1745 : merged1745 = Integer.Sparse.merge merged1740 merged1744 := by decide +kernel

theorem mergedZero1745 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1745 x = 0 := by
  rw [mergeCheck1745, Integer.Sparse.eval_merge]
  rw [mergedZero1740 x h, mergedZero1744 x h]
  simp only [add_zero]

theorem mergeCheck1746 : merged1746 = Integer.Sparse.merge (Integer.Sparse.scale (-42803540231282488627200) (sourceRows 1751)) (Integer.Sparse.scale (40784198334970096742400) (sourceRows 1752)) := by decide +kernel

theorem mergedZero1746 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1746 x = 0 := by
  rw [mergeCheck1746, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1747 : merged1747 = Integer.Sparse.merge (Integer.Sparse.scale (-2569672923078240000) (sourceRows 1754)) (Integer.Sparse.scale (-1770709794526310400) (sourceRows 1755)) := by decide +kernel

theorem mergedZero1747 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1747 x = 0 := by
  rw [mergeCheck1747, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1748 : merged1748 = Integer.Sparse.merge (Integer.Sparse.scale (7547386787752896000) (sourceRows 1753)) merged1747 := by decide +kernel

theorem mergedZero1748 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1748 x = 0 := by
  rw [mergeCheck1748, Integer.Sparse.eval_merge]
  rw [mergedZero1747 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1749 : merged1749 = Integer.Sparse.merge merged1746 merged1748 := by decide +kernel

theorem mergedZero1749 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1749 x = 0 := by
  rw [mergeCheck1749, Integer.Sparse.eval_merge]
  rw [mergedZero1746 x h, mergedZero1748 x h]
  simp only [add_zero]

theorem mergeCheck1750 : merged1750 = Integer.Sparse.merge (Integer.Sparse.scale (-1863973528737546240000) (sourceRows 1756)) (Integer.Sparse.scale (-1770709794526310400) (sourceRows 1757)) := by decide +kernel

theorem mergedZero1750 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1750 x = 0 := by
  rw [mergeCheck1750, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1751 : merged1751 = Integer.Sparse.merge (Integer.Sparse.scale (-6952024476549398937600) (sourceRows 1759)) (Integer.Sparse.scale (16040059898978304000) (sourceRows 1760)) := by decide +kernel

theorem mergedZero1751 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1751 x = 0 := by
  rw [mergeCheck1751, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1752 : merged1752 = Integer.Sparse.merge (Integer.Sparse.scale (13120079437306920960000) (sourceRows 1758)) merged1751 := by decide +kernel

theorem mergedZero1752 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1752 x = 0 := by
  rw [mergeCheck1752, Integer.Sparse.eval_merge]
  rw [mergedZero1751 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1753 : merged1753 = Integer.Sparse.merge merged1750 merged1752 := by decide +kernel

theorem mergedZero1753 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1753 x = 0 := by
  rw [mergeCheck1753, Integer.Sparse.eval_merge]
  rw [mergedZero1750 x h, mergedZero1752 x h]
  simp only [add_zero]

theorem mergeCheck1754 : merged1754 = Integer.Sparse.merge merged1749 merged1753 := by decide +kernel

theorem mergedZero1754 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1754 x = 0 := by
  rw [mergeCheck1754, Integer.Sparse.eval_merge]
  rw [mergedZero1749 x h, mergedZero1753 x h]
  simp only [add_zero]

theorem mergeCheck1755 : merged1755 = Integer.Sparse.merge merged1745 merged1754 := by decide +kernel

theorem mergedZero1755 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1755 x = 0 := by
  rw [mergeCheck1755, Integer.Sparse.eval_merge]
  rw [mergedZero1745 x h, mergedZero1754 x h]
  simp only [add_zero]

theorem mergeCheck1756 : merged1756 = Integer.Sparse.merge (Integer.Sparse.scale (3215596833921024000) (sourceRows 1761)) (Integer.Sparse.scale (-27156418471526400000) (sourceRows 1762)) := by decide +kernel

theorem mergedZero1756 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1756 x = 0 := by
  rw [mergeCheck1756, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1757 : merged1757 = Integer.Sparse.merge (Integer.Sparse.scale (-36218966526549615513600) (sourceRows 1763)) (Integer.Sparse.scale (136972496683008000) (sourceRows 1764)) := by decide +kernel

theorem mergedZero1757 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1757 x = 0 := by
  rw [mergeCheck1757, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1758 : merged1758 = Integer.Sparse.merge merged1756 merged1757 := by decide +kernel

theorem mergedZero1758 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1758 x = 0 := by
  rw [mergeCheck1758, Integer.Sparse.eval_merge]
  rw [mergedZero1756 x h, mergedZero1757 x h]
  simp only [add_zero]

theorem mergeCheck1759 : merged1759 = Integer.Sparse.merge (Integer.Sparse.scale (3215596833921024000) (sourceRows 1765)) (Integer.Sparse.scale (-76313428175881116057600) (sourceRows 1766)) := by decide +kernel

theorem mergedZero1759 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1759 x = 0 := by
  rw [mergeCheck1759, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1760 : merged1760 = Integer.Sparse.merge (Integer.Sparse.scale (-3215596833921024000) (sourceRows 1768)) (Integer.Sparse.scale (19383598030147545600) (sourceRows 1769)) := by decide +kernel

theorem mergedZero1760 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1760 x = 0 := by
  rw [mergeCheck1760, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1761 : merged1761 = Integer.Sparse.merge (Integer.Sparse.scale (1415934024744960000000) (sourceRows 1767)) merged1760 := by decide +kernel

theorem mergedZero1761 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1761 x = 0 := by
  rw [mergeCheck1761, Integer.Sparse.eval_merge]
  rw [mergedZero1760 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1762 : merged1762 = Integer.Sparse.merge merged1759 merged1761 := by decide +kernel

theorem mergedZero1762 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1762 x = 0 := by
  rw [mergeCheck1762, Integer.Sparse.eval_merge]
  rw [mergedZero1759 x h, mergedZero1761 x h]
  simp only [add_zero]

theorem mergeCheck1763 : merged1763 = Integer.Sparse.merge merged1758 merged1762 := by decide +kernel

theorem mergedZero1763 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1763 x = 0 := by
  rw [mergeCheck1763, Integer.Sparse.eval_merge]
  rw [mergedZero1758 x h, mergedZero1762 x h]
  simp only [add_zero]

theorem mergeCheck1764 : merged1764 = Integer.Sparse.merge (Integer.Sparse.scale (19910357509401638092800) (sourceRows 1770)) (Integer.Sparse.scale (70988703333631869542400) (sourceRows 1771)) := by decide +kernel

theorem mergedZero1764 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1764 x = 0 := by
  rw [mergeCheck1764, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1765 : merged1765 = Integer.Sparse.merge (Integer.Sparse.scale (12998680655440731955200) (sourceRows 1773)) (Integer.Sparse.scale (4717287960827904000) (sourceRows 1774)) := by decide +kernel

theorem mergedZero1765 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1765 x = 0 := by
  rw [mergeCheck1765, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1766 : merged1766 = Integer.Sparse.merge (Integer.Sparse.scale (-154684550564832260044800) (sourceRows 1772)) merged1765 := by decide +kernel

theorem mergedZero1766 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1766 x = 0 := by
  rw [mergeCheck1766, Integer.Sparse.eval_merge]
  rw [mergedZero1765 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1767 : merged1767 = Integer.Sparse.merge merged1764 merged1766 := by decide +kernel

theorem mergedZero1767 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1767 x = 0 := by
  rw [mergeCheck1767, Integer.Sparse.eval_merge]
  rw [mergedZero1764 x h, mergedZero1766 x h]
  simp only [add_zero]

theorem mergeCheck1768 : merged1768 = Integer.Sparse.merge (Integer.Sparse.scale (-25689366208062911692800) (sourceRows 1775)) (Integer.Sparse.scale (-161169374095679880806400) (sourceRows 1776)) := by decide +kernel

theorem mergedZero1768 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1768 x = 0 := by
  rw [mergeCheck1768, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1769 : merged1769 = Integer.Sparse.merge (Integer.Sparse.scale (-1991486997089049600) (sourceRows 1778)) (Integer.Sparse.scale (-11602987217177932800) (sourceRows 1779)) := by decide +kernel

theorem mergedZero1769 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1769 x = 0 := by
  rw [mergeCheck1769, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1770 : merged1770 = Integer.Sparse.merge (Integer.Sparse.scale (4331062165789900800) (sourceRows 1777)) merged1769 := by decide +kernel

theorem mergedZero1770 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1770 x = 0 := by
  rw [mergeCheck1770, Integer.Sparse.eval_merge]
  rw [mergedZero1769 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1771 : merged1771 = Integer.Sparse.merge merged1768 merged1770 := by decide +kernel

theorem mergedZero1771 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1771 x = 0 := by
  rw [mergeCheck1771, Integer.Sparse.eval_merge]
  rw [mergedZero1768 x h, mergedZero1770 x h]
  simp only [add_zero]

theorem mergeCheck1772 : merged1772 = Integer.Sparse.merge merged1767 merged1771 := by decide +kernel

theorem mergedZero1772 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1772 x = 0 := by
  rw [mergeCheck1772, Integer.Sparse.eval_merge]
  rw [mergedZero1767 x h, mergedZero1771 x h]
  simp only [add_zero]

theorem mergeCheck1773 : merged1773 = Integer.Sparse.merge merged1763 merged1772 := by decide +kernel

theorem mergedZero1773 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1773 x = 0 := by
  rw [mergeCheck1773, Integer.Sparse.eval_merge]
  rw [mergedZero1763 x h, mergedZero1772 x h]
  simp only [add_zero]

theorem mergeCheck1774 : merged1774 = Integer.Sparse.merge merged1755 merged1773 := by decide +kernel

theorem mergedZero1774 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1774 x = 0 := by
  rw [mergeCheck1774, Integer.Sparse.eval_merge]
  rw [mergedZero1755 x h, mergedZero1773 x h]
  simp only [add_zero]

theorem mergeCheck1775 : merged1775 = Integer.Sparse.merge (Integer.Sparse.scale (78230454220800) (sourceRows 1780)) (Integer.Sparse.scale (110994539141323192320) (sourceRows 1781)) := by decide +kernel

theorem mergedZero1775 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1775 x = 0 := by
  rw [mergeCheck1775, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1776 : merged1776 = Integer.Sparse.merge (Integer.Sparse.scale (412348938624000) (sourceRows 1782)) (Integer.Sparse.scale (-538512615192384000) (sourceRows 1783)) := by decide +kernel

theorem mergedZero1776 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1776 x = 0 := by
  rw [mergeCheck1776, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1777 : merged1777 = Integer.Sparse.merge merged1775 merged1776 := by decide +kernel

theorem mergedZero1777 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1777 x = 0 := by
  rw [mergeCheck1777, Integer.Sparse.eval_merge]
  rw [mergedZero1775 x h, mergedZero1776 x h]
  simp only [add_zero]

theorem mergeCheck1778 : merged1778 = Integer.Sparse.merge (Integer.Sparse.scale (-28178996428800) (sourceRows 1784)) (Integer.Sparse.scale (-18983562498929226240) (sourceRows 1785)) := by decide +kernel

theorem mergedZero1778 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1778 x = 0 := by
  rw [mergeCheck1778, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1779 : merged1779 = Integer.Sparse.merge (Integer.Sparse.scale (-342820359049931642880) (sourceRows 1787)) (Integer.Sparse.scale (-15817952191104000) (sourceRows 1788)) := by decide +kernel

theorem mergedZero1779 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1779 x = 0 := by
  rw [mergeCheck1779, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1780 : merged1780 = Integer.Sparse.merge (Integer.Sparse.scale (-976405144780800) (sourceRows 1786)) merged1779 := by decide +kernel

theorem mergedZero1780 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1780 x = 0 := by
  rw [mergeCheck1780, Integer.Sparse.eval_merge]
  rw [mergedZero1779 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1781 : merged1781 = Integer.Sparse.merge merged1778 merged1780 := by decide +kernel

theorem mergedZero1781 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1781 x = 0 := by
  rw [mergeCheck1781, Integer.Sparse.eval_merge]
  rw [mergedZero1778 x h, mergedZero1780 x h]
  simp only [add_zero]

theorem mergeCheck1782 : merged1782 = Integer.Sparse.merge merged1777 merged1781 := by decide +kernel

theorem mergedZero1782 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1782 x = 0 := by
  rw [mergeCheck1782, Integer.Sparse.eval_merge]
  rw [mergedZero1777 x h, mergedZero1781 x h]
  simp only [add_zero]

theorem mergeCheck1783 : merged1783 = Integer.Sparse.merge (Integer.Sparse.scale (1200107018799780940800) (sourceRows 1789)) (Integer.Sparse.scale (58576147660800) (sourceRows 1790)) := by decide +kernel

theorem mergedZero1783 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1783 x = 0 := by
  rw [mergeCheck1783, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1784 : merged1784 = Integer.Sparse.merge (Integer.Sparse.scale (-1138001372530606080000) (sourceRows 1792)) (Integer.Sparse.scale (-49464526826188770508800) (sourceRows 1793)) := by decide +kernel

theorem mergedZero1784 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1784 x = 0 := by
  rw [mergeCheck1784, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1785 : merged1785 = Integer.Sparse.merge (Integer.Sparse.scale (-14383510443083980800) (sourceRows 1791)) merged1784 := by decide +kernel

theorem mergedZero1785 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1785 x = 0 := by
  rw [mergeCheck1785, Integer.Sparse.eval_merge]
  rw [mergedZero1784 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1786 : merged1786 = Integer.Sparse.merge merged1783 merged1785 := by decide +kernel

theorem mergedZero1786 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1786 x = 0 := by
  rw [mergeCheck1786, Integer.Sparse.eval_merge]
  rw [mergedZero1783 x h, mergedZero1785 x h]
  simp only [add_zero]

theorem mergeCheck1787 : merged1787 = Integer.Sparse.merge (Integer.Sparse.scale (-26784795852324518400) (sourceRows 1794)) (Integer.Sparse.scale (-1169181924481105920000) (sourceRows 1795)) := by decide +kernel

theorem mergedZero1787 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1787 x = 0 := by
  rw [mergeCheck1787, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1788 : merged1788 = Integer.Sparse.merge (Integer.Sparse.scale (-1170216869321428992000) (sourceRows 1797)) (Integer.Sparse.scale (-208794719458533306470400) (sourceRows 1798)) := by decide +kernel

theorem mergedZero1788 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1788 x = 0 := by
  rw [mergeCheck1788, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1789 : merged1789 = Integer.Sparse.merge (Integer.Sparse.scale (-1915115254972416000) (sourceRows 1796)) merged1788 := by decide +kernel

theorem mergedZero1789 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1789 x = 0 := by
  rw [mergeCheck1789, Integer.Sparse.eval_merge]
  rw [mergedZero1788 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1790 : merged1790 = Integer.Sparse.merge merged1787 merged1789 := by decide +kernel

theorem mergedZero1790 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1790 x = 0 := by
  rw [mergeCheck1790, Integer.Sparse.eval_merge]
  rw [mergedZero1787 x h, mergedZero1789 x h]
  simp only [add_zero]

theorem mergeCheck1791 : merged1791 = Integer.Sparse.merge merged1786 merged1790 := by decide +kernel

theorem mergedZero1791 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1791 x = 0 := by
  rw [mergeCheck1791, Integer.Sparse.eval_merge]
  rw [mergedZero1786 x h, mergedZero1790 x h]
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

theorem mergeCheck1792 : merged1792 = Integer.Sparse.merge merged1782 merged1791 := by decide +kernel

theorem mergedZero1792 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1792 x = 0 := by
  rw [mergeCheck1792, Integer.Sparse.eval_merge]
  rw [mergedZero1782 x h, mergedZero1791 x h]
  simp only [add_zero]

theorem mergeCheck1793 : merged1793 = Integer.Sparse.merge (Integer.Sparse.scale (-66661724668426439731200) (sourceRows 1799)) (Integer.Sparse.scale (40537083271041442713600) (sourceRows 1800)) := by decide +kernel

theorem mergedZero1793 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1793 x = 0 := by
  rw [mergeCheck1793, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1794 : merged1794 = Integer.Sparse.merge (Integer.Sparse.scale (2902908387314073600) (sourceRows 1801)) (Integer.Sparse.scale (10919026262826662400) (sourceRows 1802)) := by decide +kernel

theorem mergedZero1794 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1794 x = 0 := by
  rw [mergeCheck1794, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1795 : merged1795 = Integer.Sparse.merge merged1793 merged1794 := by decide +kernel

theorem mergedZero1795 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1795 x = 0 := by
  rw [mergeCheck1795, Integer.Sparse.eval_merge]
  rw [mergedZero1793 x h, mergedZero1794 x h]
  simp only [add_zero]

theorem mergeCheck1796 : merged1796 = Integer.Sparse.merge (Integer.Sparse.scale (-4666690457468928000000) (sourceRows 1803)) (Integer.Sparse.scale (-66463257326179114598400) (sourceRows 1804)) := by decide +kernel

theorem mergedZero1796 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1796 x = 0 := by
  rw [mergeCheck1796, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1797 : merged1797 = Integer.Sparse.merge (Integer.Sparse.scale (-3215596833921024000) (sourceRows 1806)) (Integer.Sparse.scale (-3803843851573248000) (sourceRows 1807)) := by decide +kernel

theorem mergedZero1797 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1797 x = 0 := by
  rw [mergeCheck1797, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1798 : merged1798 = Integer.Sparse.merge (Integer.Sparse.scale (-14235888883075924377600) (sourceRows 1805)) merged1797 := by decide +kernel

theorem mergedZero1798 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1798 x = 0 := by
  rw [mergeCheck1798, Integer.Sparse.eval_merge]
  rw [mergedZero1797 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1799 : merged1799 = Integer.Sparse.merge merged1796 merged1798 := by decide +kernel

theorem mergedZero1799 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1799 x = 0 := by
  rw [mergeCheck1799, Integer.Sparse.eval_merge]
  rw [mergedZero1796 x h, mergedZero1798 x h]
  simp only [add_zero]

theorem mergeCheck1800 : merged1800 = Integer.Sparse.merge merged1795 merged1799 := by decide +kernel

theorem mergedZero1800 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1800 x = 0 := by
  rw [mergeCheck1800, Integer.Sparse.eval_merge]
  rw [mergedZero1795 x h, mergedZero1799 x h]
  simp only [add_zero]

theorem mergeCheck1801 : merged1801 = Integer.Sparse.merge (Integer.Sparse.scale (80238164225378387558400) (sourceRows 1808)) (Integer.Sparse.scale (59345050458059044761600) (sourceRows 1809)) := by decide +kernel

theorem mergedZero1801 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1801 x = 0 := by
  rw [mergeCheck1801, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1802 : merged1802 = Integer.Sparse.merge (Integer.Sparse.scale (2525383848512028672000) (sourceRows 1811)) (Integer.Sparse.scale (2524973042627610624000) (sourceRows 1812)) := by decide +kernel

theorem mergedZero1802 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1802 x = 0 := by
  rw [mergeCheck1802, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1803 : merged1803 = Integer.Sparse.merge (Integer.Sparse.scale (3400767333171855360000) (sourceRows 1810)) merged1802 := by decide +kernel

theorem mergedZero1803 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1803 x = 0 := by
  rw [mergeCheck1803, Integer.Sparse.eval_merge]
  rw [mergedZero1802 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1804 : merged1804 = Integer.Sparse.merge merged1801 merged1803 := by decide +kernel

theorem mergedZero1804 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1804 x = 0 := by
  rw [mergeCheck1804, Integer.Sparse.eval_merge]
  rw [mergedZero1801 x h, mergedZero1803 x h]
  simp only [add_zero]

theorem mergeCheck1805 : merged1805 = Integer.Sparse.merge (Integer.Sparse.scale (3777206074992967680000) (sourceRows 1813)) (Integer.Sparse.scale (-5801493608588966400) (sourceRows 1814)) := by decide +kernel

theorem mergedZero1805 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1805 x = 0 := by
  rw [mergeCheck1805, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1806 : merged1806 = Integer.Sparse.merge (Integer.Sparse.scale (8776111805153280000) (sourceRows 1816)) (Integer.Sparse.scale (-6790833532022077440000) (sourceRows 1817)) := by decide +kernel

theorem mergedZero1806 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1806 x = 0 := by
  rw [mergeCheck1806, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1807 : merged1807 = Integer.Sparse.merge (Integer.Sparse.scale (-6790911489114439680000) (sourceRows 1815)) merged1806 := by decide +kernel

theorem mergedZero1807 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1807 x = 0 := by
  rw [mergeCheck1807, Integer.Sparse.eval_merge]
  rw [mergedZero1806 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1808 : merged1808 = Integer.Sparse.merge merged1805 merged1807 := by decide +kernel

theorem mergedZero1808 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1808 x = 0 := by
  rw [mergeCheck1808, Integer.Sparse.eval_merge]
  rw [mergedZero1805 x h, mergedZero1807 x h]
  simp only [add_zero]

theorem mergeCheck1809 : merged1809 = Integer.Sparse.merge merged1804 merged1808 := by decide +kernel

theorem mergedZero1809 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1809 x = 0 := by
  rw [mergeCheck1809, Integer.Sparse.eval_merge]
  rw [mergedZero1804 x h, mergedZero1808 x h]
  simp only [add_zero]

theorem mergeCheck1810 : merged1810 = Integer.Sparse.merge merged1800 merged1809 := by decide +kernel

theorem mergedZero1810 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1810 x = 0 := by
  rw [mergeCheck1810, Integer.Sparse.eval_merge]
  rw [mergedZero1800 x h, mergedZero1809 x h]
  simp only [add_zero]

theorem mergeCheck1811 : merged1811 = Integer.Sparse.merge merged1792 merged1810 := by decide +kernel

theorem mergedZero1811 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1811 x = 0 := by
  rw [mergeCheck1811, Integer.Sparse.eval_merge]
  rw [mergedZero1792 x h, mergedZero1810 x h]
  simp only [add_zero]

theorem mergeCheck1812 : merged1812 = Integer.Sparse.merge merged1774 merged1811 := by decide +kernel

theorem mergedZero1812 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1812 x = 0 := by
  rw [mergeCheck1812, Integer.Sparse.eval_merge]
  rw [mergedZero1774 x h, mergedZero1811 x h]
  simp only [add_zero]

theorem mergeCheck1813 : merged1813 = Integer.Sparse.merge merged1737 merged1812 := by decide +kernel

theorem mergedZero1813_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1813 x = 0 := by
  rw [mergeCheck1813, Integer.Sparse.eval_merge]
  rw [mergedZero1737 x h, mergedZero1812 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1813_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1813_e_oai
