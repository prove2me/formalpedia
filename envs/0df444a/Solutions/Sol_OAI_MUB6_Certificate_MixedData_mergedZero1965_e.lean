-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1965_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:23:50.465203+00:00
-- url     : https://prove2.me/submissions/5befca5e-172a-495a-9da3-12c8670227e0

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E064
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1964_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1816 : merged1816 = Integer.Sparse.merge (Integer.Sparse.scale (240908039290659234816000) (sourceRows 1818)) (Integer.Sparse.scale (-125469564054547481395200) (sourceRows 1819)) := by decide +kernel

theorem mergedZero1816 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1816 x = 0 := by
  rw [mergeCheck1816, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1817 : merged1817 = Integer.Sparse.merge (Integer.Sparse.scale (169104712542601315737600) (sourceRows 1820)) (Integer.Sparse.scale (-169104712542601315737600) (sourceRows 1821)) := by decide +kernel

theorem mergedZero1817 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1817 x = 0 := by
  rw [mergeCheck1817, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1818 : merged1818 = Integer.Sparse.merge merged1816 merged1817 := by decide +kernel

theorem mergedZero1818 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1818 x = 0 := by
  rw [mergeCheck1818, Integer.Sparse.eval_merge]
  rw [mergedZero1816 x h, mergedZero1817 x h]
  simp only [add_zero]

theorem mergeCheck1819 : merged1819 = Integer.Sparse.merge (Integer.Sparse.scale (-118320732633600) (sourceRows 1822)) (Integer.Sparse.scale (-1901921925786624000) (sourceRows 1823)) := by decide +kernel

theorem mergedZero1819 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1819 x = 0 := by
  rw [mergeCheck1819, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1820 : merged1820 = Integer.Sparse.merge (Integer.Sparse.scale (-2442115563082481664000) (sourceRows 1825)) (Integer.Sparse.scale (-2442044612438839296000) (sourceRows 1826)) := by decide +kernel

theorem mergedZero1820 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1820 x = 0 := by
  rw [mergeCheck1820, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1821 : merged1821 = Integer.Sparse.merge (Integer.Sparse.scale (32710738830336000) (sourceRows 1824)) merged1820 := by decide +kernel

theorem mergedZero1821 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1821 x = 0 := by
  rw [mergeCheck1821, Integer.Sparse.eval_merge]
  rw [mergedZero1820 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1822 : merged1822 = Integer.Sparse.merge merged1819 merged1821 := by decide +kernel

theorem mergedZero1822 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1822 x = 0 := by
  rw [mergeCheck1822, Integer.Sparse.eval_merge]
  rw [mergedZero1819 x h, mergedZero1821 x h]
  simp only [add_zero]

theorem mergeCheck1823 : merged1823 = Integer.Sparse.merge merged1818 merged1822 := by decide +kernel

theorem mergedZero1823 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1823 x = 0 := by
  rw [mergeCheck1823, Integer.Sparse.eval_merge]
  rw [mergedZero1818 x h, mergedZero1822 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1824 : merged1824 = Integer.Sparse.merge (Integer.Sparse.scale (-60557348922893590118400) (sourceRows 1827)) (Integer.Sparse.scale (10996468582939951104000) (sourceRows 1828)) := by decide +kernel

theorem mergedZero1824 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1824 x = 0 := by
  rw [mergeCheck1824, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1825 : merged1825 = Integer.Sparse.merge (Integer.Sparse.scale (10997185720300351488000) (sourceRows 1829)) (Integer.Sparse.scale (73471847768821761638400) (sourceRows 1830)) := by decide +kernel

theorem mergedZero1825 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1825 x = 0 := by
  rw [mergeCheck1825, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1826 : merged1826 = Integer.Sparse.merge merged1824 merged1825 := by decide +kernel

theorem mergedZero1826 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1826 x = 0 := by
  rw [mergeCheck1826, Integer.Sparse.eval_merge]
  rw [mergedZero1824 x h, mergedZero1825 x h]
  simp only [add_zero]

theorem mergeCheck1827 : merged1827 = Integer.Sparse.merge (Integer.Sparse.scale (632609492920860672000) (sourceRows 1831)) (Integer.Sparse.scale (632644968242681856000) (sourceRows 1832)) := by decide +kernel

theorem mergedZero1827 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1827 x = 0 := by
  rw [mergeCheck1827, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1828 : merged1828 = Integer.Sparse.merge (Integer.Sparse.scale (9673103103564515328000) (sourceRows 1834)) (Integer.Sparse.scale (511145564977152000) (sourceRows 1835)) := by decide +kernel

theorem mergedZero1828 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1828 x = 0 := by
  rw [mergeCheck1828, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1829 : merged1829 = Integer.Sparse.merge (Integer.Sparse.scale (9670893906442503168000) (sourceRows 1833)) merged1828 := by decide +kernel

theorem mergedZero1829 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1829 x = 0 := by
  rw [mergeCheck1829, Integer.Sparse.eval_merge]
  rw [mergedZero1828 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1830 : merged1830 = Integer.Sparse.merge merged1827 merged1829 := by decide +kernel

theorem mergedZero1830 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1830 x = 0 := by
  rw [mergeCheck1830, Integer.Sparse.eval_merge]
  rw [mergedZero1827 x h, mergedZero1829 x h]
  simp only [add_zero]

theorem mergeCheck1831 : merged1831 = Integer.Sparse.merge merged1826 merged1830 := by decide +kernel

theorem mergedZero1831 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1831 x = 0 := by
  rw [mergeCheck1831, Integer.Sparse.eval_merge]
  rw [mergedZero1826 x h, mergedZero1830 x h]
  simp only [add_zero]

theorem mergeCheck1832 : merged1832 = Integer.Sparse.merge merged1823 merged1831 := by decide +kernel

theorem mergedZero1832 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1832 x = 0 := by
  rw [mergeCheck1832, Integer.Sparse.eval_merge]
  rw [mergedZero1823 x h, mergedZero1831 x h]
  simp only [add_zero]

theorem mergeCheck1833 : merged1833 = Integer.Sparse.merge (Integer.Sparse.scale (1901921925786624000) (sourceRows 1836)) (Integer.Sparse.scale (1441093683765657600) (sourceRows 1837)) := by decide +kernel

theorem mergedZero1833 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1833 x = 0 := by
  rw [mergeCheck1833, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1834 : merged1834 = Integer.Sparse.merge (Integer.Sparse.scale (255572782488576000) (sourceRows 1838)) (Integer.Sparse.scale (-4472892228971593728000) (sourceRows 1839)) := by decide +kernel

theorem mergedZero1834 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1834 x = 0 := by
  rw [mergeCheck1834, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1835 : merged1835 = Integer.Sparse.merge merged1833 merged1834 := by decide +kernel

theorem mergedZero1835 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1835 x = 0 := by
  rw [mergeCheck1835, Integer.Sparse.eval_merge]
  rw [mergedZero1833 x h, mergedZero1834 x h]
  simp only [add_zero]

theorem mergeCheck1836 : merged1836 = Integer.Sparse.merge (Integer.Sparse.scale (-5793135250384097280) (sourceRows 1840)) (Integer.Sparse.scale (-4472888281759779840000) (sourceRows 1841)) := by decide +kernel

theorem mergedZero1836 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1836 x = 0 := by
  rw [mergeCheck1836, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1837 : merged1837 = Integer.Sparse.merge (Integer.Sparse.scale (-11561314781747114496000) (sourceRows 1843)) (Integer.Sparse.scale (54099605952000) (sourceRows 1844)) := by decide +kernel

theorem mergedZero1837 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1837 x = 0 := by
  rw [mergeCheck1837, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1838 : merged1838 = Integer.Sparse.merge (Integer.Sparse.scale (10598274472208709888000) (sourceRows 1842)) merged1837 := by decide +kernel

theorem mergedZero1838 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1838 x = 0 := by
  rw [mergeCheck1838, Integer.Sparse.eval_merge]
  rw [mergedZero1837 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1839 : merged1839 = Integer.Sparse.merge merged1836 merged1838 := by decide +kernel

theorem mergedZero1839 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1839 x = 0 := by
  rw [mergeCheck1839, Integer.Sparse.eval_merge]
  rw [mergedZero1836 x h, mergedZero1838 x h]
  simp only [add_zero]

theorem mergeCheck1840 : merged1840 = Integer.Sparse.merge merged1835 merged1839 := by decide +kernel

theorem mergedZero1840 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1840 x = 0 := by
  rw [mergeCheck1840, Integer.Sparse.eval_merge]
  rw [mergedZero1835 x h, mergedZero1839 x h]
  simp only [add_zero]

theorem mergeCheck1841 : merged1841 = Integer.Sparse.merge (Integer.Sparse.scale (1883369556620697600) (sourceRows 1845)) (Integer.Sparse.scale (-8290021226739840) (sourceRows 1846)) := by decide +kernel

theorem mergedZero1841 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1841 x = 0 := by
  rw [mergeCheck1841, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1842 : merged1842 = Integer.Sparse.merge (Integer.Sparse.scale (-205746179761963008000) (sourceRows 1848)) (Integer.Sparse.scale (-12676002184402421760) (sourceRows 1849)) := by decide +kernel

theorem mergedZero1842 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1842 x = 0 := by
  rw [mergeCheck1842, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1843 : merged1843 = Integer.Sparse.merge (Integer.Sparse.scale (-307066237052440320) (sourceRows 1847)) merged1842 := by decide +kernel

theorem mergedZero1843 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1843 x = 0 := by
  rw [mergeCheck1843, Integer.Sparse.eval_merge]
  rw [mergedZero1842 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1844 : merged1844 = Integer.Sparse.merge merged1841 merged1843 := by decide +kernel

theorem mergedZero1844 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1844 x = 0 := by
  rw [mergeCheck1844, Integer.Sparse.eval_merge]
  rw [mergedZero1841 x h, mergedZero1843 x h]
  simp only [add_zero]

theorem mergeCheck1845 : merged1845 = Integer.Sparse.merge (Integer.Sparse.scale (-205779422229147648000) (sourceRows 1850)) (Integer.Sparse.scale (-9354947622380091648000) (sourceRows 1851)) := by decide +kernel

theorem mergedZero1845 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1845 x = 0 := by
  rw [mergeCheck1845, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1846 : merged1846 = Integer.Sparse.merge (Integer.Sparse.scale (54099605952000) (sourceRows 1853)) (Integer.Sparse.scale (-9779476741521258240) (sourceRows 1854)) := by decide +kernel

theorem mergedZero1846 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1846 x = 0 := by
  rw [mergeCheck1846, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1847 : merged1847 = Integer.Sparse.merge (Integer.Sparse.scale (33865766668577958912000) (sourceRows 1852)) merged1846 := by decide +kernel

theorem mergedZero1847 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1847 x = 0 := by
  rw [mergeCheck1847, Integer.Sparse.eval_merge]
  rw [mergedZero1846 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1848 : merged1848 = Integer.Sparse.merge merged1845 merged1847 := by decide +kernel

theorem mergedZero1848 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1848 x = 0 := by
  rw [mergeCheck1848, Integer.Sparse.eval_merge]
  rw [mergedZero1845 x h, mergedZero1847 x h]
  simp only [add_zero]

theorem mergeCheck1849 : merged1849 = Integer.Sparse.merge merged1844 merged1848 := by decide +kernel

theorem mergedZero1849 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1849 x = 0 := by
  rw [mergeCheck1849, Integer.Sparse.eval_merge]
  rw [mergedZero1844 x h, mergedZero1848 x h]
  simp only [add_zero]

theorem mergeCheck1850 : merged1850 = Integer.Sparse.merge merged1840 merged1849 := by decide +kernel

theorem mergedZero1850 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1850 x = 0 := by
  rw [mergeCheck1850, Integer.Sparse.eval_merge]
  rw [mergedZero1840 x h, mergedZero1849 x h]
  simp only [add_zero]

theorem mergeCheck1851 : merged1851 = Integer.Sparse.merge merged1832 merged1850 := by decide +kernel

theorem mergedZero1851 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1851 x = 0 := by
  rw [mergeCheck1851, Integer.Sparse.eval_merge]
  rw [mergedZero1832 x h, mergedZero1850 x h]
  simp only [add_zero]

theorem mergeCheck1852 : merged1852 = Integer.Sparse.merge (Integer.Sparse.scale (115458313420800) (sourceRows 1855)) (Integer.Sparse.scale (-33160084906959360) (sourceRows 1856)) := by decide +kernel

theorem mergedZero1852 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1852 x = 0 := by
  rw [mergeCheck1852, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1853 : merged1853 = Integer.Sparse.merge (Integer.Sparse.scale (38962539831253512499200) (sourceRows 1857)) (Integer.Sparse.scale (460809475344433152000) (sourceRows 1858)) := by decide +kernel

theorem mergedZero1853 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1853 x = 0 := by
  rw [mergeCheck1853, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1854 : merged1854 = Integer.Sparse.merge merged1852 merged1853 := by decide +kernel

theorem mergedZero1854 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1854 x = 0 := by
  rw [mergeCheck1854, Integer.Sparse.eval_merge]
  rw [mergedZero1852 x h, mergedZero1853 x h]
  simp only [add_zero]

theorem mergeCheck1855 : merged1855 = Integer.Sparse.merge (Integer.Sparse.scale (16805642993185334400) (sourceRows 1859)) (Integer.Sparse.scale (460827819980494848000) (sourceRows 1860)) := by decide +kernel

theorem mergedZero1855 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1855 x = 0 := by
  rw [mergeCheck1855, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1856 : merged1856 = Integer.Sparse.merge (Integer.Sparse.scale (15376523222686058496000) (sourceRows 1862)) (Integer.Sparse.scale (11561314781747114496000) (sourceRows 1863)) := by decide +kernel

theorem mergedZero1856 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1856 x = 0 := by
  rw [mergeCheck1856, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1857 : merged1857 = Integer.Sparse.merge (Integer.Sparse.scale (-18303489116215865856000) (sourceRows 1861)) merged1856 := by decide +kernel

theorem mergedZero1857 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1857 x = 0 := by
  rw [mergeCheck1857, Integer.Sparse.eval_merge]
  rw [mergedZero1856 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1858 : merged1858 = Integer.Sparse.merge merged1855 merged1857 := by decide +kernel

theorem mergedZero1858 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1858 x = 0 := by
  rw [mergeCheck1858, Integer.Sparse.eval_merge]
  rw [mergedZero1855 x h, mergedZero1857 x h]
  simp only [add_zero]

theorem mergeCheck1859 : merged1859 = Integer.Sparse.merge merged1854 merged1858 := by decide +kernel

theorem mergedZero1859 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1859 x = 0 := by
  rw [mergeCheck1859, Integer.Sparse.eval_merge]
  rw [mergedZero1854 x h, mergedZero1858 x h]
  simp only [add_zero]

theorem mergeCheck1860 : merged1860 = Integer.Sparse.merge (Integer.Sparse.scale (54099605952000) (sourceRows 1864)) (Integer.Sparse.scale (-4672040384326533120000) (sourceRows 1865)) := by decide +kernel

theorem mergedZero1860 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1860 x = 0 := by
  rw [mergeCheck1860, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1861 : merged1861 = Integer.Sparse.merge (Integer.Sparse.scale (-4671888470512349184000) (sourceRows 1867)) (Integer.Sparse.scale (24805961784655704576000) (sourceRows 1868)) := by decide +kernel

theorem mergedZero1861 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1861 x = 0 := by
  rw [mergeCheck1861, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1862 : merged1862 = Integer.Sparse.merge (Integer.Sparse.scale (-4551514511535694080) (sourceRows 1866)) merged1861 := by decide +kernel

theorem mergedZero1862 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1862 x = 0 := by
  rw [mergeCheck1862, Integer.Sparse.eval_merge]
  rw [mergedZero1861 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1863 : merged1863 = Integer.Sparse.merge merged1860 merged1862 := by decide +kernel

theorem mergedZero1863 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1863 x = 0 := by
  rw [mergeCheck1863, Integer.Sparse.eval_merge]
  rw [mergedZero1860 x h, mergedZero1862 x h]
  simp only [add_zero]

theorem mergeCheck1864 : merged1864 = Integer.Sparse.merge (Integer.Sparse.scale (-3829082208146141184000) (sourceRows 1869)) (Integer.Sparse.scale (-33865766668577958912000) (sourceRows 1870)) := by decide +kernel

theorem mergedZero1864 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1864 x = 0 := by
  rw [mergeCheck1864, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1865 : merged1865 = Integer.Sparse.merge (Integer.Sparse.scale (230916626841600) (sourceRows 1872)) (Integer.Sparse.scale (4577684403626901504000) (sourceRows 1873)) := by decide +kernel

theorem mergedZero1865 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1865 x = 0 := by
  rw [mergeCheck1865, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1866 : merged1866 = Integer.Sparse.merge (Integer.Sparse.scale (54099605952000) (sourceRows 1871)) merged1865 := by decide +kernel

theorem mergedZero1866 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1866 x = 0 := by
  rw [mergeCheck1866, Integer.Sparse.eval_merge]
  rw [mergedZero1865 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1867 : merged1867 = Integer.Sparse.merge merged1864 merged1866 := by decide +kernel

theorem mergedZero1867 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1867 x = 0 := by
  rw [mergeCheck1867, Integer.Sparse.eval_merge]
  rw [mergedZero1864 x h, mergedZero1866 x h]
  simp only [add_zero]

theorem mergeCheck1868 : merged1868 = Integer.Sparse.merge merged1863 merged1867 := by decide +kernel

theorem mergedZero1868 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1868 x = 0 := by
  rw [mergeCheck1868, Integer.Sparse.eval_merge]
  rw [mergedZero1863 x h, mergedZero1867 x h]
  simp only [add_zero]

theorem mergeCheck1869 : merged1869 = Integer.Sparse.merge merged1859 merged1868 := by decide +kernel

theorem mergedZero1869 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1869 x = 0 := by
  rw [mergeCheck1869, Integer.Sparse.eval_merge]
  rw [mergedZero1859 x h, mergedZero1868 x h]
  simp only [add_zero]

theorem mergeCheck1870 : merged1870 = Integer.Sparse.merge (Integer.Sparse.scale (-10054389444188443200) (sourceRows 1874)) (Integer.Sparse.scale (4577708607213708288000) (sourceRows 1875)) := by decide +kernel

theorem mergedZero1870 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1870 x = 0 := by
  rw [mergeCheck1870, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1871 : merged1871 = Integer.Sparse.merge (Integer.Sparse.scale (10328414113048898764800) (sourceRows 1876)) (Integer.Sparse.scale (5328860401675593216000) (sourceRows 1877)) := by decide +kernel

theorem mergedZero1871 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1871 x = 0 := by
  rw [mergeCheck1871, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1872 : merged1872 = Integer.Sparse.merge merged1870 merged1871 := by decide +kernel

theorem mergedZero1872 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1872 x = 0 := by
  rw [mergeCheck1872, Integer.Sparse.eval_merge]
  rw [mergedZero1870 x h, mergedZero1871 x h]
  simp only [add_zero]

theorem mergeCheck1873 : merged1873 = Integer.Sparse.merge (Integer.Sparse.scale (5328901865349135360000) (sourceRows 1878)) (Integer.Sparse.scale (-16170919632373692211200) (sourceRows 1879)) := by decide +kernel

theorem mergedZero1873 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1873 x = 0 := by
  rw [mergeCheck1873, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1874 : merged1874 = Integer.Sparse.merge (Integer.Sparse.scale (-701130893137920000) (sourceRows 1881)) (Integer.Sparse.scale (68134203694448640) (sourceRows 1882)) := by decide +kernel

theorem mergedZero1874 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1874 x = 0 := by
  rw [mergeCheck1874, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1875 : merged1875 = Integer.Sparse.merge (Integer.Sparse.scale (-1051696339706880000) (sourceRows 1880)) merged1874 := by decide +kernel

theorem mergedZero1875 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1875 x = 0 := by
  rw [mergeCheck1875, Integer.Sparse.eval_merge]
  rw [mergedZero1874 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1876 : merged1876 = Integer.Sparse.merge merged1873 merged1875 := by decide +kernel

theorem mergedZero1876 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1876 x = 0 := by
  rw [mergeCheck1876, Integer.Sparse.eval_merge]
  rw [mergedZero1873 x h, mergedZero1875 x h]
  simp only [add_zero]

theorem mergeCheck1877 : merged1877 = Integer.Sparse.merge merged1872 merged1876 := by decide +kernel

theorem mergedZero1877 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1877 x = 0 := by
  rw [mergeCheck1877, Integer.Sparse.eval_merge]
  rw [mergedZero1872 x h, mergedZero1876 x h]
  simp only [add_zero]

theorem mergeCheck1878 : merged1878 = Integer.Sparse.merge (Integer.Sparse.scale (-14517695406509909913600) (sourceRows 1883)) (Integer.Sparse.scale (24359314843032777216000) (sourceRows 1884)) := by decide +kernel

theorem mergedZero1878 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1878 x = 0 := by
  rw [mergeCheck1878, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1879 : merged1879 = Integer.Sparse.merge (Integer.Sparse.scale (38135604618997320960000) (sourceRows 1886)) (Integer.Sparse.scale (55938618423812836454400) (sourceRows 1887)) := by decide +kernel

theorem mergedZero1879 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1879 x = 0 := by
  rw [mergeCheck1879, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1880 : merged1880 = Integer.Sparse.merge (Integer.Sparse.scale (-227933900151855206400) (sourceRows 1885)) merged1879 := by decide +kernel

theorem mergedZero1880 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1880 x = 0 := by
  rw [mergeCheck1880, Integer.Sparse.eval_merge]
  rw [mergedZero1879 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1881 : merged1881 = Integer.Sparse.merge merged1878 merged1880 := by decide +kernel

theorem mergedZero1881 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1881 x = 0 := by
  rw [mergeCheck1881, Integer.Sparse.eval_merge]
  rw [mergedZero1878 x h, mergedZero1880 x h]
  simp only [add_zero]

theorem mergeCheck1882 : merged1882 = Integer.Sparse.merge (Integer.Sparse.scale (22489684711592587776000) (sourceRows 1888)) (Integer.Sparse.scale (17353188653662665216000) (sourceRows 1889)) := by decide +kernel

theorem mergedZero1882 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1882 x = 0 := by
  rw [mergeCheck1882, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1883 : merged1883 = Integer.Sparse.merge (Integer.Sparse.scale (-32794955452720052121600) (sourceRows 1891)) (Integer.Sparse.scale (-15557617380127044096000) (sourceRows 1892)) := by decide +kernel

theorem mergedZero1883 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1883 x = 0 := by
  rw [mergeCheck1883, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1884 : merged1884 = Integer.Sparse.merge (Integer.Sparse.scale (5023829814312960000000) (sourceRows 1890)) merged1883 := by decide +kernel

theorem mergedZero1884 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1884 x = 0 := by
  rw [mergeCheck1884, Integer.Sparse.eval_merge]
  rw [mergedZero1883 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1885 : merged1885 = Integer.Sparse.merge merged1882 merged1884 := by decide +kernel

theorem mergedZero1885 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1885 x = 0 := by
  rw [mergeCheck1885, Integer.Sparse.eval_merge]
  rw [mergedZero1882 x h, mergedZero1884 x h]
  simp only [add_zero]

theorem mergeCheck1886 : merged1886 = Integer.Sparse.merge merged1881 merged1885 := by decide +kernel

theorem mergedZero1886 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1886 x = 0 := by
  rw [mergeCheck1886, Integer.Sparse.eval_merge]
  rw [mergedZero1881 x h, mergedZero1885 x h]
  simp only [add_zero]

theorem mergeCheck1887 : merged1887 = Integer.Sparse.merge merged1877 merged1886 := by decide +kernel

theorem mergedZero1887 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1887 x = 0 := by
  rw [mergeCheck1887, Integer.Sparse.eval_merge]
  rw [mergedZero1877 x h, mergedZero1886 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1888 : merged1888 = Integer.Sparse.merge merged1869 merged1887 := by decide +kernel

theorem mergedZero1888 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1888 x = 0 := by
  rw [mergeCheck1888, Integer.Sparse.eval_merge]
  rw [mergedZero1869 x h, mergedZero1887 x h]
  simp only [add_zero]

theorem mergeCheck1889 : merged1889 = Integer.Sparse.merge merged1851 merged1888 := by decide +kernel

theorem mergedZero1889 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1889 x = 0 := by
  rw [mergeCheck1889, Integer.Sparse.eval_merge]
  rw [mergedZero1851 x h, mergedZero1888 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1965 : merged1965 = Integer.Sparse.merge merged1889 merged1964 := by decide +kernel

theorem mergedZero1965_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1965 x = 0 := by
  rw [mergeCheck1965, Integer.Sparse.eval_merge]
  rw [mergedZero1889 x h, mergedZero1964_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1965_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1965_e_oai
