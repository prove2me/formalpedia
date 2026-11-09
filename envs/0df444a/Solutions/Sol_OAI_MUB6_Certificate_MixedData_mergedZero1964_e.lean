-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1964_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:23:22.232898+00:00
-- url     : https://prove2.me/submissions/93ae59f9-8ea1-4232-93e8-171e6c6d8864

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E064
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1890 : merged1890 = Integer.Sparse.merge (Integer.Sparse.scale (18660738856764933734400) (sourceRows 1893)) (Integer.Sparse.scale (-2711226786498478080000) (sourceRows 1894)) := by decide +kernel

theorem mergedZero1890 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1890 x = 0 := by
  rw [mergeCheck1890, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1891 : merged1891 = Integer.Sparse.merge (Integer.Sparse.scale (-8918978986518773760000) (sourceRows 1895)) (Integer.Sparse.scale (12289126261063680000000) (sourceRows 1896)) := by decide +kernel

theorem mergedZero1891 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1891 x = 0 := by
  rw [mergeCheck1891, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1892 : merged1892 = Integer.Sparse.merge merged1890 merged1891 := by decide +kernel

theorem mergedZero1892 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1892 x = 0 := by
  rw [mergeCheck1892, Integer.Sparse.eval_merge]
  rw [mergedZero1890 x h, mergedZero1891 x h]
  simp only [add_zero]

theorem mergeCheck1893 : merged1893 = Integer.Sparse.merge (Integer.Sparse.scale (33241284796606709760000) (sourceRows 1897)) (Integer.Sparse.scale (-29672525229029522380800) (sourceRows 1898)) := by decide +kernel

theorem mergedZero1893 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1893 x = 0 := by
  rw [mergeCheck1893, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1894 : merged1894 = Integer.Sparse.merge (Integer.Sparse.scale (38156714087940558028800) (sourceRows 1900)) (Integer.Sparse.scale (105994668503015121715200) (sourceRows 1901)) := by decide +kernel

theorem mergedZero1894 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1894 x = 0 := by
  rw [mergeCheck1894, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1895 : merged1895 = Integer.Sparse.merge (Integer.Sparse.scale (9041040045215203737600) (sourceRows 1899)) merged1894 := by decide +kernel

theorem mergedZero1895 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1895 x = 0 := by
  rw [mergeCheck1895, Integer.Sparse.eval_merge]
  rw [mergedZero1894 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1896 : merged1896 = Integer.Sparse.merge merged1893 merged1895 := by decide +kernel

theorem mergedZero1896 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1896 x = 0 := by
  rw [mergeCheck1896, Integer.Sparse.eval_merge]
  rw [mergedZero1893 x h, mergedZero1895 x h]
  simp only [add_zero]

theorem mergeCheck1897 : merged1897 = Integer.Sparse.merge merged1892 merged1896 := by decide +kernel

theorem mergedZero1897 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1897 x = 0 := by
  rw [mergeCheck1897, Integer.Sparse.eval_merge]
  rw [mergedZero1892 x h, mergedZero1896 x h]
  simp only [add_zero]

theorem mergeCheck1898 : merged1898 = Integer.Sparse.merge (Integer.Sparse.scale (-105994668503015121715200) (sourceRows 1902)) (Integer.Sparse.scale (-280491251092665019545600) (sourceRows 1903)) := by decide +kernel

theorem mergedZero1898 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1898 x = 0 := by
  rw [mergeCheck1898, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1899 : merged1899 = Integer.Sparse.merge (Integer.Sparse.scale (9376267261116672000) (sourceRows 1905)) (Integer.Sparse.scale (-34764097536000) (sourceRows 1906)) := by decide +kernel

theorem mergedZero1899 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1899 x = 0 := by
  rw [mergeCheck1899, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1900 : merged1900 = Integer.Sparse.merge (Integer.Sparse.scale (-357849578419200) (sourceRows 1904)) merged1899 := by decide +kernel

theorem mergedZero1900 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1900 x = 0 := by
  rw [mergeCheck1900, Integer.Sparse.eval_merge]
  rw [mergedZero1899 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1901 : merged1901 = Integer.Sparse.merge merged1898 merged1900 := by decide +kernel

theorem mergedZero1901 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1901 x = 0 := by
  rw [mergeCheck1901, Integer.Sparse.eval_merge]
  rw [mergedZero1898 x h, mergedZero1900 x h]
  simp only [add_zero]

theorem mergeCheck1902 : merged1902 = Integer.Sparse.merge (Integer.Sparse.scale (14045211640535040000) (sourceRows 1907)) (Integer.Sparse.scale (-359770650624000) (sourceRows 1908)) := by decide +kernel

theorem mergedZero1902 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1902 x = 0 := by
  rw [mergeCheck1902, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1903 : merged1903 = Integer.Sparse.merge (Integer.Sparse.scale (1721887938892800) (sourceRows 1910)) (Integer.Sparse.scale (18425234202195340800) (sourceRows 1911)) := by decide +kernel

theorem mergedZero1903 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1903 x = 0 := by
  rw [mergeCheck1903, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1904 : merged1904 = Integer.Sparse.merge (Integer.Sparse.scale (-14762797477147238400) (sourceRows 1909)) merged1903 := by decide +kernel

theorem mergedZero1904 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1904 x = 0 := by
  rw [mergeCheck1904, Integer.Sparse.eval_merge]
  rw [mergedZero1903 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1905 : merged1905 = Integer.Sparse.merge merged1902 merged1904 := by decide +kernel

theorem mergedZero1905 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1905 x = 0 := by
  rw [mergeCheck1905, Integer.Sparse.eval_merge]
  rw [mergedZero1902 x h, mergedZero1904 x h]
  simp only [add_zero]

theorem mergeCheck1906 : merged1906 = Integer.Sparse.merge merged1901 merged1905 := by decide +kernel

theorem mergedZero1906 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1906 x = 0 := by
  rw [mergeCheck1906, Integer.Sparse.eval_merge]
  rw [mergedZero1901 x h, mergedZero1905 x h]
  simp only [add_zero]

theorem mergeCheck1907 : merged1907 = Integer.Sparse.merge merged1897 merged1906 := by decide +kernel

theorem mergedZero1907 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1907 x = 0 := by
  rw [mergeCheck1907, Integer.Sparse.eval_merge]
  rw [mergedZero1897 x h, mergedZero1906 x h]
  simp only [add_zero]

theorem mergeCheck1908 : merged1908 = Integer.Sparse.merge (Integer.Sparse.scale (2183928565283684352000) (sourceRows 1912)) (Integer.Sparse.scale (2184861267190683648000) (sourceRows 1913)) := by decide +kernel

theorem mergedZero1908 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1908 x = 0 := by
  rw [mergeCheck1908, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1909 : merged1909 = Integer.Sparse.merge (Integer.Sparse.scale (-37328834188800) (sourceRows 1914)) (Integer.Sparse.scale (12763098726623078400) (sourceRows 1915)) := by decide +kernel

theorem mergedZero1909 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1909 x = 0 := by
  rw [mergeCheck1909, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1910 : merged1910 = Integer.Sparse.merge merged1908 merged1909 := by decide +kernel

theorem mergedZero1910 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1910 x = 0 := by
  rw [mergeCheck1910, Integer.Sparse.eval_merge]
  rw [mergedZero1908 x h, mergedZero1909 x h]
  simp only [add_zero]

theorem mergeCheck1911 : merged1911 = Integer.Sparse.merge (Integer.Sparse.scale (84550241664000) (sourceRows 1916)) (Integer.Sparse.scale (6360451911463104000) (sourceRows 1917)) := by decide +kernel

theorem mergedZero1911 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1911 x = 0 := by
  rw [mergeCheck1911, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1912 : merged1912 = Integer.Sparse.merge (Integer.Sparse.scale (134733551393364902092800) (sourceRows 1919)) (Integer.Sparse.scale (-47615228451600790579200) (sourceRows 1920)) := by decide +kernel

theorem mergedZero1912 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1912 x = 0 := by
  rw [mergeCheck1912, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1913 : merged1913 = Integer.Sparse.merge (Integer.Sparse.scale (-30817685606400) (sourceRows 1918)) merged1912 := by decide +kernel

theorem mergedZero1913 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1913 x = 0 := by
  rw [mergeCheck1913, Integer.Sparse.eval_merge]
  rw [mergedZero1912 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1914 : merged1914 = Integer.Sparse.merge merged1911 merged1913 := by decide +kernel

theorem mergedZero1914 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1914 x = 0 := by
  rw [mergeCheck1914, Integer.Sparse.eval_merge]
  rw [mergedZero1911 x h, mergedZero1913 x h]
  simp only [add_zero]

theorem mergeCheck1915 : merged1915 = Integer.Sparse.merge merged1910 merged1914 := by decide +kernel

theorem mergedZero1915 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1915 x = 0 := by
  rw [mergeCheck1915, Integer.Sparse.eval_merge]
  rw [mergedZero1910 x h, mergedZero1914 x h]
  simp only [add_zero]

theorem mergeCheck1916 : merged1916 = Integer.Sparse.merge (Integer.Sparse.scale (-60936435870695307417600) (sourceRows 1921)) (Integer.Sparse.scale (32476209071860937779200) (sourceRows 1922)) := by decide +kernel

theorem mergedZero1916 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1916 x = 0 := by
  rw [mergeCheck1916, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1917 : merged1917 = Integer.Sparse.merge (Integer.Sparse.scale (-11144540526937767936000) (sourceRows 1924)) (Integer.Sparse.scale (1032289234550784000) (sourceRows 1925)) := by decide +kernel

theorem mergedZero1917 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1917 x = 0 := by
  rw [mergeCheck1917, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1918 : merged1918 = Integer.Sparse.merge (Integer.Sparse.scale (7607687703146496000) (sourceRows 1923)) merged1917 := by decide +kernel

theorem mergedZero1918 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1918 x = 0 := by
  rw [mergeCheck1918, Integer.Sparse.eval_merge]
  rw [mergedZero1917 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1919 : merged1919 = Integer.Sparse.merge merged1916 merged1918 := by decide +kernel

theorem mergedZero1919 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1919 x = 0 := by
  rw [mergeCheck1919, Integer.Sparse.eval_merge]
  rw [mergedZero1916 x h, mergedZero1918 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1920 : merged1920 = Integer.Sparse.merge (Integer.Sparse.scale (-11144394464241346560000) (sourceRows 1926)) (Integer.Sparse.scale (270085009626100411545600) (sourceRows 1927)) := by decide +kernel

theorem mergedZero1920 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1920 x = 0 := by
  rw [mergeCheck1920, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1921 : merged1921 = Integer.Sparse.merge (Integer.Sparse.scale (28014733210304087654400) (sourceRows 1929)) (Integer.Sparse.scale (-11796193314151464960000) (sourceRows 1930)) := by decide +kernel

theorem mergedZero1921 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1921 x = 0 := by
  rw [mergeCheck1921, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1922 : merged1922 = Integer.Sparse.merge (Integer.Sparse.scale (-4433171053215744000000) (sourceRows 1928)) merged1921 := by decide +kernel

theorem mergedZero1922 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1922 x = 0 := by
  rw [mergeCheck1922, Integer.Sparse.eval_merge]
  rw [mergedZero1921 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1923 : merged1923 = Integer.Sparse.merge merged1920 merged1922 := by decide +kernel

theorem mergedZero1923 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1923 x = 0 := by
  rw [mergeCheck1923, Integer.Sparse.eval_merge]
  rw [mergedZero1920 x h, mergedZero1922 x h]
  simp only [add_zero]

theorem mergeCheck1924 : merged1924 = Integer.Sparse.merge merged1919 merged1923 := by decide +kernel

theorem mergedZero1924 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1924 x = 0 := by
  rw [mergeCheck1924, Integer.Sparse.eval_merge]
  rw [mergedZero1919 x h, mergedZero1923 x h]
  simp only [add_zero]

theorem mergeCheck1925 : merged1925 = Integer.Sparse.merge merged1915 merged1924 := by decide +kernel

theorem mergedZero1925 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1925 x = 0 := by
  rw [mergeCheck1925, Integer.Sparse.eval_merge]
  rw [mergedZero1915 x h, mergedZero1924 x h]
  simp only [add_zero]

theorem mergeCheck1926 : merged1926 = Integer.Sparse.merge merged1907 merged1925 := by decide +kernel

theorem mergedZero1926 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1926 x = 0 := by
  rw [mergeCheck1926, Integer.Sparse.eval_merge]
  rw [mergedZero1907 x h, mergedZero1925 x h]
  simp only [add_zero]

theorem mergeCheck1927 : merged1927 = Integer.Sparse.merge (Integer.Sparse.scale (7011835949075005440000) (sourceRows 1931)) (Integer.Sparse.scale (4035982506785832960000) (sourceRows 1932)) := by decide +kernel

theorem mergedZero1927 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1927 x = 0 := by
  rw [mergeCheck1927, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1928 : merged1928 = Integer.Sparse.merge (Integer.Sparse.scale (-45316965335040000) (sourceRows 1933)) (Integer.Sparse.scale (-2050187137963130880000) (sourceRows 1934)) := by decide +kernel

theorem mergedZero1928 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1928 x = 0 := by
  rw [mergeCheck1928, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1929 : merged1929 = Integer.Sparse.merge merged1927 merged1928 := by decide +kernel

theorem mergedZero1929 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1929 x = 0 := by
  rw [mergeCheck1929, Integer.Sparse.eval_merge]
  rw [mergedZero1927 x h, mergedZero1928 x h]
  simp only [add_zero]

theorem mergeCheck1930 : merged1930 = Integer.Sparse.merge (Integer.Sparse.scale (-12071546075759837184000) (sourceRows 1935)) (Integer.Sparse.scale (-12072214716507445248000) (sourceRows 1936)) := by decide +kernel

theorem mergedZero1930 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1930 x = 0 := by
  rw [mergeCheck1930, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1931 : merged1931 = Integer.Sparse.merge (Integer.Sparse.scale (6630943594603603968000) (sourceRows 1938)) (Integer.Sparse.scale (416003421044736000000) (sourceRows 1939)) := by decide +kernel

theorem mergedZero1931 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1931 x = 0 := by
  rw [mergeCheck1931, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1932 : merged1932 = Integer.Sparse.merge (Integer.Sparse.scale (6630899195785052160000) (sourceRows 1937)) merged1931 := by decide +kernel

theorem mergedZero1932 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1932 x = 0 := by
  rw [mergeCheck1932, Integer.Sparse.eval_merge]
  rw [mergedZero1931 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1933 : merged1933 = Integer.Sparse.merge merged1930 merged1932 := by decide +kernel

theorem mergedZero1933 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1933 x = 0 := by
  rw [mergeCheck1933, Integer.Sparse.eval_merge]
  rw [mergedZero1930 x h, mergedZero1932 x h]
  simp only [add_zero]

theorem mergeCheck1934 : merged1934 = Integer.Sparse.merge merged1929 merged1933 := by decide +kernel

theorem mergedZero1934 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1934 x = 0 := by
  rw [mergeCheck1934, Integer.Sparse.eval_merge]
  rw [mergedZero1929 x h, mergedZero1933 x h]
  simp only [add_zero]

theorem mergeCheck1935 : merged1935 = Integer.Sparse.merge (Integer.Sparse.scale (67975448002560000) (sourceRows 1940)) (Integer.Sparse.scale (-1071367865869271040000) (sourceRows 1941)) := by decide +kernel

theorem mergedZero1935 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1935 x = 0 := by
  rw [mergeCheck1935, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1936 : merged1936 = Integer.Sparse.merge (Integer.Sparse.scale (-9579097704557445120000) (sourceRows 1943)) (Integer.Sparse.scale (-118320732633600) (sourceRows 1944)) := by decide +kernel

theorem mergedZero1936 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1936 x = 0 := by
  rw [mergeCheck1936, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1937 : merged1937 = Integer.Sparse.merge (Integer.Sparse.scale (-1071499232730415104000) (sourceRows 1942)) merged1936 := by decide +kernel

theorem mergedZero1937 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1937 x = 0 := by
  rw [mergeCheck1937, Integer.Sparse.eval_merge]
  rw [mergedZero1936 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1938 : merged1938 = Integer.Sparse.merge merged1935 merged1937 := by decide +kernel

theorem mergedZero1938 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1938 x = 0 := by
  rw [mergeCheck1938, Integer.Sparse.eval_merge]
  rw [mergedZero1935 x h, mergedZero1937 x h]
  simp only [add_zero]

theorem mergeCheck1939 : merged1939 = Integer.Sparse.merge (Integer.Sparse.scale (1261600520887074816000) (sourceRows 1945)) (Integer.Sparse.scale (1261472758598320128000) (sourceRows 1946)) := by decide +kernel

theorem mergedZero1939 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1939 x = 0 := by
  rw [mergeCheck1939, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1940 : merged1940 = Integer.Sparse.merge (Integer.Sparse.scale (389388921062400) (sourceRows 1948)) (Integer.Sparse.scale (1077530262490644480000) (sourceRows 1949)) := by decide +kernel

theorem mergedZero1940 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1940 x = 0 := by
  rw [mergeCheck1940, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1941 : merged1941 = Integer.Sparse.merge (Integer.Sparse.scale (60936435870695307417600) (sourceRows 1947)) merged1940 := by decide +kernel

theorem mergedZero1941 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1941 x = 0 := by
  rw [mergeCheck1941, Integer.Sparse.eval_merge]
  rw [mergedZero1940 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1942 : merged1942 = Integer.Sparse.merge merged1939 merged1941 := by decide +kernel

theorem mergedZero1942 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1942 x = 0 := by
  rw [mergeCheck1942, Integer.Sparse.eval_merge]
  rw [mergedZero1939 x h, mergedZero1941 x h]
  simp only [add_zero]

theorem mergeCheck1943 : merged1943 = Integer.Sparse.merge merged1938 merged1942 := by decide +kernel

theorem mergedZero1943 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1943 x = 0 := by
  rw [mergeCheck1943, Integer.Sparse.eval_merge]
  rw [mergedZero1938 x h, mergedZero1942 x h]
  simp only [add_zero]

theorem mergeCheck1944 : merged1944 = Integer.Sparse.merge merged1934 merged1943 := by decide +kernel

theorem mergedZero1944 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1944 x = 0 := by
  rw [mergeCheck1944, Integer.Sparse.eval_merge]
  rw [mergedZero1934 x h, mergedZero1943 x h]
  simp only [add_zero]

theorem mergeCheck1945 : merged1945 = Integer.Sparse.merge (Integer.Sparse.scale (1077398895629500416000) (sourceRows 1950)) (Integer.Sparse.scale (-129163021063585005772800) (sourceRows 1951)) := by decide +kernel

theorem mergedZero1945 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1945 x = 0 := by
  rw [mergeCheck1945, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1946 : merged1946 = Integer.Sparse.merge (Integer.Sparse.scale (-118320732633600) (sourceRows 1952)) (Integer.Sparse.scale (12944695177520676864000) (sourceRows 1953)) := by decide +kernel

theorem mergedZero1946 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1946 x = 0 := by
  rw [mergeCheck1946, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1947 : merged1947 = Integer.Sparse.merge merged1945 merged1946 := by decide +kernel

theorem mergedZero1947 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1947 x = 0 := by
  rw [mergeCheck1947, Integer.Sparse.eval_merge]
  rw [mergedZero1945 x h, mergedZero1946 x h]
  simp only [add_zero]

theorem mergeCheck1948 : merged1948 = Integer.Sparse.merge (Integer.Sparse.scale (12945578055377780736000) (sourceRows 1954)) (Integer.Sparse.scale (-92461733203840139059200) (sourceRows 1955)) := by decide +kernel

theorem mergedZero1948 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1948 x = 0 := by
  rw [mergeCheck1948, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1949 : merged1949 = Integer.Sparse.merge (Integer.Sparse.scale (871962864676227072000) (sourceRows 1957)) (Integer.Sparse.scale (-3797966589227532288000) (sourceRows 1958)) := by decide +kernel

theorem mergedZero1949 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1949 x = 0 := by
  rw [mergeCheck1949, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1950 : merged1950 = Integer.Sparse.merge (Integer.Sparse.scale (872021895715160064000) (sourceRows 1956)) merged1949 := by decide +kernel

theorem mergedZero1950 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1950 x = 0 := by
  rw [mergeCheck1950, Integer.Sparse.eval_merge]
  rw [mergedZero1949 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1951 : merged1951 = Integer.Sparse.merge merged1948 merged1950 := by decide +kernel

theorem mergedZero1951 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1951 x = 0 := by
  rw [mergeCheck1951, Integer.Sparse.eval_merge]
  rw [mergedZero1948 x h, mergedZero1950 x h]
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

theorem mergeCheck1952 : merged1952 = Integer.Sparse.merge merged1947 merged1951 := by decide +kernel

theorem mergedZero1952 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1952 x = 0 := by
  rw [mergeCheck1952, Integer.Sparse.eval_merge]
  rw [mergedZero1947 x h, mergedZero1951 x h]
  simp only [add_zero]

theorem mergeCheck1953 : merged1953 = Integer.Sparse.merge (Integer.Sparse.scale (-3798467059195017216000) (sourceRows 1959)) (Integer.Sparse.scale (-9074381281832337408000) (sourceRows 1960)) := by decide +kernel

theorem mergedZero1953 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1953 x = 0 := by
  rw [mergeCheck1953, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1954 : merged1954 = Integer.Sparse.merge (Integer.Sparse.scale (33614764187073869721600) (sourceRows 1962)) (Integer.Sparse.scale (-27049802976000) (sourceRows 1963)) := by decide +kernel

theorem mergedZero1954 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1954 x = 0 := by
  rw [mergeCheck1954, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1955 : merged1955 = Integer.Sparse.merge (Integer.Sparse.scale (-9074406441288609792000) (sourceRows 1961)) merged1954 := by decide +kernel

theorem mergedZero1955 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1955 x = 0 := by
  rw [mergeCheck1955, Integer.Sparse.eval_merge]
  rw [mergedZero1954 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1956 : merged1956 = Integer.Sparse.merge merged1953 merged1955 := by decide +kernel

theorem mergedZero1956 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1956 x = 0 := by
  rw [mergeCheck1956, Integer.Sparse.eval_merge]
  rw [mergedZero1953 x h, mergedZero1955 x h]
  simp only [add_zero]

theorem mergeCheck1957 : merged1957 = Integer.Sparse.merge (Integer.Sparse.scale (2625511718751384960) (sourceRows 1964)) (Integer.Sparse.scale (-2204178844784394240000) (sourceRows 1965)) := by decide +kernel

theorem mergedZero1957 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1957 x = 0 := by
  rw [mergeCheck1957, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1958 : merged1958 = Integer.Sparse.merge (Integer.Sparse.scale (-16254530038740220416000) (sourceRows 1967)) (Integer.Sparse.scale (-27049802976000) (sourceRows 1968)) := by decide +kernel

theorem mergedZero1958 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1958 x = 0 := by
  rw [mergeCheck1958, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1959 : merged1959 = Integer.Sparse.merge (Integer.Sparse.scale (-2204247331283558400000) (sourceRows 1966)) merged1958 := by decide +kernel

theorem mergedZero1959 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1959 x = 0 := by
  rw [mergeCheck1959, Integer.Sparse.eval_merge]
  rw [mergedZero1958 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1960 : merged1960 = Integer.Sparse.merge merged1957 merged1959 := by decide +kernel

theorem mergedZero1960 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1960 x = 0 := by
  rw [mergeCheck1960, Integer.Sparse.eval_merge]
  rw [mergedZero1957 x h, mergedZero1959 x h]
  simp only [add_zero]

theorem mergeCheck1961 : merged1961 = Integer.Sparse.merge merged1956 merged1960 := by decide +kernel

theorem mergedZero1961 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1961 x = 0 := by
  rw [mergeCheck1961, Integer.Sparse.eval_merge]
  rw [mergedZero1956 x h, mergedZero1960 x h]
  simp only [add_zero]

theorem mergeCheck1962 : merged1962 = Integer.Sparse.merge merged1952 merged1961 := by decide +kernel

theorem mergedZero1962 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1962 x = 0 := by
  rw [mergeCheck1962, Integer.Sparse.eval_merge]
  rw [mergedZero1952 x h, mergedZero1961 x h]
  simp only [add_zero]

theorem mergeCheck1963 : merged1963 = Integer.Sparse.merge merged1944 merged1962 := by decide +kernel

theorem mergedZero1963 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1963 x = 0 := by
  rw [mergeCheck1963, Integer.Sparse.eval_merge]
  rw [mergedZero1944 x h, mergedZero1962 x h]
  simp only [add_zero]

theorem mergeCheck1964 : merged1964 = Integer.Sparse.merge merged1926 merged1963 := by decide +kernel

theorem mergedZero1964_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1964 x = 0 := by
  rw [mergeCheck1964, Integer.Sparse.eval_merge]
  rw [mergedZero1926 x h, mergedZero1963 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1964_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1964_e_oai
