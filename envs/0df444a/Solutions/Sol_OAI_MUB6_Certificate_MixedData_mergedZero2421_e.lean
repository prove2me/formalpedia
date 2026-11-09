-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero2421_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:25:48.221036+00:00
-- url     : https://prove2.me/submissions/43ed4436-04ce-4367-bec3-139525647993

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E063
import Definitions.Def_OAIQ106E183
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1965_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero2040_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero2419_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2041 : merged2041 = Integer.Sparse.merge (Integer.Sparse.scale (6364636425815851008000) (sourceRows 2045)) (Integer.Sparse.scale (-491643758592000000) (sourceRows 2046)) := by decide +kernel

theorem mergedZero2041 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2041 x = 0 := by
  rw [mergeCheck2041, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2042 : merged2042 = Integer.Sparse.merge (Integer.Sparse.scale (6364737782984641536000) (sourceRows 2047)) (Integer.Sparse.scale (62539370611200) (sourceRows 2048)) := by decide +kernel

theorem mergedZero2042 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2042 x = 0 := by
  rw [mergeCheck2042, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2043 : merged2043 = Integer.Sparse.merge merged2041 merged2042 := by decide +kernel

theorem mergedZero2043 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2043 x = 0 := by
  rw [mergeCheck2043, Integer.Sparse.eval_merge]
  rw [mergedZero2041 x h, mergedZero2042 x h]
  simp only [add_zero]

theorem mergeCheck2044 : merged2044 = Integer.Sparse.merge (Integer.Sparse.scale (-10577375156153998080) (sourceRows 2049)) (Integer.Sparse.scale (62148675778560) (sourceRows 2050)) := by decide +kernel

theorem mergedZero2044 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2044 x = 0 := by
  rw [mergeCheck2044, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2045 : merged2045 = Integer.Sparse.merge (Integer.Sparse.scale (-3550182978878355456000) (sourceRows 2052)) (Integer.Sparse.scale (2685717250429667328000) (sourceRows 2053)) := by decide +kernel

theorem mergedZero2045 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2045 x = 0 := by
  rw [mergeCheck2045, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2046 : merged2046 = Integer.Sparse.merge (Integer.Sparse.scale (-3550343469667319808000) (sourceRows 2051)) merged2045 := by decide +kernel

theorem mergedZero2046 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2046 x = 0 := by
  rw [mergeCheck2046, Integer.Sparse.eval_merge]
  rw [mergedZero2045 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2047 : merged2047 = Integer.Sparse.merge merged2044 merged2046 := by decide +kernel

theorem mergedZero2047 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2047 x = 0 := by
  rw [mergeCheck2047, Integer.Sparse.eval_merge]
  rw [mergedZero2044 x h, mergedZero2046 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2048 : merged2048 = Integer.Sparse.merge merged2043 merged2047 := by decide +kernel

theorem mergedZero2048 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2048 x = 0 := by
  rw [mergeCheck2048, Integer.Sparse.eval_merge]
  rw [mergedZero2043 x h, mergedZero2047 x h]
  simp only [add_zero]

theorem mergeCheck2049 : merged2049 = Integer.Sparse.merge (Integer.Sparse.scale (-87250000174453392998400) (sourceRows 2054)) (Integer.Sparse.scale (87250000174453392998400) (sourceRows 2055)) := by decide +kernel

theorem mergedZero2049 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2049 x = 0 := by
  rw [mergeCheck2049, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2050 : merged2050 = Integer.Sparse.merge (Integer.Sparse.scale (6859712377813865472000) (sourceRows 2057)) (Integer.Sparse.scale (-189858001592770560) (sourceRows 2058)) := by decide +kernel

theorem mergedZero2050 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2050 x = 0 := by
  rw [mergeCheck2050, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2051 : merged2051 = Integer.Sparse.merge (Integer.Sparse.scale (6859573290976250880000) (sourceRows 2056)) merged2050 := by decide +kernel

theorem mergedZero2051 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2051 x = 0 := by
  rw [mergeCheck2051, Integer.Sparse.eval_merge]
  rw [mergedZero2050 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2052 : merged2052 = Integer.Sparse.merge merged2049 merged2051 := by decide +kernel

theorem mergedZero2052 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2052 x = 0 := by
  rw [mergeCheck2052, Integer.Sparse.eval_merge]
  rw [mergedZero2049 x h, mergedZero2051 x h]
  simp only [add_zero]

theorem mergeCheck2053 : merged2053 = Integer.Sparse.merge (Integer.Sparse.scale (-15074183980800) (sourceRows 2059)) (Integer.Sparse.scale (-916490284416000) (sourceRows 2060)) := by decide +kernel

theorem mergedZero2053 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2053 x = 0 := by
  rw [mergeCheck2053, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2054 : merged2054 = Integer.Sparse.merge (Integer.Sparse.scale (37770691392000) (sourceRows 2062)) (Integer.Sparse.scale (-3956030668800) (sourceRows 2063)) := by decide +kernel

theorem mergedZero2054 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2054 x = 0 := by
  rw [mergeCheck2054, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2055 : merged2055 = Integer.Sparse.merge (Integer.Sparse.scale (-142909691904000) (sourceRows 2061)) merged2054 := by decide +kernel

theorem mergedZero2055 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2055 x = 0 := by
  rw [mergeCheck2055, Integer.Sparse.eval_merge]
  rw [mergedZero2054 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2056 : merged2056 = Integer.Sparse.merge merged2053 merged2055 := by decide +kernel

theorem mergedZero2056 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2056 x = 0 := by
  rw [mergeCheck2056, Integer.Sparse.eval_merge]
  rw [mergedZero2053 x h, mergedZero2055 x h]
  simp only [add_zero]

theorem mergeCheck2057 : merged2057 = Integer.Sparse.merge merged2052 merged2056 := by decide +kernel

theorem mergedZero2057 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2057 x = 0 := by
  rw [mergeCheck2057, Integer.Sparse.eval_merge]
  rw [mergedZero2052 x h, mergedZero2056 x h]
  simp only [add_zero]

theorem mergeCheck2058 : merged2058 = Integer.Sparse.merge merged2048 merged2057 := by decide +kernel

theorem mergedZero2058 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2058 x = 0 := by
  rw [mergeCheck2058, Integer.Sparse.eval_merge]
  rw [mergedZero2048 x h, mergedZero2057 x h]
  simp only [add_zero]

theorem mergeCheck2059 : merged2059 = Integer.Sparse.merge (Integer.Sparse.scale (-8303621836873531392000) (sourceRows 2064)) (Integer.Sparse.scale (-8303619124257859584000) (sourceRows 2065)) := by decide +kernel

theorem mergedZero2059 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2059 x = 0 := by
  rw [mergeCheck2059, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2060 : merged2060 = Integer.Sparse.merge (Integer.Sparse.scale (90356062809600) (sourceRows 2066)) (Integer.Sparse.scale (-2018701969923244032000) (sourceRows 2067)) := by decide +kernel

theorem mergedZero2060 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2060 x = 0 := by
  rw [mergeCheck2060, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2061 : merged2061 = Integer.Sparse.merge merged2059 merged2060 := by decide +kernel

theorem mergedZero2061 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2061 x = 0 := by
  rw [mergeCheck2061, Integer.Sparse.eval_merge]
  rw [mergedZero2059 x h, mergedZero2060 x h]
  simp only [add_zero]

theorem mergeCheck2062 : merged2062 = Integer.Sparse.merge (Integer.Sparse.scale (-2018705574495633408000) (sourceRows 2068)) (Integer.Sparse.scale (-9770356551311032320000) (sourceRows 2069)) := by decide +kernel

theorem mergedZero2062 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2062 x = 0 := by
  rw [mergeCheck2062, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2063 : merged2063 = Integer.Sparse.merge (Integer.Sparse.scale (1486105768226193408000) (sourceRows 2071)) (Integer.Sparse.scale (1486237135087337472000) (sourceRows 2072)) := by decide +kernel

theorem mergedZero2063 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2063 x = 0 := by
  rw [mergeCheck2063, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2064 : merged2064 = Integer.Sparse.merge (Integer.Sparse.scale (-9770222471834216448000) (sourceRows 2070)) merged2063 := by decide +kernel

theorem mergedZero2064 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2064 x = 0 := by
  rw [mergeCheck2064, Integer.Sparse.eval_merge]
  rw [mergedZero2063 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2065 : merged2065 = Integer.Sparse.merge merged2062 merged2064 := by decide +kernel

theorem mergedZero2065 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2065 x = 0 := by
  rw [mergeCheck2065, Integer.Sparse.eval_merge]
  rw [mergedZero2062 x h, mergedZero2064 x h]
  simp only [add_zero]

theorem mergeCheck2066 : merged2066 = Integer.Sparse.merge merged2061 merged2065 := by decide +kernel

theorem mergedZero2066 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2066 x = 0 := by
  rw [mergeCheck2066, Integer.Sparse.eval_merge]
  rw [mergedZero2061 x h, mergedZero2065 x h]
  simp only [add_zero]

theorem mergeCheck2067 : merged2067 = Integer.Sparse.merge (Integer.Sparse.scale (8244053715484016640000) (sourceRows 2073)) (Integer.Sparse.scale (8244051002868344832000) (sourceRows 2074)) := by decide +kernel

theorem mergedZero2067 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2067 x = 0 := by
  rw [mergeCheck2067, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2068 : merged2068 = Integer.Sparse.merge (Integer.Sparse.scale (794279074176000) (sourceRows 2076)) (Integer.Sparse.scale (-12305575296000) (sourceRows 2077)) := by decide +kernel

theorem mergedZero2068 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2068 x = 0 := by
  rw [mergeCheck2068, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2069 : merged2069 = Integer.Sparse.merge (Integer.Sparse.scale (-229546982246400) (sourceRows 2075)) merged2068 := by decide +kernel

theorem mergedZero2069 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2069 x = 0 := by
  rw [mergeCheck2069, Integer.Sparse.eval_merge]
  rw [mergedZero2068 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2070 : merged2070 = Integer.Sparse.merge merged2067 merged2069 := by decide +kernel

theorem mergedZero2070 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2070 x = 0 := by
  rw [mergeCheck2070, Integer.Sparse.eval_merge]
  rw [mergedZero2067 x h, mergedZero2069 x h]
  simp only [add_zero]

theorem mergeCheck2071 : merged2071 = Integer.Sparse.merge (Integer.Sparse.scale (-520707015170850816000) (sourceRows 2078)) (Integer.Sparse.scale (-520969748893138944000) (sourceRows 2079)) := by decide +kernel

theorem mergedZero2071 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2071 x = 0 := by
  rw [mergeCheck2071, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2072 : merged2072 = Integer.Sparse.merge (Integer.Sparse.scale (-1794097207692066816000) (sourceRows 2081)) (Integer.Sparse.scale (2809602793205268480000) (sourceRows 2082)) := by decide +kernel

theorem mergedZero2072 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2072 x = 0 := by
  rw [mergeCheck2072, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2073 : merged2073 = Integer.Sparse.merge (Integer.Sparse.scale (-1793757588297744384000) (sourceRows 2080)) merged2072 := by decide +kernel

theorem mergedZero2073 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2073 x = 0 := by
  rw [mergeCheck2073, Integer.Sparse.eval_merge]
  rw [mergedZero2072 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2074 : merged2074 = Integer.Sparse.merge merged2071 merged2073 := by decide +kernel

theorem mergedZero2074 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2074 x = 0 := by
  rw [mergeCheck2074, Integer.Sparse.eval_merge]
  rw [mergedZero2071 x h, mergedZero2073 x h]
  simp only [add_zero]

theorem mergeCheck2075 : merged2075 = Integer.Sparse.merge merged2070 merged2074 := by decide +kernel

theorem mergedZero2075 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2075 x = 0 := by
  rw [mergeCheck2075, Integer.Sparse.eval_merge]
  rw [mergedZero2070 x h, mergedZero2074 x h]
  simp only [add_zero]

theorem mergeCheck2076 : merged2076 = Integer.Sparse.merge merged2066 merged2075 := by decide +kernel

theorem mergedZero2076 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2076 x = 0 := by
  rw [mergeCheck2076, Integer.Sparse.eval_merge]
  rw [mergedZero2066 x h, mergedZero2075 x h]
  simp only [add_zero]

theorem mergeCheck2077 : merged2077 = Integer.Sparse.merge merged2058 merged2076 := by decide +kernel

theorem mergedZero2077 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2077 x = 0 := by
  rw [mergeCheck2077, Integer.Sparse.eval_merge]
  rw [mergedZero2058 x h, mergedZero2076 x h]
  simp only [add_zero]

theorem mergeCheck2078 : merged2078 = Integer.Sparse.merge (Integer.Sparse.scale (2809541533377116160000) (sourceRows 2083)) (Integer.Sparse.scale (4793685891068067840000) (sourceRows 2084)) := by decide +kernel

theorem mergedZero2078 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2078 x = 0 := by
  rw [mergeCheck2078, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2079 : merged2079 = Integer.Sparse.merge (Integer.Sparse.scale (4793788134001391616000) (sourceRows 2085)) (Integer.Sparse.scale (6217009671966621696000) (sourceRows 2086)) := by decide +kernel

theorem mergedZero2079 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2079 x = 0 := by
  rw [mergeCheck2079, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2080 : merged2080 = Integer.Sparse.merge merged2078 merged2079 := by decide +kernel

theorem mergedZero2080 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2080 x = 0 := by
  rw [mergeCheck2080, Integer.Sparse.eval_merge]
  rw [mergedZero2078 x h, mergedZero2079 x h]
  simp only [add_zero]

theorem mergeCheck2081 : merged2081 = Integer.Sparse.merge (Integer.Sparse.scale (6217031189133047808000) (sourceRows 2087)) (Integer.Sparse.scale (16933983132052094976000) (sourceRows 2088)) := by decide +kernel

theorem mergedZero2081 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2081 x = 0 := by
  rw [mergeCheck2081, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2082 : merged2082 = Integer.Sparse.merge (Integer.Sparse.scale (-10161184136862302208000) (sourceRows 2090)) (Integer.Sparse.scale (-10161163860139321344000) (sourceRows 2091)) := by decide +kernel

theorem mergedZero2082 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2082 x = 0 := by
  rw [mergeCheck2082, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2083 : merged2083 = Integer.Sparse.merge (Integer.Sparse.scale (16934109073681895424000) (sourceRows 2089)) merged2082 := by decide +kernel

theorem mergedZero2083 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2083 x = 0 := by
  rw [mergeCheck2083, Integer.Sparse.eval_merge]
  rw [mergedZero2082 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2084 : merged2084 = Integer.Sparse.merge merged2081 merged2083 := by decide +kernel

theorem mergedZero2084 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2084 x = 0 := by
  rw [mergeCheck2084, Integer.Sparse.eval_merge]
  rw [mergedZero2081 x h, mergedZero2083 x h]
  simp only [add_zero]

theorem mergeCheck2085 : merged2085 = Integer.Sparse.merge merged2080 merged2084 := by decide +kernel

theorem mergedZero2085 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2085 x = 0 := by
  rw [mergeCheck2085, Integer.Sparse.eval_merge]
  rw [mergedZero2080 x h, mergedZero2084 x h]
  simp only [add_zero]

theorem mergeCheck2086 : merged2086 = Integer.Sparse.merge (Integer.Sparse.scale (-392822798764032000) (sourceRows 2092)) (Integer.Sparse.scale (2426647588485120000) (sourceRows 2093)) := by decide +kernel

theorem mergedZero2086 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2086 x = 0 := by
  rw [mergeCheck2086, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2087 : merged2087 = Integer.Sparse.merge (Integer.Sparse.scale (-3786592309602859008000) (sourceRows 2095)) (Integer.Sparse.scale (-1171014574012416000) (sourceRows 2096)) := by decide +kernel

theorem mergedZero2087 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2087 x = 0 := by
  rw [mergeCheck2087, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2088 : merged2088 = Integer.Sparse.merge (Integer.Sparse.scale (-3786555279556804608000) (sourceRows 2094)) merged2087 := by decide +kernel

theorem mergedZero2088 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2088 x = 0 := by
  rw [mergeCheck2088, Integer.Sparse.eval_merge]
  rw [mergedZero2087 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2089 : merged2089 = Integer.Sparse.merge merged2086 merged2088 := by decide +kernel

theorem mergedZero2089 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2089 x = 0 := by
  rw [mergeCheck2089, Integer.Sparse.eval_merge]
  rw [mergedZero2086 x h, mergedZero2088 x h]
  simp only [add_zero]

theorem mergeCheck2090 : merged2090 = Integer.Sparse.merge (Integer.Sparse.scale (-1171014574012416000) (sourceRows 2097)) (Integer.Sparse.scale (441387625703915520) (sourceRows 2098)) := by decide +kernel

theorem mergedZero2090 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2090 x = 0 := by
  rw [mergeCheck2090, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2091 : merged2091 = Integer.Sparse.merge (Integer.Sparse.scale (946634569699295232000) (sourceRows 2100)) (Integer.Sparse.scale (946627287878651904000) (sourceRows 2101)) := by decide +kernel

theorem mergedZero2091 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2091 x = 0 := by
  rw [mergeCheck2091, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2092 : merged2092 = Integer.Sparse.merge (Integer.Sparse.scale (90356062809600) (sourceRows 2099)) merged2091 := by decide +kernel

theorem mergedZero2092 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2092 x = 0 := by
  rw [mergeCheck2092, Integer.Sparse.eval_merge]
  rw [mergedZero2091 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2093 : merged2093 = Integer.Sparse.merge merged2090 merged2092 := by decide +kernel

theorem mergedZero2093 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2093 x = 0 := by
  rw [mergeCheck2093, Integer.Sparse.eval_merge]
  rw [mergedZero2090 x h, mergedZero2092 x h]
  simp only [add_zero]

theorem mergeCheck2094 : merged2094 = Integer.Sparse.merge merged2089 merged2093 := by decide +kernel

theorem mergedZero2094 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2094 x = 0 := by
  rw [mergeCheck2094, Integer.Sparse.eval_merge]
  rw [mergedZero2089 x h, mergedZero2093 x h]
  simp only [add_zero]

theorem mergeCheck2095 : merged2095 = Integer.Sparse.merge merged2085 merged2094 := by decide +kernel

theorem mergedZero2095 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2095 x = 0 := by
  rw [mergeCheck2095, Integer.Sparse.eval_merge]
  rw [mergedZero2085 x h, mergedZero2094 x h]
  simp only [add_zero]

theorem mergeCheck2096 : merged2096 = Integer.Sparse.merge (Integer.Sparse.scale (-18889838150400) (sourceRows 2102)) (Integer.Sparse.scale (1298383248027156480000) (sourceRows 2103)) := by decide +kernel

theorem mergedZero2096 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2096 x = 0 := by
  rw [mergeCheck2096, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2097 : merged2097 = Integer.Sparse.merge (Integer.Sparse.scale (1298352997215848448000) (sourceRows 2104)) (Integer.Sparse.scale (-224909431488000) (sourceRows 2105)) := by decide +kernel

theorem mergedZero2097 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2097 x = 0 := by
  rw [mergeCheck2097, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2098 : merged2098 = Integer.Sparse.merge merged2096 merged2097 := by decide +kernel

theorem mergedZero2098 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2098 x = 0 := by
  rw [mergeCheck2098, Integer.Sparse.eval_merge]
  rw [mergedZero2096 x h, mergedZero2097 x h]
  simp only [add_zero]

theorem mergeCheck2099 : merged2099 = Integer.Sparse.merge (Integer.Sparse.scale (-157640445736058880) (sourceRows 2106)) (Integer.Sparse.scale (66966190905600) (sourceRows 2107)) := by decide +kernel

theorem mergedZero2099 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2099 x = 0 := by
  rw [mergeCheck2099, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2100 : merged2100 = Integer.Sparse.merge (Integer.Sparse.scale (-8150314783600410624000) (sourceRows 2109)) (Integer.Sparse.scale (-8150377754415310848000) (sourceRows 2110)) := by decide +kernel

theorem mergedZero2100 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2100 x = 0 := by
  rw [mergeCheck2100, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2101 : merged2101 = Integer.Sparse.merge (Integer.Sparse.scale (-164212746163200) (sourceRows 2108)) merged2100 := by decide +kernel

theorem mergedZero2101 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2101 x = 0 := by
  rw [mergeCheck2101, Integer.Sparse.eval_merge]
  rw [mergedZero2100 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2102 : merged2102 = Integer.Sparse.merge merged2099 merged2101 := by decide +kernel

theorem mergedZero2102 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2102 x = 0 := by
  rw [mergeCheck2102, Integer.Sparse.eval_merge]
  rw [mergedZero2099 x h, mergedZero2101 x h]
  simp only [add_zero]

theorem mergeCheck2103 : merged2103 = Integer.Sparse.merge merged2098 merged2102 := by decide +kernel

theorem mergedZero2103 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2103 x = 0 := by
  rw [mergeCheck2103, Integer.Sparse.eval_merge]
  rw [mergedZero2098 x h, mergedZero2102 x h]
  simp only [add_zero]

theorem mergeCheck2104 : merged2104 = Integer.Sparse.merge (Integer.Sparse.scale (-125764812055572480) (sourceRows 2111)) (Integer.Sparse.scale (-1776029068800000) (sourceRows 2112)) := by decide +kernel

theorem mergedZero2104 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2104 x = 0 := by
  rw [mergeCheck2104, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2105 : merged2105 = Integer.Sparse.merge (Integer.Sparse.scale (-34278315982848000) (sourceRows 2114)) (Integer.Sparse.scale (-99968954222592000) (sourceRows 2115)) := by decide +kernel

theorem mergedZero2105 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2105 x = 0 := by
  rw [mergeCheck2105, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2106 : merged2106 = Integer.Sparse.merge (Integer.Sparse.scale (-28396975832064000) (sourceRows 2113)) merged2105 := by decide +kernel

theorem mergedZero2106 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2106 x = 0 := by
  rw [mergeCheck2106, Integer.Sparse.eval_merge]
  rw [mergedZero2105 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2107 : merged2107 = Integer.Sparse.merge merged2104 merged2106 := by decide +kernel

theorem mergedZero2107 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2107 x = 0 := by
  rw [mergeCheck2107, Integer.Sparse.eval_merge]
  rw [mergedZero2104 x h, mergedZero2106 x h]
  simp only [add_zero]

theorem mergeCheck2108 : merged2108 = Integer.Sparse.merge (Integer.Sparse.scale (-113587903328256000) (sourceRows 2116)) (Integer.Sparse.scale (-7336529593344000) (sourceRows 2117)) := by decide +kernel

theorem mergedZero2108 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2108 x = 0 := by
  rw [mergeCheck2108, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2109 : merged2109 = Integer.Sparse.merge (Integer.Sparse.scale (-233155983126528000) (sourceRows 2119)) (Integer.Sparse.scale (340763709984768000) (sourceRows 2120)) := by decide +kernel

theorem mergedZero2109 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2109 x = 0 := by
  rw [mergeCheck2109, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2110 : merged2110 = Integer.Sparse.merge (Integer.Sparse.scale (-83526781879296000) (sourceRows 2118)) merged2109 := by decide +kernel

theorem mergedZero2110 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2110 x = 0 := by
  rw [mergeCheck2110, Integer.Sparse.eval_merge]
  rw [mergedZero2109 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2111 : merged2111 = Integer.Sparse.merge merged2108 merged2110 := by decide +kernel

theorem mergedZero2111 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2111 x = 0 := by
  rw [mergeCheck2111, Integer.Sparse.eval_merge]
  rw [mergedZero2108 x h, mergedZero2110 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2112 : merged2112 = Integer.Sparse.merge merged2107 merged2111 := by decide +kernel

theorem mergedZero2112 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2112 x = 0 := by
  rw [mergeCheck2112, Integer.Sparse.eval_merge]
  rw [mergedZero2107 x h, mergedZero2111 x h]
  simp only [add_zero]

theorem mergeCheck2113 : merged2113 = Integer.Sparse.merge merged2103 merged2112 := by decide +kernel

theorem mergedZero2113 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2113 x = 0 := by
  rw [mergeCheck2113, Integer.Sparse.eval_merge]
  rw [mergedZero2103 x h, mergedZero2112 x h]
  simp only [add_zero]

theorem mergeCheck2114 : merged2114 = Integer.Sparse.merge merged2095 merged2113 := by decide +kernel

theorem mergedZero2114 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2114 x = 0 := by
  rw [mergeCheck2114, Integer.Sparse.eval_merge]
  rw [mergedZero2095 x h, mergedZero2113 x h]
  simp only [add_zero]

theorem mergeCheck2115 : merged2115 = Integer.Sparse.merge merged2077 merged2114 := by decide +kernel

theorem mergedZero2115 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2115 x = 0 := by
  rw [mergeCheck2115, Integer.Sparse.eval_merge]
  rw [mergedZero2077 x h, mergedZero2114 x h]
  simp only [add_zero]

theorem mergeCheck2116 : merged2116 = Integer.Sparse.merge merged2040 merged2115 := by decide +kernel

theorem mergedZero2116 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2116 x = 0 := by
  rw [mergeCheck2116, Integer.Sparse.eval_merge]
  rw [mergedZero2040_e x h, mergedZero2115 x h]
  simp only [add_zero]

theorem mergeCheck2117 : merged2117 = Integer.Sparse.merge merged1965 merged2116 := by decide +kernel

theorem mergedZero2117 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2117 x = 0 := by
  rw [mergeCheck2117, Integer.Sparse.eval_merge]
  rw [mergedZero1965_e x h, mergedZero2116 x h]
  simp only [add_zero]

theorem mergeCheck2118 : merged2118 = Integer.Sparse.merge (Integer.Sparse.scale (227175806656512000) (sourceRows 2121)) (Integer.Sparse.scale (-66943030597632000) (sourceRows 2122)) := by decide +kernel

theorem mergedZero2118 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2118 x = 0 := by
  rw [mergeCheck2118, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2119 : merged2119 = Integer.Sparse.merge (Integer.Sparse.scale (-6096714946560000) (sourceRows 2123)) (Integer.Sparse.scale (367996811212800000) (sourceRows 2124)) := by decide +kernel

theorem mergedZero2119 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2119 x = 0 := by
  rw [mergeCheck2119, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2120 : merged2120 = Integer.Sparse.merge merged2118 merged2119 := by decide +kernel

theorem mergedZero2120 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2120 x = 0 := by
  rw [mergeCheck2120, Integer.Sparse.eval_merge]
  rw [mergedZero2118 x h, mergedZero2119 x h]
  simp only [add_zero]

theorem mergeCheck2121 : merged2121 = Integer.Sparse.merge (Integer.Sparse.scale (240706727460864000) (sourceRows 2125)) (Integer.Sparse.scale (-58816909541376000) (sourceRows 2126)) := by decide +kernel

theorem mergedZero2121 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2121 x = 0 := by
  rw [mergeCheck2121, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2122 : merged2122 = Integer.Sparse.merge (Integer.Sparse.scale (-115405531508736000) (sourceRows 2128)) (Integer.Sparse.scale (379137507065856000) (sourceRows 2129)) := by decide +kernel

theorem mergedZero2122 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2122 x = 0 := by
  rw [mergeCheck2122, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2123 : merged2123 = Integer.Sparse.merge (Integer.Sparse.scale (703487006208000000) (sourceRows 2127)) merged2122 := by decide +kernel

theorem mergedZero2123 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2123 x = 0 := by
  rw [mergeCheck2123, Integer.Sparse.eval_merge]
  rw [mergedZero2122 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2124 : merged2124 = Integer.Sparse.merge merged2121 merged2123 := by decide +kernel

theorem mergedZero2124 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2124 x = 0 := by
  rw [mergeCheck2124, Integer.Sparse.eval_merge]
  rw [mergedZero2121 x h, mergedZero2123 x h]
  simp only [add_zero]

theorem mergeCheck2125 : merged2125 = Integer.Sparse.merge merged2120 merged2124 := by decide +kernel

theorem mergedZero2125 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2125 x = 0 := by
  rw [mergeCheck2125, Integer.Sparse.eval_merge]
  rw [mergedZero2120 x h, mergedZero2124 x h]
  simp only [add_zero]

theorem mergeCheck2126 : merged2126 = Integer.Sparse.merge (Integer.Sparse.scale (411880398225408000) (sourceRows 2130)) (Integer.Sparse.scale (-1053960688263168000) (sourceRows 2131)) := by decide +kernel

theorem mergedZero2126 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2126 x = 0 := by
  rw [mergeCheck2126, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2127 : merged2127 = Integer.Sparse.merge (Integer.Sparse.scale (-93108317073408000) (sourceRows 2133)) (Integer.Sparse.scale (-92654390771712000) (sourceRows 2134)) := by decide +kernel

theorem mergedZero2127 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2127 x = 0 := by
  rw [mergeCheck2127, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2128 : merged2128 = Integer.Sparse.merge (Integer.Sparse.scale (-149640498717696000) (sourceRows 2132)) merged2127 := by decide +kernel

theorem mergedZero2128 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2128 x = 0 := by
  rw [mergeCheck2128, Integer.Sparse.eval_merge]
  rw [mergedZero2127 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2129 : merged2129 = Integer.Sparse.merge merged2126 merged2128 := by decide +kernel

theorem mergedZero2129 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2129 x = 0 := by
  rw [mergeCheck2129, Integer.Sparse.eval_merge]
  rw [mergedZero2126 x h, mergedZero2128 x h]
  simp only [add_zero]

theorem mergeCheck2130 : merged2130 = Integer.Sparse.merge (Integer.Sparse.scale (-298744832655360000) (sourceRows 2135)) (Integer.Sparse.scale (-13938131386368000) (sourceRows 2136)) := by decide +kernel

theorem mergedZero2130 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2130 x = 0 := by
  rw [mergeCheck2130, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2131 : merged2131 = Integer.Sparse.merge (Integer.Sparse.scale (-278742227484672000) (sourceRows 2138)) (Integer.Sparse.scale (-50627016824832000) (sourceRows 2139)) := by decide +kernel

theorem mergedZero2131 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2131 x = 0 := by
  rw [mergeCheck2131, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2132 : merged2132 = Integer.Sparse.merge (Integer.Sparse.scale (-76706333835264000) (sourceRows 2137)) merged2131 := by decide +kernel

theorem mergedZero2132 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2132 x = 0 := by
  rw [mergeCheck2132, Integer.Sparse.eval_merge]
  rw [mergedZero2131 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2133 : merged2133 = Integer.Sparse.merge merged2130 merged2132 := by decide +kernel

theorem mergedZero2133 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2133 x = 0 := by
  rw [mergeCheck2133, Integer.Sparse.eval_merge]
  rw [mergedZero2130 x h, mergedZero2132 x h]
  simp only [add_zero]

theorem mergeCheck2134 : merged2134 = Integer.Sparse.merge merged2129 merged2133 := by decide +kernel

theorem mergedZero2134 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2134 x = 0 := by
  rw [mergeCheck2134, Integer.Sparse.eval_merge]
  rw [mergedZero2129 x h, mergedZero2133 x h]
  simp only [add_zero]

theorem mergeCheck2135 : merged2135 = Integer.Sparse.merge merged2125 merged2134 := by decide +kernel

theorem mergedZero2135 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2135 x = 0 := by
  rw [mergeCheck2135, Integer.Sparse.eval_merge]
  rw [mergedZero2125 x h, mergedZero2134 x h]
  simp only [add_zero]

theorem mergeCheck2136 : merged2136 = Integer.Sparse.merge (Integer.Sparse.scale (-263617370505216000) (sourceRows 2140)) (Integer.Sparse.scale (-355360710684672000) (sourceRows 2141)) := by decide +kernel

theorem mergedZero2136 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2136 x = 0 := by
  rw [mergeCheck2136, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2137 : merged2137 = Integer.Sparse.merge (Integer.Sparse.scale (1022291129954304000) (sourceRows 2142)) (Integer.Sparse.scale (681527419969536000) (sourceRows 2143)) := by decide +kernel

theorem mergedZero2137 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2137 x = 0 := by
  rw [mergeCheck2137, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2138 : merged2138 = Integer.Sparse.merge merged2136 merged2137 := by decide +kernel

theorem mergedZero2138 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2138 x = 0 := by
  rw [mergeCheck2138, Integer.Sparse.eval_merge]
  rw [mergedZero2136 x h, mergedZero2137 x h]
  simp only [add_zero]

theorem mergeCheck2139 : merged2139 = Integer.Sparse.merge (Integer.Sparse.scale (849971074240512000) (sourceRows 2144)) (Integer.Sparse.scale (553504902709248000) (sourceRows 2145)) := by decide +kernel

theorem mergedZero2139 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2139 x = 0 := by
  rw [mergeCheck2139, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2140 : merged2140 = Integer.Sparse.merge (Integer.Sparse.scale (-9172318030848000) (sourceRows 2147)) (Integer.Sparse.scale (-56318731564032000) (sourceRows 2148)) := by decide +kernel

theorem mergedZero2140 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2140 x = 0 := by
  rw [mergeCheck2140, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2141 : merged2141 = Integer.Sparse.merge (Integer.Sparse.scale (1659561707446272000) (sourceRows 2146)) merged2140 := by decide +kernel

theorem mergedZero2141 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2141 x = 0 := by
  rw [mergeCheck2141, Integer.Sparse.eval_merge]
  rw [mergedZero2140 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2142 : merged2142 = Integer.Sparse.merge merged2139 merged2141 := by decide +kernel

theorem mergedZero2142 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2142 x = 0 := by
  rw [mergeCheck2142, Integer.Sparse.eval_merge]
  rw [mergedZero2139 x h, mergedZero2141 x h]
  simp only [add_zero]

theorem mergeCheck2143 : merged2143 = Integer.Sparse.merge merged2138 merged2142 := by decide +kernel

theorem mergedZero2143 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2143 x = 0 := by
  rw [mergeCheck2143, Integer.Sparse.eval_merge]
  rw [mergedZero2138 x h, mergedZero2142 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2144 : merged2144 = Integer.Sparse.merge (Integer.Sparse.scale (-137073201979392000) (sourceRows 2149)) (Integer.Sparse.scale (-280113725767680000) (sourceRows 2150)) := by decide +kernel

theorem mergedZero2144 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2144 x = 0 := by
  rw [mergeCheck2144, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2145 : merged2145 = Integer.Sparse.merge (Integer.Sparse.scale (-16105071919104000) (sourceRows 2152)) (Integer.Sparse.scale (-136634074214400000) (sourceRows 2153)) := by decide +kernel

theorem mergedZero2145 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2145 x = 0 := by
  rw [mergeCheck2145, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2146 : merged2146 = Integer.Sparse.merge (Integer.Sparse.scale (-67325754617856000) (sourceRows 2151)) merged2145 := by decide +kernel

theorem mergedZero2146 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2146 x = 0 := by
  rw [mergeCheck2146, Integer.Sparse.eval_merge]
  rw [mergedZero2145 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2147 : merged2147 = Integer.Sparse.merge merged2144 merged2146 := by decide +kernel

theorem mergedZero2147 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2147 x = 0 := by
  rw [mergeCheck2147, Integer.Sparse.eval_merge]
  rw [mergedZero2144 x h, mergedZero2146 x h]
  simp only [add_zero]

theorem mergeCheck2148 : merged2148 = Integer.Sparse.merge (Integer.Sparse.scale (-23247717341184000) (sourceRows 2154)) (Integer.Sparse.scale (-37875851403264000) (sourceRows 2155)) := by decide +kernel

theorem mergedZero2148 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2148 x = 0 := by
  rw [mergeCheck2148, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2149 : merged2149 = Integer.Sparse.merge (Integer.Sparse.scale (-203367323013120000) (sourceRows 2157)) (Integer.Sparse.scale (880824142098432000) (sourceRows 2158)) := by decide +kernel

theorem mergedZero2149 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2149 x = 0 := by
  rw [mergeCheck2149, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2150 : merged2150 = Integer.Sparse.merge (Integer.Sparse.scale (961563390713856000) (sourceRows 2156)) merged2149 := by decide +kernel

theorem mergedZero2150 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2150 x = 0 := by
  rw [mergeCheck2150, Integer.Sparse.eval_merge]
  rw [mergedZero2149 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2151 : merged2151 = Integer.Sparse.merge merged2148 merged2150 := by decide +kernel

theorem mergedZero2151 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2151 x = 0 := by
  rw [mergeCheck2151, Integer.Sparse.eval_merge]
  rw [mergedZero2148 x h, mergedZero2150 x h]
  simp only [add_zero]

theorem mergeCheck2152 : merged2152 = Integer.Sparse.merge merged2147 merged2151 := by decide +kernel

theorem mergedZero2152 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2152 x = 0 := by
  rw [mergeCheck2152, Integer.Sparse.eval_merge]
  rw [mergedZero2147 x h, mergedZero2151 x h]
  simp only [add_zero]

theorem mergeCheck2153 : merged2153 = Integer.Sparse.merge merged2143 merged2152 := by decide +kernel

theorem mergedZero2153 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2153 x = 0 := by
  rw [mergeCheck2153, Integer.Sparse.eval_merge]
  rw [mergedZero2143 x h, mergedZero2152 x h]
  simp only [add_zero]

theorem mergeCheck2154 : merged2154 = Integer.Sparse.merge merged2135 merged2153 := by decide +kernel

theorem mergedZero2154 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2154 x = 0 := by
  rw [mergeCheck2154, Integer.Sparse.eval_merge]
  rw [mergedZero2135 x h, mergedZero2153 x h]
  simp only [add_zero]

theorem mergeCheck2155 : merged2155 = Integer.Sparse.merge (Integer.Sparse.scale (-126922315032576000) (sourceRows 2159)) (Integer.Sparse.scale (31892602355712000) (sourceRows 2160)) := by decide +kernel

theorem mergedZero2155 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2155 x = 0 := by
  rw [mergeCheck2155, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2156 : merged2156 = Integer.Sparse.merge (Integer.Sparse.scale (-65683430572032000) (sourceRows 2161)) (Integer.Sparse.scale (-81196310200320000) (sourceRows 2162)) := by decide +kernel

theorem mergedZero2156 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2156 x = 0 := by
  rw [mergeCheck2156, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2157 : merged2157 = Integer.Sparse.merge merged2155 merged2156 := by decide +kernel

theorem mergedZero2157 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2157 x = 0 := by
  rw [mergeCheck2157, Integer.Sparse.eval_merge]
  rw [mergedZero2155 x h, mergedZero2156 x h]
  simp only [add_zero]

theorem mergeCheck2158 : merged2158 = Integer.Sparse.merge (Integer.Sparse.scale (-127762288754688000) (sourceRows 2163)) (Integer.Sparse.scale (583000142118912000) (sourceRows 2164)) := by decide +kernel

theorem mergedZero2158 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2158 x = 0 := by
  rw [mergeCheck2158, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2159 : merged2159 = Integer.Sparse.merge (Integer.Sparse.scale (-471481894938622064730) (sourceRows 2166)) (Integer.Sparse.scale (14585853364901976168600) (sourceRows 2167)) := by decide +kernel

theorem mergedZero2159 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2159 x = 0 := by
  rw [mergeCheck2159, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2160 : merged2160 = Integer.Sparse.merge (Integer.Sparse.scale (-48953614284288000) (sourceRows 2165)) merged2159 := by decide +kernel

theorem mergedZero2160 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2160 x = 0 := by
  rw [mergeCheck2160, Integer.Sparse.eval_merge]
  rw [mergedZero2159 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2161 : merged2161 = Integer.Sparse.merge merged2158 merged2160 := by decide +kernel

theorem mergedZero2161 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2161 x = 0 := by
  rw [mergeCheck2161, Integer.Sparse.eval_merge]
  rw [mergedZero2158 x h, mergedZero2160 x h]
  simp only [add_zero]

theorem mergeCheck2162 : merged2162 = Integer.Sparse.merge merged2157 merged2161 := by decide +kernel

theorem mergedZero2162 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2162 x = 0 := by
  rw [mergeCheck2162, Integer.Sparse.eval_merge]
  rw [mergedZero2157 x h, mergedZero2161 x h]
  simp only [add_zero]

theorem mergeCheck2163 : merged2163 = Integer.Sparse.merge (Integer.Sparse.scale (-9359487155430625758600) (sourceRows 2168)) (Integer.Sparse.scale (-1576483324055018373600) (sourceRows 2169)) := by decide +kernel

theorem mergedZero2163 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2163 x = 0 := by
  rw [mergeCheck2163, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2164 : merged2164 = Integer.Sparse.merge (Integer.Sparse.scale (1647298494211020315105) (sourceRows 2171)) (Integer.Sparse.scale (-9023810459646773794770) (sourceRows 2172)) := by decide +kernel

theorem mergedZero2164 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2164 x = 0 := by
  rw [mergeCheck2164, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2165 : merged2165 = Integer.Sparse.merge (Integer.Sparse.scale (3355456074771726820680) (sourceRows 2170)) merged2164 := by decide +kernel

theorem mergedZero2165 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2165 x = 0 := by
  rw [mergeCheck2165, Integer.Sparse.eval_merge]
  rw [mergedZero2164 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2166 : merged2166 = Integer.Sparse.merge merged2163 merged2165 := by decide +kernel

theorem mergedZero2166 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2166 x = 0 := by
  rw [mergeCheck2166, Integer.Sparse.eval_merge]
  rw [mergedZero2163 x h, mergedZero2165 x h]
  simp only [add_zero]

theorem mergeCheck2167 : merged2167 = Integer.Sparse.merge (Integer.Sparse.scale (1898532428544381888000) (sourceRows 2173)) (Integer.Sparse.scale (149170466996631331200) (sourceRows 2174)) := by decide +kernel

theorem mergedZero2167 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2167 x = 0 := by
  rw [mergeCheck2167, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2168 : merged2168 = Integer.Sparse.merge (Integer.Sparse.scale (-266357691941051750400) (sourceRows 2176)) (Integer.Sparse.scale (2739225600000) (sourceRows 2177)) := by decide +kernel

theorem mergedZero2168 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2168 x = 0 := by
  rw [mergeCheck2168, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2169 : merged2169 = Integer.Sparse.merge (Integer.Sparse.scale (-214544380976863430400) (sourceRows 2175)) merged2168 := by decide +kernel

theorem mergedZero2169 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2169 x = 0 := by
  rw [mergeCheck2169, Integer.Sparse.eval_merge]
  rw [mergedZero2168 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2170 : merged2170 = Integer.Sparse.merge merged2167 merged2169 := by decide +kernel

theorem mergedZero2170 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2170 x = 0 := by
  rw [mergeCheck2170, Integer.Sparse.eval_merge]
  rw [mergedZero2167 x h, mergedZero2169 x h]
  simp only [add_zero]

theorem mergeCheck2171 : merged2171 = Integer.Sparse.merge merged2166 merged2170 := by decide +kernel

theorem mergedZero2171 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2171 x = 0 := by
  rw [mergeCheck2171, Integer.Sparse.eval_merge]
  rw [mergedZero2166 x h, mergedZero2170 x h]
  simp only [add_zero]

theorem mergeCheck2172 : merged2172 = Integer.Sparse.merge merged2162 merged2171 := by decide +kernel

theorem mergedZero2172 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2172 x = 0 := by
  rw [mergeCheck2172, Integer.Sparse.eval_merge]
  rw [mergedZero2162 x h, mergedZero2171 x h]
  simp only [add_zero]

theorem mergeCheck2173 : merged2173 = Integer.Sparse.merge (Integer.Sparse.scale (2663576451002939904000) (sourceRows 2178)) (Integer.Sparse.scale (133178859529692595200) (sourceRows 2179)) := by decide +kernel

theorem mergedZero2173 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2173 x = 0 := by
  rw [mergeCheck2173, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2174 : merged2174 = Integer.Sparse.merge (Integer.Sparse.scale (-29552210277540595200) (sourceRows 2180)) (Integer.Sparse.scale (368997011479345660960) (sourceRows 2181)) := by decide +kernel

theorem mergedZero2174 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2174 x = 0 := by
  rw [mergeCheck2174, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2175 : merged2175 = Integer.Sparse.merge merged2173 merged2174 := by decide +kernel

theorem mergedZero2175 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2175 x = 0 := by
  rw [mergeCheck2175, Integer.Sparse.eval_merge]
  rw [mergedZero2173 x h, mergedZero2174 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2176 : merged2176 = Integer.Sparse.merge (Integer.Sparse.scale (709891899627673299340) (sourceRows 2182)) (Integer.Sparse.scale (565015994851938066720) (sourceRows 2183)) := by decide +kernel

theorem mergedZero2176 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2176 x = 0 := by
  rw [mergeCheck2176, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2177 : merged2177 = Integer.Sparse.merge (Integer.Sparse.scale (-1211837945923492600400) (sourceRows 2185)) (Integer.Sparse.scale (911061131617190060700) (sourceRows 2186)) := by decide +kernel

theorem mergedZero2177 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2177 x = 0 := by
  rw [mergeCheck2177, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2178 : merged2178 = Integer.Sparse.merge (Integer.Sparse.scale (382575018872691703800) (sourceRows 2184)) merged2177 := by decide +kernel

theorem mergedZero2178 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2178 x = 0 := by
  rw [mergeCheck2178, Integer.Sparse.eval_merge]
  rw [mergedZero2177 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2179 : merged2179 = Integer.Sparse.merge merged2176 merged2178 := by decide +kernel

theorem mergedZero2179 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2179 x = 0 := by
  rw [mergeCheck2179, Integer.Sparse.eval_merge]
  rw [mergedZero2176 x h, mergedZero2178 x h]
  simp only [add_zero]

theorem mergeCheck2180 : merged2180 = Integer.Sparse.merge merged2175 merged2179 := by decide +kernel

theorem mergedZero2180 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2180 x = 0 := by
  rw [mergeCheck2180, Integer.Sparse.eval_merge]
  rw [mergedZero2175 x h, mergedZero2179 x h]
  simp only [add_zero]

theorem mergeCheck2181 : merged2181 = Integer.Sparse.merge (Integer.Sparse.scale (-98397226572127027200) (sourceRows 2187)) (Integer.Sparse.scale (-84845193292519372800) (sourceRows 2188)) := by decide +kernel

theorem mergedZero2181 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2181 x = 0 := by
  rw [mergeCheck2181, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2182 : merged2182 = Integer.Sparse.merge (Integer.Sparse.scale (-305122143982574952000) (sourceRows 2190)) (Integer.Sparse.scale (211603340467242874080) (sourceRows 2191)) := by decide +kernel

theorem mergedZero2182 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2182 x = 0 := by
  rw [mergeCheck2182, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2183 : merged2183 = Integer.Sparse.merge (Integer.Sparse.scale (836973200925869221440) (sourceRows 2189)) merged2182 := by decide +kernel

theorem mergedZero2183 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2183 x = 0 := by
  rw [mergeCheck2183, Integer.Sparse.eval_merge]
  rw [mergedZero2182 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2184 : merged2184 = Integer.Sparse.merge merged2181 merged2183 := by decide +kernel

theorem mergedZero2184 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2184 x = 0 := by
  rw [mergeCheck2184, Integer.Sparse.eval_merge]
  rw [mergedZero2181 x h, mergedZero2183 x h]
  simp only [add_zero]

theorem mergeCheck2185 : merged2185 = Integer.Sparse.merge (Integer.Sparse.scale (-50061709587488018400) (sourceRows 2192)) (Integer.Sparse.scale (81365791123931155200) (sourceRows 2193)) := by decide +kernel

theorem mergedZero2185 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2185 x = 0 := by
  rw [mergeCheck2185, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2186 : merged2186 = Integer.Sparse.merge (Integer.Sparse.scale (-188637950068468070400) (sourceRows 2195)) (Integer.Sparse.scale (-98475873218063989920) (sourceRows 2196)) := by decide +kernel

theorem mergedZero2186 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2186 x = 0 := by
  rw [mergeCheck2186, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2187 : merged2187 = Integer.Sparse.merge (Integer.Sparse.scale (377275890275723980800) (sourceRows 2194)) merged2186 := by decide +kernel

theorem mergedZero2187 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2187 x = 0 := by
  rw [mergeCheck2187, Integer.Sparse.eval_merge]
  rw [mergedZero2186 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2188 : merged2188 = Integer.Sparse.merge merged2185 merged2187 := by decide +kernel

theorem mergedZero2188 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2188 x = 0 := by
  rw [mergeCheck2188, Integer.Sparse.eval_merge]
  rw [mergedZero2185 x h, mergedZero2187 x h]
  simp only [add_zero]

theorem mergeCheck2189 : merged2189 = Integer.Sparse.merge merged2184 merged2188 := by decide +kernel

theorem mergedZero2189 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2189 x = 0 := by
  rw [mergeCheck2189, Integer.Sparse.eval_merge]
  rw [mergedZero2184 x h, mergedZero2188 x h]
  simp only [add_zero]

theorem mergeCheck2190 : merged2190 = Integer.Sparse.merge merged2180 merged2189 := by decide +kernel

theorem mergedZero2190 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2190 x = 0 := by
  rw [mergeCheck2190, Integer.Sparse.eval_merge]
  rw [mergedZero2180 x h, mergedZero2189 x h]
  simp only [add_zero]

theorem mergeCheck2191 : merged2191 = Integer.Sparse.merge merged2172 merged2190 := by decide +kernel

theorem mergedZero2191 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2191 x = 0 := by
  rw [mergeCheck2191, Integer.Sparse.eval_merge]
  rw [mergedZero2172 x h, mergedZero2190 x h]
  simp only [add_zero]

theorem mergeCheck2192 : merged2192 = Integer.Sparse.merge merged2154 merged2191 := by decide +kernel

theorem mergedZero2192 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2192 x = 0 := by
  rw [mergeCheck2192, Integer.Sparse.eval_merge]
  rw [mergedZero2154 x h, mergedZero2191 x h]
  simp only [add_zero]

theorem mergeCheck2193 : merged2193 = Integer.Sparse.merge (Integer.Sparse.scale (2430420944481676800) (sourceRows 2197)) (Integer.Sparse.scale (-79542136861573017600) (sourceRows 2198)) := by decide +kernel

theorem mergedZero2193 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2193 x = 0 := by
  rw [mergeCheck2193, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2194 : merged2194 = Integer.Sparse.merge (Integer.Sparse.scale (67803579574694496000) (sourceRows 2199)) (Integer.Sparse.scale (-205099516800000) (sourceRows 2200)) := by decide +kernel

theorem mergedZero2194 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2194 x = 0 := by
  rw [mergeCheck2194, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2195 : merged2195 = Integer.Sparse.merge merged2193 merged2194 := by decide +kernel

theorem mergedZero2195 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2195 x = 0 := by
  rw [mergeCheck2195, Integer.Sparse.eval_merge]
  rw [mergedZero2193 x h, mergedZero2194 x h]
  simp only [add_zero]

theorem mergeCheck2196 : merged2196 = Integer.Sparse.merge (Integer.Sparse.scale (-241666255516958668800) (sourceRows 2201)) (Integer.Sparse.scale (-129531505687912800000) (sourceRows 2202)) := by decide +kernel

theorem mergedZero2196 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2196 x = 0 := by
  rw [mergeCheck2196, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2197 : merged2197 = Integer.Sparse.merge (Integer.Sparse.scale (-283373312515973568000) (sourceRows 2204)) (Integer.Sparse.scale (-94926617112938774400) (sourceRows 2205)) := by decide +kernel

theorem mergedZero2197 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2197 x = 0 := by
  rw [mergeCheck2197, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2198 : merged2198 = Integer.Sparse.merge (Integer.Sparse.scale (723155558400000) (sourceRows 2203)) merged2197 := by decide +kernel

theorem mergedZero2198 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2198 x = 0 := by
  rw [mergeCheck2198, Integer.Sparse.eval_merge]
  rw [mergedZero2197 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2199 : merged2199 = Integer.Sparse.merge merged2196 merged2198 := by decide +kernel

theorem mergedZero2199 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2199 x = 0 := by
  rw [mergeCheck2199, Integer.Sparse.eval_merge]
  rw [mergedZero2196 x h, mergedZero2198 x h]
  simp only [add_zero]

theorem mergeCheck2200 : merged2200 = Integer.Sparse.merge merged2195 merged2199 := by decide +kernel

theorem mergedZero2200 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2200 x = 0 := by
  rw [mergeCheck2200, Integer.Sparse.eval_merge]
  rw [mergedZero2195 x h, mergedZero2199 x h]
  simp only [add_zero]

theorem mergeCheck2201 : merged2201 = Integer.Sparse.merge (Integer.Sparse.scale (53636094627890097600) (sourceRows 2206)) (Integer.Sparse.scale (-66589411275073497600) (sourceRows 2207)) := by decide +kernel

theorem mergedZero2201 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2201 x = 0 := by
  rw [mergeCheck2201, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2202 : merged2202 = Integer.Sparse.merge (Integer.Sparse.scale (-48925253891583924480) (sourceRows 2209)) (Integer.Sparse.scale (41026693273210814400) (sourceRows 2210)) := by decide +kernel

theorem mergedZero2202 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2202 x = 0 := by
  rw [mergeCheck2202, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2203 : merged2203 = Integer.Sparse.merge (Integer.Sparse.scale (-431519765171970297600) (sourceRows 2208)) merged2202 := by decide +kernel

theorem mergedZero2203 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2203 x = 0 := by
  rw [mergeCheck2203, Integer.Sparse.eval_merge]
  rw [mergedZero2202 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2204 : merged2204 = Integer.Sparse.merge merged2201 merged2203 := by decide +kernel

theorem mergedZero2204 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2204 x = 0 := by
  rw [mergeCheck2204, Integer.Sparse.eval_merge]
  rw [mergedZero2201 x h, mergedZero2203 x h]
  simp only [add_zero]

theorem mergeCheck2205 : merged2205 = Integer.Sparse.merge (Integer.Sparse.scale (167704727870085120000) (sourceRows 2211)) (Integer.Sparse.scale (20090325909474504000) (sourceRows 2212)) := by decide +kernel

theorem mergedZero2205 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2205 x = 0 := by
  rw [mergeCheck2205, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2206 : merged2206 = Integer.Sparse.merge (Integer.Sparse.scale (26570522719557584640) (sourceRows 2214)) (Integer.Sparse.scale (42165096512153544000) (sourceRows 2215)) := by decide +kernel

theorem mergedZero2206 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2206 x = 0 := by
  rw [mergeCheck2206, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2207 : merged2207 = Integer.Sparse.merge (Integer.Sparse.scale (-6550171644794400000) (sourceRows 2213)) merged2206 := by decide +kernel

theorem mergedZero2207 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2207 x = 0 := by
  rw [mergeCheck2207, Integer.Sparse.eval_merge]
  rw [mergedZero2206 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2208 : merged2208 = Integer.Sparse.merge merged2205 merged2207 := by decide +kernel

theorem mergedZero2208 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2208 x = 0 := by
  rw [mergeCheck2208, Integer.Sparse.eval_merge]
  rw [mergedZero2205 x h, mergedZero2207 x h]
  simp only [add_zero]

theorem mergeCheck2209 : merged2209 = Integer.Sparse.merge merged2204 merged2208 := by decide +kernel

theorem mergedZero2209 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2209 x = 0 := by
  rw [mergeCheck2209, Integer.Sparse.eval_merge]
  rw [mergedZero2204 x h, mergedZero2208 x h]
  simp only [add_zero]

theorem mergeCheck2210 : merged2210 = Integer.Sparse.merge merged2200 merged2209 := by decide +kernel

theorem mergedZero2210 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2210 x = 0 := by
  rw [mergeCheck2210, Integer.Sparse.eval_merge]
  rw [mergedZero2200 x h, mergedZero2209 x h]
  simp only [add_zero]

theorem mergeCheck2211 : merged2211 = Integer.Sparse.merge (Integer.Sparse.scale (49204814183959680000) (sourceRows 2216)) (Integer.Sparse.scale (-11065137673376044800) (sourceRows 2217)) := by decide +kernel

theorem mergedZero2211 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2211 x = 0 := by
  rw [mergeCheck2211, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2212 : merged2212 = Integer.Sparse.merge (Integer.Sparse.scale (471735256679053516800) (sourceRows 2218)) (Integer.Sparse.scale (13560676584224659200) (sourceRows 2219)) := by decide +kernel

theorem mergedZero2212 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2212 x = 0 := by
  rw [mergeCheck2212, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2213 : merged2213 = Integer.Sparse.merge merged2211 merged2212 := by decide +kernel

theorem mergedZero2213 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2213 x = 0 := by
  rw [mergeCheck2213, Integer.Sparse.eval_merge]
  rw [mergedZero2211 x h, mergedZero2212 x h]
  simp only [add_zero]

theorem mergeCheck2214 : merged2214 = Integer.Sparse.merge (Integer.Sparse.scale (160300531213011993600) (sourceRows 2220)) (Integer.Sparse.scale (-16161431040000) (sourceRows 2221)) := by decide +kernel

theorem mergedZero2214 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2214 x = 0 := by
  rw [mergeCheck2214, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2215 : merged2215 = Integer.Sparse.merge (Integer.Sparse.scale (-40682873417038617600) (sourceRows 2223)) (Integer.Sparse.scale (-742814405959462560000) (sourceRows 2224)) := by decide +kernel

theorem mergedZero2215 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2215 x = 0 := by
  rw [mergeCheck2215, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2216 : merged2216 = Integer.Sparse.merge (Integer.Sparse.scale (-27940101120000) (sourceRows 2222)) merged2215 := by decide +kernel

theorem mergedZero2216 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2216 x = 0 := by
  rw [mergeCheck2216, Integer.Sparse.eval_merge]
  rw [mergedZero2215 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2217 : merged2217 = Integer.Sparse.merge merged2214 merged2216 := by decide +kernel

theorem mergedZero2217 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2217 x = 0 := by
  rw [mergeCheck2217, Integer.Sparse.eval_merge]
  rw [mergedZero2214 x h, mergedZero2216 x h]
  simp only [add_zero]

theorem mergeCheck2218 : merged2218 = Integer.Sparse.merge merged2213 merged2217 := by decide +kernel

theorem mergedZero2218 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2218 x = 0 := by
  rw [mergeCheck2218, Integer.Sparse.eval_merge]
  rw [mergedZero2213 x h, mergedZero2217 x h]
  simp only [add_zero]

theorem mergeCheck2219 : merged2219 = Integer.Sparse.merge (Integer.Sparse.scale (-61667798288350233600) (sourceRows 2225)) (Integer.Sparse.scale (-440599108461867187200) (sourceRows 2226)) := by decide +kernel

theorem mergedZero2219 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2219 x = 0 := by
  rw [mergeCheck2219, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2220 : merged2220 = Integer.Sparse.merge (Integer.Sparse.scale (-84593858647296384000) (sourceRows 2228)) (Integer.Sparse.scale (-8948205002350080000) (sourceRows 2229)) := by decide +kernel

theorem mergedZero2220 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2220 x = 0 := by
  rw [mergeCheck2220, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2221 : merged2221 = Integer.Sparse.merge (Integer.Sparse.scale (-177894323563761100800) (sourceRows 2227)) merged2220 := by decide +kernel

theorem mergedZero2221 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2221 x = 0 := by
  rw [mergeCheck2221, Integer.Sparse.eval_merge]
  rw [mergedZero2220 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2222 : merged2222 = Integer.Sparse.merge merged2219 merged2221 := by decide +kernel

theorem mergedZero2222 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2222 x = 0 := by
  rw [mergeCheck2222, Integer.Sparse.eval_merge]
  rw [mergedZero2219 x h, mergedZero2221 x h]
  simp only [add_zero]

theorem mergeCheck2223 : merged2223 = Integer.Sparse.merge (Integer.Sparse.scale (-783563706777600000) (sourceRows 2230)) (Integer.Sparse.scale (120193786125197107200) (sourceRows 2231)) := by decide +kernel

theorem mergedZero2223 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2223 x = 0 := by
  rw [mergeCheck2223, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2224 : merged2224 = Integer.Sparse.merge (Integer.Sparse.scale (-22998626512021440000) (sourceRows 2233)) (Integer.Sparse.scale (688132721846976768000) (sourceRows 2234)) := by decide +kernel

theorem mergedZero2224 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2224 x = 0 := by
  rw [mergeCheck2224, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2225 : merged2225 = Integer.Sparse.merge (Integer.Sparse.scale (-275181185833804800000) (sourceRows 2232)) merged2224 := by decide +kernel

theorem mergedZero2225 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2225 x = 0 := by
  rw [mergeCheck2225, Integer.Sparse.eval_merge]
  rw [mergedZero2224 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2226 : merged2226 = Integer.Sparse.merge merged2223 merged2225 := by decide +kernel

theorem mergedZero2226 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2226 x = 0 := by
  rw [mergeCheck2226, Integer.Sparse.eval_merge]
  rw [mergedZero2223 x h, mergedZero2225 x h]
  simp only [add_zero]

theorem mergeCheck2227 : merged2227 = Integer.Sparse.merge merged2222 merged2226 := by decide +kernel

theorem mergedZero2227 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2227 x = 0 := by
  rw [mergeCheck2227, Integer.Sparse.eval_merge]
  rw [mergedZero2222 x h, mergedZero2226 x h]
  simp only [add_zero]

theorem mergeCheck2228 : merged2228 = Integer.Sparse.merge merged2218 merged2227 := by decide +kernel

theorem mergedZero2228 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2228 x = 0 := by
  rw [mergeCheck2228, Integer.Sparse.eval_merge]
  rw [mergedZero2218 x h, mergedZero2227 x h]
  simp only [add_zero]

theorem mergeCheck2229 : merged2229 = Integer.Sparse.merge merged2210 merged2228 := by decide +kernel

theorem mergedZero2229 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2229 x = 0 := by
  rw [mergeCheck2229, Integer.Sparse.eval_merge]
  rw [mergedZero2210 x h, mergedZero2228 x h]
  simp only [add_zero]

theorem mergeCheck2230 : merged2230 = Integer.Sparse.merge (Integer.Sparse.scale (7259078082816000000) (sourceRows 2235)) (Integer.Sparse.scale (128974759899955200000) (sourceRows 2236)) := by decide +kernel

theorem mergedZero2230 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2230 x = 0 := by
  rw [mergeCheck2230, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2231 : merged2231 = Integer.Sparse.merge (Integer.Sparse.scale (-1509943717012500288000) (sourceRows 2237)) (Integer.Sparse.scale (11299305600000) (sourceRows 2238)) := by decide +kernel

theorem mergedZero2231 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2231 x = 0 := by
  rw [mergeCheck2231, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2232 : merged2232 = Integer.Sparse.merge merged2230 merged2231 := by decide +kernel

theorem mergedZero2232 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2232 x = 0 := by
  rw [mergeCheck2232, Integer.Sparse.eval_merge]
  rw [mergedZero2230 x h, mergedZero2231 x h]
  simp only [add_zero]

theorem mergeCheck2233 : merged2233 = Integer.Sparse.merge (Integer.Sparse.scale (-160300164636146073600) (sourceRows 2239)) (Integer.Sparse.scale (14169024729714758400) (sourceRows 2240)) := by decide +kernel

theorem mergedZero2233 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2233 x = 0 := by
  rw [mergeCheck2233, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2234 : merged2234 = Integer.Sparse.merge (Integer.Sparse.scale (-7084514196714499200) (sourceRows 2242)) (Integer.Sparse.scale (-27121846411672358400) (sourceRows 2243)) := by decide +kernel

theorem mergedZero2234 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2234 x = 0 := by
  rw [mergeCheck2234, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2235 : merged2235 = Integer.Sparse.merge (Integer.Sparse.scale (-44512416000000) (sourceRows 2241)) merged2234 := by decide +kernel

theorem mergedZero2235 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2235 x = 0 := by
  rw [mergeCheck2235, Integer.Sparse.eval_merge]
  rw [mergedZero2234 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2236 : merged2236 = Integer.Sparse.merge merged2233 merged2235 := by decide +kernel

theorem mergedZero2236 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2236 x = 0 := by
  rw [mergeCheck2236, Integer.Sparse.eval_merge]
  rw [mergedZero2233 x h, mergedZero2235 x h]
  simp only [add_zero]

theorem mergeCheck2237 : merged2237 = Integer.Sparse.merge merged2232 merged2236 := by decide +kernel

theorem mergedZero2237 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2237 x = 0 := by
  rw [mergeCheck2237, Integer.Sparse.eval_merge]
  rw [mergedZero2232 x h, mergedZero2236 x h]
  simp only [add_zero]

theorem mergeCheck2238 : merged2238 = Integer.Sparse.merge (Integer.Sparse.scale (67197031645415356800) (sourceRows 2244)) (Integer.Sparse.scale (234277046985810240000) (sourceRows 2245)) := by decide +kernel

theorem mergedZero2238 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2238 x = 0 := by
  rw [mergeCheck2238, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2239 : merged2239 = Integer.Sparse.merge (Integer.Sparse.scale (-67803938670050496000) (sourceRows 2247)) (Integer.Sparse.scale (-271219563145394784000) (sourceRows 2248)) := by decide +kernel

theorem mergedZero2239 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2239 x = 0 := by
  rw [mergeCheck2239, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2240 : merged2240 = Integer.Sparse.merge (Integer.Sparse.scale (13560779516333299200) (sourceRows 2246)) merged2239 := by decide +kernel

theorem mergedZero2240 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2240 x = 0 := by
  rw [mergeCheck2240, Integer.Sparse.eval_merge]
  rw [mergedZero2239 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2241 : merged2241 = Integer.Sparse.merge merged2238 merged2240 := by decide +kernel

theorem mergedZero2241 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2241 x = 0 := by
  rw [mergeCheck2241, Integer.Sparse.eval_merge]
  rw [mergedZero2238 x h, mergedZero2240 x h]
  simp only [add_zero]

theorem mergeCheck2242 : merged2242 = Integer.Sparse.merge (Integer.Sparse.scale (573301335044603520000) (sourceRows 2249)) (Integer.Sparse.scale (-67197023684540956800) (sourceRows 2250)) := by decide +kernel

theorem mergedZero2242 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2242 x = 0 := by
  rw [mergeCheck2242, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2243 : merged2243 = Integer.Sparse.merge (Integer.Sparse.scale (81365873257898755200) (sourceRows 2252)) (Integer.Sparse.scale (75497185850625014400) (sourceRows 2253)) := by decide +kernel

theorem mergedZero2243 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2243 x = 0 := by
  rw [mergeCheck2243, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2244 : merged2244 = Integer.Sparse.merge (Integer.Sparse.scale (-27121529859913958400) (sourceRows 2251)) merged2243 := by decide +kernel

theorem mergedZero2244 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2244 x = 0 := by
  rw [mergeCheck2244, Integer.Sparse.eval_merge]
  rw [mergedZero2243 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2245 : merged2245 = Integer.Sparse.merge merged2242 merged2244 := by decide +kernel

theorem mergedZero2245 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2245 x = 0 := by
  rw [mergeCheck2245, Integer.Sparse.eval_merge]
  rw [mergedZero2242 x h, mergedZero2244 x h]
  simp only [add_zero]

theorem mergeCheck2246 : merged2246 = Integer.Sparse.merge merged2241 merged2245 := by decide +kernel

theorem mergedZero2246 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2246 x = 0 := by
  rw [mergeCheck2246, Integer.Sparse.eval_merge]
  rw [mergedZero2241 x h, mergedZero2245 x h]
  simp only [add_zero]

theorem mergeCheck2247 : merged2247 = Integer.Sparse.merge merged2237 merged2246 := by decide +kernel

theorem mergedZero2247 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2247 x = 0 := by
  rw [mergeCheck2247, Integer.Sparse.eval_merge]
  rw [mergedZero2237 x h, mergedZero2246 x h]
  simp only [add_zero]

theorem mergeCheck2248 : merged2248 = Integer.Sparse.merge (Integer.Sparse.scale (-61328265006041136000) (sourceRows 2254)) (Integer.Sparse.scale (-14168920844583878400) (sourceRows 2255)) := by decide +kernel

theorem mergedZero2248 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2248 x = 0 := by
  rw [mergeCheck2248, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2249 : merged2249 = Integer.Sparse.merge (Integer.Sparse.scale (11504747520000) (sourceRows 2256)) (Integer.Sparse.scale (-81365679723050035200) (sourceRows 2257)) := by decide +kernel

theorem mergedZero2249 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2249 x = 0 := by
  rw [mergeCheck2249, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2250 : merged2250 = Integer.Sparse.merge merged2248 merged2249 := by decide +kernel

theorem mergedZero2250 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2250 x = 0 := by
  rw [mergeCheck2250, Integer.Sparse.eval_merge]
  rw [mergedZero2248 x h, mergedZero2249 x h]
  simp only [add_zero]

theorem mergeCheck2251 : merged2251 = Integer.Sparse.merge (Integer.Sparse.scale (-14168900266151558400) (sourceRows 2258)) (Integer.Sparse.scale (27121901915231078400) (sourceRows 2259)) := by decide +kernel

theorem mergedZero2251 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2251 x = 0 := by
  rw [mergeCheck2251, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2252 : merged2252 = Integer.Sparse.merge (Integer.Sparse.scale (108487531647413913600) (sourceRows 2261)) (Integer.Sparse.scale (83888784000000) (sourceRows 2262)) := by decide +kernel

theorem mergedZero2252 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2252 x = 0 := by
  rw [mergeCheck2252, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2253 : merged2253 = Integer.Sparse.merge (Integer.Sparse.scale (-40075077385295078400) (sourceRows 2260)) merged2252 := by decide +kernel

theorem mergedZero2253 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2253 x = 0 := by
  rw [mergeCheck2253, Integer.Sparse.eval_merge]
  rw [mergedZero2252 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2254 : merged2254 = Integer.Sparse.merge merged2251 merged2253 := by decide +kernel

theorem mergedZero2254 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2254 x = 0 := by
  rw [mergeCheck2254, Integer.Sparse.eval_merge]
  rw [mergedZero2251 x h, mergedZero2253 x h]
  simp only [add_zero]

theorem mergeCheck2255 : merged2255 = Integer.Sparse.merge merged2250 merged2254 := by decide +kernel

theorem mergedZero2255 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2255 x = 0 := by
  rw [mergeCheck2255, Integer.Sparse.eval_merge]
  rw [mergedZero2250 x h, mergedZero2254 x h]
  simp only [add_zero]

theorem mergeCheck2256 : merged2256 = Integer.Sparse.merge (Integer.Sparse.scale (56154124800000) (sourceRows 2263)) (Integer.Sparse.scale (129599611200000) (sourceRows 2264)) := by decide +kernel

theorem mergedZero2256 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2256 x = 0 := by
  rw [mergeCheck2256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2257 : merged2257 = Integer.Sparse.merge (Integer.Sparse.scale (-67803969486338496000) (sourceRows 2266)) (Integer.Sparse.scale (108487867168309593600) (sourceRows 2267)) := by decide +kernel

theorem mergedZero2257 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2257 x = 0 := by
  rw [mergeCheck2257, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2258 : merged2258 = Integer.Sparse.merge (Integer.Sparse.scale (108487405095191193600) (sourceRows 2265)) merged2257 := by decide +kernel

theorem mergedZero2258 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2258 x = 0 := by
  rw [mergeCheck2258, Integer.Sparse.eval_merge]
  rw [mergedZero2257 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2259 : merged2259 = Integer.Sparse.merge merged2256 merged2258 := by decide +kernel

theorem mergedZero2259 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2259 x = 0 := by
  rw [mergeCheck2259, Integer.Sparse.eval_merge]
  rw [mergedZero2256 x h, mergedZero2258 x h]
  simp only [add_zero]

theorem mergeCheck2260 : merged2260 = Integer.Sparse.merge (Integer.Sparse.scale (-135609769117780992000) (sourceRows 2268)) (Integer.Sparse.scale (236429162737900992000) (sourceRows 2269)) := by decide +kernel

theorem mergedZero2260 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2260 x = 0 := by
  rw [mergeCheck2260, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2261 : merged2261 = Integer.Sparse.merge (Integer.Sparse.scale (-3287070720000) (sourceRows 2271)) (Integer.Sparse.scale (821767680000) (sourceRows 2272)) := by decide +kernel

theorem mergedZero2261 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2261 x = 0 := by
  rw [mergeCheck2261, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2262 : merged2262 = Integer.Sparse.merge (Integer.Sparse.scale (-27121950810408038400) (sourceRows 2270)) merged2261 := by decide +kernel

theorem mergedZero2262 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2262 x = 0 := by
  rw [mergeCheck2262, Integer.Sparse.eval_merge]
  rw [mergedZero2261 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2263 : merged2263 = Integer.Sparse.merge merged2260 merged2262 := by decide +kernel

theorem mergedZero2263 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2263 x = 0 := by
  rw [mergeCheck2263, Integer.Sparse.eval_merge]
  rw [mergedZero2260 x h, mergedZero2262 x h]
  simp only [add_zero]

theorem mergeCheck2264 : merged2264 = Integer.Sparse.merge merged2259 merged2263 := by decide +kernel

theorem mergedZero2264 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2264 x = 0 := by
  rw [mergeCheck2264, Integer.Sparse.eval_merge]
  rw [mergedZero2259 x h, mergedZero2263 x h]
  simp only [add_zero]

theorem mergeCheck2265 : merged2265 = Integer.Sparse.merge merged2255 merged2264 := by decide +kernel

theorem mergedZero2265 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2265 x = 0 := by
  rw [mergeCheck2265, Integer.Sparse.eval_merge]
  rw [mergedZero2255 x h, mergedZero2264 x h]
  simp only [add_zero]

theorem mergeCheck2266 : merged2266 = Integer.Sparse.merge merged2247 merged2265 := by decide +kernel

theorem mergedZero2266 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2266 x = 0 := by
  rw [mergeCheck2266, Integer.Sparse.eval_merge]
  rw [mergedZero2247 x h, mergedZero2265 x h]
  simp only [add_zero]

theorem mergeCheck2267 : merged2267 = Integer.Sparse.merge merged2229 merged2266 := by decide +kernel

theorem mergedZero2267 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2267 x = 0 := by
  rw [mergeCheck2267, Integer.Sparse.eval_merge]
  rw [mergedZero2229 x h, mergedZero2266 x h]
  simp only [add_zero]

theorem mergeCheck2268 : merged2268 = Integer.Sparse.merge merged2192 merged2267 := by decide +kernel

theorem mergedZero2268 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2268 x = 0 := by
  rw [mergeCheck2268, Integer.Sparse.eval_merge]
  rw [mergedZero2192 x h, mergedZero2267 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2420 : merged2420 = Integer.Sparse.merge merged2268 merged2419 := by decide +kernel

theorem mergedZero2420 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2420 x = 0 := by
  rw [mergeCheck2420, Integer.Sparse.eval_merge]
  rw [mergedZero2268 x h, mergedZero2419_e x h]
  simp only [add_zero]

theorem mergeCheck2421 : merged2421 = Integer.Sparse.merge merged2117 merged2420 := by decide +kernel

theorem mergedZero2421_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2421 x = 0 := by
  rw [mergeCheck2421, Integer.Sparse.eval_merge]
  rw [mergedZero2117 x h, mergedZero2420 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero2421_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero2421_e_oai
