-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1210_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:37:40.888245+00:00
-- url     : https://prove2.me/submissions/05300aa0-06c3-4793-9c59-f005002bc36f

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E180
import Definitions.Def_OAIQ106E059
import Definitions.Def_OAIQ106E181
import Definitions.Def_OAIQ106E063
import Definitions.Def_OAIQ106E183
import Definitions.Def_OAIQ106E185
import Definitions.Def_OAIQ106E186
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1208_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero300_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero603_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero754_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero904_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck0 : merged0 = Integer.Sparse.merge (Integer.Sparse.scale (15357734392026912696720) (sourceRows 0)) (Integer.Sparse.scale (32332550166444604362300) (sourceRows 1)) := by decide +kernel

theorem mergedZero0 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged0 x = 0 := by
  rw [mergeCheck0, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1 : merged1 = Integer.Sparse.merge (Integer.Sparse.scale (2859528086971291726200) (sourceRows 2)) (Integer.Sparse.scale (-6445714169906629555770) (sourceRows 3)) := by decide +kernel

theorem mergedZero1 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1 x = 0 := by
  rw [mergeCheck1, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2 : merged2 = Integer.Sparse.merge merged0 merged1 := by decide +kernel

theorem mergedZero2 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2 x = 0 := by
  rw [mergeCheck2, Integer.Sparse.eval_merge]
  rw [mergedZero0 x h, mergedZero1 x h]
  simp only [add_zero]

theorem mergeCheck3 : merged3 = Integer.Sparse.merge (Integer.Sparse.scale (1258149954870237611926800) (sourceRows 4)) (Integer.Sparse.scale (-326444944117902936051600) (sourceRows 5)) := by decide +kernel

theorem mergedZero3 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged3 x = 0 := by
  rw [mergeCheck3, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck4 : merged4 = Integer.Sparse.merge (Integer.Sparse.scale (124171180781189484927600) (sourceRows 7)) (Integer.Sparse.scale (3395997384597721242045) (sourceRows 8)) := by decide +kernel

theorem mergedZero4 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged4 x = 0 := by
  rw [mergeCheck4, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck5 : merged5 = Integer.Sparse.merge (Integer.Sparse.scale (-3096559467411397668555) (sourceRows 6)) merged4 := by decide +kernel

theorem mergedZero5 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged5 x = 0 := by
  rw [mergeCheck5, Integer.Sparse.eval_merge]
  rw [mergedZero4 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck6 : merged6 = Integer.Sparse.merge merged3 merged5 := by decide +kernel

theorem mergedZero6 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged6 x = 0 := by
  rw [mergeCheck6, Integer.Sparse.eval_merge]
  rw [mergedZero3 x h, mergedZero5 x h]
  simp only [add_zero]

theorem mergeCheck7 : merged7 = Integer.Sparse.merge merged2 merged6 := by decide +kernel

theorem mergedZero7 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged7 x = 0 := by
  rw [mergeCheck7, Integer.Sparse.eval_merge]
  rw [mergedZero2 x h, mergedZero6 x h]
  simp only [add_zero]

theorem mergeCheck8 : merged8 = Integer.Sparse.merge (Integer.Sparse.scale (-161902519766095530271500) (sourceRows 9)) (Integer.Sparse.scale (303087927832139457735840) (sourceRows 10)) := by decide +kernel

theorem mergedZero8 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged8 x = 0 := by
  rw [mergeCheck8, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck9 : merged9 = Integer.Sparse.merge (Integer.Sparse.scale (682651120580828509549320) (sourceRows 11)) (Integer.Sparse.scale (-1778921829578303070150) (sourceRows 12)) := by decide +kernel

theorem mergedZero9 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged9 x = 0 := by
  rw [mergeCheck9, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck10 : merged10 = Integer.Sparse.merge merged8 merged9 := by decide +kernel

theorem mergedZero10 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged10 x = 0 := by
  rw [mergeCheck10, Integer.Sparse.eval_merge]
  rw [mergedZero8 x h, mergedZero9 x h]
  simp only [add_zero]

theorem mergeCheck11 : merged11 = Integer.Sparse.merge (Integer.Sparse.scale (-1558123319545552039560) (sourceRows 13)) (Integer.Sparse.scale (-3609590204025959883660) (sourceRows 14)) := by decide +kernel

theorem mergedZero11 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged11 x = 0 := by
  rw [mergeCheck11, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck12 : merged12 = Integer.Sparse.merge (Integer.Sparse.scale (24625873744536946073220) (sourceRows 16)) (Integer.Sparse.scale (18617542608584318902650) (sourceRows 17)) := by decide +kernel

theorem mergedZero12 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged12 x = 0 := by
  rw [mergeCheck12, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck13 : merged13 = Integer.Sparse.merge (Integer.Sparse.scale (2996680884161723827215) (sourceRows 15)) merged12 := by decide +kernel

theorem mergedZero13 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged13 x = 0 := by
  rw [mergeCheck13, Integer.Sparse.eval_merge]
  rw [mergedZero12 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck14 : merged14 = Integer.Sparse.merge merged11 merged13 := by decide +kernel

theorem mergedZero14 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged14 x = 0 := by
  rw [mergeCheck14, Integer.Sparse.eval_merge]
  rw [mergedZero11 x h, mergedZero13 x h]
  simp only [add_zero]

theorem mergeCheck15 : merged15 = Integer.Sparse.merge merged10 merged14 := by decide +kernel

theorem mergedZero15 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged15 x = 0 := by
  rw [mergeCheck15, Integer.Sparse.eval_merge]
  rw [mergedZero10 x h, mergedZero14 x h]
  simp only [add_zero]

theorem mergeCheck16 : merged16 = Integer.Sparse.merge merged7 merged15 := by decide +kernel

theorem mergedZero16 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged16 x = 0 := by
  rw [mergeCheck16, Integer.Sparse.eval_merge]
  rw [mergedZero7 x h, mergedZero15 x h]
  simp only [add_zero]

theorem mergeCheck17 : merged17 = Integer.Sparse.merge (Integer.Sparse.scale (-2073416072033269067580) (sourceRows 18)) (Integer.Sparse.scale (3688575213639409863840) (sourceRows 19)) := by decide +kernel

theorem mergedZero17 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged17 x = 0 := by
  rw [mergeCheck17, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck18 : merged18 = Integer.Sparse.merge (Integer.Sparse.scale (3818014240064227649040) (sourceRows 20)) (Integer.Sparse.scale (36583535641162815749115) (sourceRows 21)) := by decide +kernel

theorem mergedZero18 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged18 x = 0 := by
  rw [mergeCheck18, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck19 : merged19 = Integer.Sparse.merge merged17 merged18 := by decide +kernel

theorem mergedZero19 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged19 x = 0 := by
  rw [mergeCheck19, Integer.Sparse.eval_merge]
  rw [mergedZero17 x h, mergedZero18 x h]
  simp only [add_zero]

theorem mergeCheck20 : merged20 = Integer.Sparse.merge (Integer.Sparse.scale (-36244397189916434126790) (sourceRows 22)) (Integer.Sparse.scale (4791512187911783728380) (sourceRows 23)) := by decide +kernel

theorem mergedZero20 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged20 x = 0 := by
  rw [mergeCheck20, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck21 : merged21 = Integer.Sparse.merge (Integer.Sparse.scale (133164276814485616400190) (sourceRows 25)) (Integer.Sparse.scale (2034725479296032357100) (sourceRows 26)) := by decide +kernel

theorem mergedZero21 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged21 x = 0 := by
  rw [mergeCheck21, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck22 : merged22 = Integer.Sparse.merge (Integer.Sparse.scale (-1444966504132294742763150) (sourceRows 24)) merged21 := by decide +kernel

theorem mergedZero22 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged22 x = 0 := by
  rw [mergeCheck22, Integer.Sparse.eval_merge]
  rw [mergedZero21 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck23 : merged23 = Integer.Sparse.merge merged20 merged22 := by decide +kernel

theorem mergedZero23 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged23 x = 0 := by
  rw [mergeCheck23, Integer.Sparse.eval_merge]
  rw [mergedZero20 x h, mergedZero22 x h]
  simp only [add_zero]

theorem mergeCheck24 : merged24 = Integer.Sparse.merge merged19 merged23 := by decide +kernel

theorem mergedZero24 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged24 x = 0 := by
  rw [mergeCheck24, Integer.Sparse.eval_merge]
  rw [mergedZero19 x h, mergedZero23 x h]
  simp only [add_zero]

theorem mergeCheck25 : merged25 = Integer.Sparse.merge (Integer.Sparse.scale (5768832232953446300280) (sourceRows 27)) (Integer.Sparse.scale (1338825243982486765050) (sourceRows 28)) := by decide +kernel

theorem mergedZero25 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged25 x = 0 := by
  rw [mergeCheck25, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck26 : merged26 = Integer.Sparse.merge (Integer.Sparse.scale (45671975029187085297600) (sourceRows 30)) (Integer.Sparse.scale (-119203902074213545881600) (sourceRows 31)) := by decide +kernel

theorem mergedZero26 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged26 x = 0 := by
  rw [mergeCheck26, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck27 : merged27 = Integer.Sparse.merge (Integer.Sparse.scale (86549035204518845410620) (sourceRows 29)) merged26 := by decide +kernel

theorem mergedZero27 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged27 x = 0 := by
  rw [mergeCheck27, Integer.Sparse.eval_merge]
  rw [mergedZero26 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck28 : merged28 = Integer.Sparse.merge merged25 merged27 := by decide +kernel

theorem mergedZero28 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged28 x = 0 := by
  rw [mergeCheck28, Integer.Sparse.eval_merge]
  rw [mergedZero25 x h, mergedZero27 x h]
  simp only [add_zero]

theorem mergeCheck29 : merged29 = Integer.Sparse.merge (Integer.Sparse.scale (204501858308188674912000) (sourceRows 32)) (Integer.Sparse.scale (-178805853111320318822400) (sourceRows 33)) := by decide +kernel

theorem mergedZero29 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged29 x = 0 := by
  rw [mergeCheck29, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck30 : merged30 = Integer.Sparse.merge (Integer.Sparse.scale (-407649785906160) (sourceRows 35)) (Integer.Sparse.scale (-3223234027226903313052800) (sourceRows 36)) := by decide +kernel

theorem mergedZero30 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged30 x = 0 := by
  rw [mergeCheck30, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck31 : merged31 = Integer.Sparse.merge (Integer.Sparse.scale (59601951037106772940800) (sourceRows 34)) merged30 := by decide +kernel

theorem mergedZero31 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged31 x = 0 := by
  rw [mergeCheck31, Integer.Sparse.eval_merge]
  rw [mergedZero30 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck32 : merged32 = Integer.Sparse.merge merged29 merged31 := by decide +kernel

theorem mergedZero32 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged32 x = 0 := by
  rw [mergeCheck32, Integer.Sparse.eval_merge]
  rw [mergedZero29 x h, mergedZero31 x h]
  simp only [add_zero]

theorem mergeCheck33 : merged33 = Integer.Sparse.merge merged28 merged32 := by decide +kernel

theorem mergedZero33 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged33 x = 0 := by
  rw [mergeCheck33, Integer.Sparse.eval_merge]
  rw [mergedZero28 x h, mergedZero32 x h]
  simp only [add_zero]

theorem mergeCheck34 : merged34 = Integer.Sparse.merge merged24 merged33 := by decide +kernel

theorem mergedZero34 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged34 x = 0 := by
  rw [mergeCheck34, Integer.Sparse.eval_merge]
  rw [mergedZero24 x h, mergedZero33 x h]
  simp only [add_zero]

theorem mergeCheck35 : merged35 = Integer.Sparse.merge merged16 merged34 := by decide +kernel

theorem mergedZero35 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged35 x = 0 := by
  rw [mergeCheck35, Integer.Sparse.eval_merge]
  rw [mergedZero16 x h, mergedZero34 x h]
  simp only [add_zero]

theorem mergeCheck36 : merged36 = Integer.Sparse.merge (Integer.Sparse.scale (2854585508387673585369600) (sourceRows 37)) (Integer.Sparse.scale (-2691019580424937852809600) (sourceRows 38)) := by decide +kernel

theorem mergedZero36 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged36 x = 0 := by
  rw [mergeCheck36, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck37 : merged37 = Integer.Sparse.merge (Integer.Sparse.scale (5709171016775347170739200) (sourceRows 39)) (Integer.Sparse.scale (-3050024876543693979806400) (sourceRows 40)) := by decide +kernel

theorem mergedZero37 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged37 x = 0 := by
  rw [mergeCheck37, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck38 : merged38 = Integer.Sparse.merge merged36 merged37 := by decide +kernel

theorem mergedZero38 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged38 x = 0 := by
  rw [mergeCheck38, Integer.Sparse.eval_merge]
  rw [mergedZero36 x h, mergedZero37 x h]
  simp only [add_zero]

theorem mergeCheck39 : merged39 = Integer.Sparse.merge (Integer.Sparse.scale (2854585508387673585369600) (sourceRows 41)) (Integer.Sparse.scale (-2779726411511658315604800) (sourceRows 42)) := by decide +kernel

theorem mergedZero39 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged39 x = 0 := by
  rw [mergeCheck39, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck40 : merged40 = Integer.Sparse.merge (Integer.Sparse.scale (-2854585508387673585369600) (sourceRows 44)) (Integer.Sparse.scale (-208665130000872840120000) (sourceRows 45)) := by decide +kernel

theorem mergedZero40 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged40 x = 0 := by
  rw [mergeCheck40, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck41 : merged41 = Integer.Sparse.merge (Integer.Sparse.scale (2854585508387673585369600) (sourceRows 43)) merged40 := by decide +kernel

theorem mergedZero41 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged41 x = 0 := by
  rw [mergeCheck41, Integer.Sparse.eval_merge]
  rw [mergedZero40 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck42 : merged42 = Integer.Sparse.merge merged39 merged41 := by decide +kernel

theorem mergedZero42 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged42 x = 0 := by
  rw [mergeCheck42, Integer.Sparse.eval_merge]
  rw [mergedZero39 x h, mergedZero41 x h]
  simp only [add_zero]

theorem mergeCheck43 : merged43 = Integer.Sparse.merge merged38 merged42 := by decide +kernel

theorem mergedZero43 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged43 x = 0 := by
  rw [mergeCheck43, Integer.Sparse.eval_merge]
  rw [mergedZero38 x h, mergedZero42 x h]
  simp only [add_zero]

theorem mergeCheck44 : merged44 = Integer.Sparse.merge (Integer.Sparse.scale (-51392010393736712179200) (sourceRows 46)) (Integer.Sparse.scale (51392010393736712179200) (sourceRows 47)) := by decide +kernel

theorem mergedZero44 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged44 x = 0 := by
  rw [mergeCheck44, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck45 : merged45 = Integer.Sparse.merge (Integer.Sparse.scale (25696005196868356089600) (sourceRows 49)) (Integer.Sparse.scale (-11146219340298719766314400) (sourceRows 50)) := by decide +kernel

theorem mergedZero45 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged45 x = 0 := by
  rw [mergeCheck45, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck46 : merged46 = Integer.Sparse.merge (Integer.Sparse.scale (-51392010393736712179200) (sourceRows 48)) merged45 := by decide +kernel

theorem mergedZero46 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged46 x = 0 := by
  rw [mergeCheck46, Integer.Sparse.eval_merge]
  rw [mergedZero45 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck47 : merged47 = Integer.Sparse.merge merged44 merged46 := by decide +kernel

theorem mergedZero47 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged47 x = 0 := by
  rw [mergeCheck47, Integer.Sparse.eval_merge]
  rw [mergedZero44 x h, mergedZero46 x h]
  simp only [add_zero]

theorem mergeCheck48 : merged48 = Integer.Sparse.merge (Integer.Sparse.scale (10810178845777068964970400) (sourceRows 51)) (Integer.Sparse.scale (-10517903089971084679284000) (sourceRows 52)) := by decide +kernel

theorem mergedZero48 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged48 x = 0 := by
  rw [mergeCheck48, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck49 : merged49 = Integer.Sparse.merge (Integer.Sparse.scale (-21706654149519240645576000) (sourceRows 54)) (Integer.Sparse.scale (32430536537331206894911200) (sourceRows 55)) := by decide +kernel

theorem mergedZero49 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged49 x = 0 := by
  rw [mergeCheck49, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck50 : merged50 = Integer.Sparse.merge (Integer.Sparse.scale (10810178845777068964970400) (sourceRows 53)) merged49 := by decide +kernel

theorem mergedZero50 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged50 x = 0 := by
  rw [mergeCheck50, Integer.Sparse.eval_merge]
  rw [mergedZero49 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck51 : merged51 = Integer.Sparse.merge merged48 merged50 := by decide +kernel

theorem mergedZero51 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged51 x = 0 := by
  rw [mergeCheck51, Integer.Sparse.eval_merge]
  rw [mergedZero48 x h, mergedZero50 x h]
  simp only [add_zero]

theorem mergeCheck52 : merged52 = Integer.Sparse.merge merged47 merged51 := by decide +kernel

theorem mergedZero52 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged52 x = 0 := by
  rw [mergeCheck52, Integer.Sparse.eval_merge]
  rw [mergedZero47 x h, mergedZero51 x h]
  simp only [add_zero]

theorem mergeCheck53 : merged53 = Integer.Sparse.merge merged43 merged52 := by decide +kernel

theorem mergedZero53 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged53 x = 0 := by
  rw [mergeCheck53, Integer.Sparse.eval_merge]
  rw [mergedZero43 x h, mergedZero52 x h]
  simp only [add_zero]

theorem mergeCheck54 : merged54 = Integer.Sparse.merge (Integer.Sparse.scale (-10810178845777068964970400) (sourceRows 56)) (Integer.Sparse.scale (-54437427174917000793600) (sourceRows 57)) := by decide +kernel

theorem mergedZero54 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged54 x = 0 := by
  rw [mergeCheck54, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck55 : merged55 = Integer.Sparse.merge (Integer.Sparse.scale (-710823144931200) (sourceRows 58)) (Integer.Sparse.scale (-48238777178430999090) (sourceRows 59)) := by decide +kernel

theorem mergedZero55 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged55 x = 0 := by
  rw [mergeCheck55, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck56 : merged56 = Integer.Sparse.merge merged54 merged55 := by decide +kernel

theorem mergedZero56 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged56 x = 0 := by
  rw [mergeCheck56, Integer.Sparse.eval_merge]
  rw [mergedZero54 x h, mergedZero55 x h]
  simp only [add_zero]

theorem mergeCheck57 : merged57 = Integer.Sparse.merge (Integer.Sparse.scale (-24547628982881236011595200) (sourceRows 60)) (Integer.Sparse.scale (4590931477683218085003600) (sourceRows 61)) := by decide +kernel

theorem mergedZero57 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged57 x = 0 := by
  rw [mergeCheck57, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck58 : merged58 = Integer.Sparse.merge (Integer.Sparse.scale (3519798061675050578480400) (sourceRows 63)) (Integer.Sparse.scale (-12251348559600103182045600) (sourceRows 64)) := by decide +kernel

theorem mergedZero58 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged58 x = 0 := by
  rw [mergeCheck58, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck59 : merged59 = Integer.Sparse.merge (Integer.Sparse.scale (-4590931477683218085003600) (sourceRows 62)) merged58 := by decide +kernel

theorem mergedZero59 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged59 x = 0 := by
  rw [mergeCheck59, Integer.Sparse.eval_merge]
  rw [mergedZero58 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck60 : merged60 = Integer.Sparse.merge merged57 merged59 := by decide +kernel

theorem mergedZero60 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged60 x = 0 := by
  rw [mergeCheck60, Integer.Sparse.eval_merge]
  rw [mergedZero57 x h, mergedZero59 x h]
  simp only [add_zero]

theorem mergeCheck61 : merged61 = Integer.Sparse.merge merged56 merged60 := by decide +kernel

theorem mergedZero61 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged61 x = 0 := by
  rw [mergeCheck61, Integer.Sparse.eval_merge]
  rw [mergedZero56 x h, mergedZero60 x h]
  simp only [add_zero]

theorem mergeCheck62 : merged62 = Integer.Sparse.merge (Integer.Sparse.scale (8934172588467040341117600) (sourceRows 65)) (Integer.Sparse.scale (16992904457055239707604400) (sourceRows 66)) := by decide +kernel

theorem mergedZero62 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged62 x = 0 := by
  rw [mergeCheck62, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck63 : merged63 = Integer.Sparse.merge (Integer.Sparse.scale (-4590931477683218085003600) (sourceRows 68)) (Integer.Sparse.scale (10901199357904092151345200) (sourceRows 69)) := by decide +kernel

theorem mergedZero63 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged63 x = 0 := by
  rw [mergeCheck63, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck64 : merged64 = Integer.Sparse.merge (Integer.Sparse.scale (30037164674115244928562000) (sourceRows 67)) merged63 := by decide +kernel

theorem mergedZero64 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged64 x = 0 := by
  rw [mergeCheck64, Integer.Sparse.eval_merge]
  rw [mergedZero63 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck65 : merged65 = Integer.Sparse.merge merged62 merged64 := by decide +kernel

theorem mergedZero65 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged65 x = 0 := by
  rw [mergeCheck65, Integer.Sparse.eval_merge]
  rw [mergedZero62 x h, mergedZero64 x h]
  simp only [add_zero]

theorem mergeCheck66 : merged66 = Integer.Sparse.merge (Integer.Sparse.scale (-10683371277093970501426800) (sourceRows 70)) (Integer.Sparse.scale (3586272118745218694442000) (sourceRows 71)) := by decide +kernel

theorem mergedZero66 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged66 x = 0 := by
  rw [mergeCheck66, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck67 : merged67 = Integer.Sparse.merge (Integer.Sparse.scale (10902412848954547151204400) (sourceRows 73)) (Integer.Sparse.scale (-10902412848954547151204400) (sourceRows 74)) := by decide +kernel

theorem mergedZero67 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged67 x = 0 := by
  rw [mergeCheck67, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck68 : merged68 = Integer.Sparse.merge (Integer.Sparse.scale (-5450543161405240304511000) (sourceRows 72)) merged67 := by decide +kernel

theorem mergedZero68 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged68 x = 0 := by
  rw [mergeCheck68, Integer.Sparse.eval_merge]
  rw [mergedZero67 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck69 : merged69 = Integer.Sparse.merge merged66 merged68 := by decide +kernel

theorem mergedZero69 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged69 x = 0 := by
  rw [mergeCheck69, Integer.Sparse.eval_merge]
  rw [mergedZero66 x h, mergedZero68 x h]
  simp only [add_zero]

theorem mergeCheck70 : merged70 = Integer.Sparse.merge merged65 merged69 := by decide +kernel

theorem mergedZero70 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged70 x = 0 := by
  rw [mergeCheck70, Integer.Sparse.eval_merge]
  rw [mergedZero65 x h, mergedZero69 x h]
  simp only [add_zero]

theorem mergeCheck71 : merged71 = Integer.Sparse.merge merged61 merged70 := by decide +kernel

theorem mergedZero71 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged71 x = 0 := by
  rw [mergeCheck71, Integer.Sparse.eval_merge]
  rw [mergedZero61 x h, mergedZero70 x h]
  simp only [add_zero]

theorem mergeCheck72 : merged72 = Integer.Sparse.merge merged53 merged71 := by decide +kernel

theorem mergedZero72 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged72 x = 0 := by
  rw [mergeCheck72, Integer.Sparse.eval_merge]
  rw [mergedZero53 x h, mergedZero71 x h]
  simp only [add_zero]

theorem mergeCheck73 : merged73 = Integer.Sparse.merge merged35 merged72 := by decide +kernel

theorem mergedZero73 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged73 x = 0 := by
  rw [mergeCheck73, Integer.Sparse.eval_merge]
  rw [mergedZero35 x h, mergedZero72 x h]
  simp only [add_zero]

theorem mergeCheck74 : merged74 = Integer.Sparse.merge (Integer.Sparse.scale (5451206424477273575602200) (sourceRows 75)) (Integer.Sparse.scale (-8910172884216391725) (sourceRows 76)) := by decide +kernel

theorem mergedZero74 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged74 x = 0 := by
  rw [mergeCheck74, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck75 : merged75 = Integer.Sparse.merge (Integer.Sparse.scale (37820280421830908966025600) (sourceRows 77)) (Integer.Sparse.scale (-68916077471162890695787200) (sourceRows 78)) := by decide +kernel

theorem mergedZero75 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged75 x = 0 := by
  rw [mergeCheck75, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck76 : merged76 = Integer.Sparse.merge merged74 merged75 := by decide +kernel

theorem mergedZero76 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged76 x = 0 := by
  rw [mergeCheck76, Integer.Sparse.eval_merge]
  rw [mergedZero74 x h, mergedZero75 x h]
  simp only [add_zero]

theorem mergeCheck77 : merged77 = Integer.Sparse.merge (Integer.Sparse.scale (62465014276515965580228000) (sourceRows 79)) (Integer.Sparse.scale (-60234375337668425302164000) (sourceRows 80)) := by decide +kernel

theorem mergedZero77 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged77 x = 0 := by
  rw [mergeCheck77, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck78 : merged78 = Integer.Sparse.merge (Integer.Sparse.scale (-68926641727092644901067200) (sourceRows 82)) (Integer.Sparse.scale (140232151979281032751080000) (sourceRows 83)) := by decide +kernel

theorem mergedZero78 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged78 x = 0 := by
  rw [mergeCheck78, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck79 : merged79 = Integer.Sparse.merge (Integer.Sparse.scale (70715315543176089407412000) (sourceRows 81)) merged78 := by decide +kernel

theorem mergedZero79 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged79 x = 0 := by
  rw [mergeCheck79, Integer.Sparse.eval_merge]
  rw [mergedZero78 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck80 : merged80 = Integer.Sparse.merge merged77 merged79 := by decide +kernel

theorem mergedZero80 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged80 x = 0 := by
  rw [mergeCheck80, Integer.Sparse.eval_merge]
  rw [mergedZero77 x h, mergedZero79 x h]
  simp only [add_zero]

theorem mergeCheck81 : merged81 = Integer.Sparse.merge merged76 merged80 := by decide +kernel

theorem mergedZero81 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged81 x = 0 := by
  rw [mergeCheck81, Integer.Sparse.eval_merge]
  rw [mergedZero76 x h, mergedZero80 x h]
  simp only [add_zero]

theorem mergeCheck82 : merged82 = Integer.Sparse.merge (Integer.Sparse.scale (-137773194167703216780604800) (sourceRows 84)) (Integer.Sparse.scale (68916077471162890695787200) (sourceRows 85)) := by decide +kernel

theorem mergedZero82 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged82 x = 0 := by
  rw [mergeCheck82, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck83 : merged83 = Integer.Sparse.merge (Integer.Sparse.scale (41011709124228833894400) (sourceRows 87)) (Integer.Sparse.scale (-5542674157715893002970200) (sourceRows 88)) := by decide +kernel

theorem mergedZero83 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged83 x = 0 := by
  rw [mergeCheck83, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck84 : merged84 = Integer.Sparse.merge (Integer.Sparse.scale (28207000937231556249600) (sourceRows 86)) merged83 := by decide +kernel

theorem mergedZero84 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged84 x = 0 := by
  rw [mergeCheck84, Integer.Sparse.eval_merge]
  rw [mergedZero83 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck85 : merged85 = Integer.Sparse.merge merged82 merged84 := by decide +kernel

theorem mergedZero85 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged85 x = 0 := by
  rw [mergeCheck85, Integer.Sparse.eval_merge]
  rw [mergedZero82 x h, mergedZero84 x h]
  simp only [add_zero]

theorem mergeCheck86 : merged86 = Integer.Sparse.merge (Integer.Sparse.scale (-663263072033271091200) (sourceRows 89)) (Integer.Sparse.scale (663263072033271091200) (sourceRows 90)) := by decide +kernel

theorem mergedZero86 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged86 x = 0 := by
  rw [mergeCheck86, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck87 : merged87 = Integer.Sparse.merge (Integer.Sparse.scale (-589639716388099951560) (sourceRows 92)) (Integer.Sparse.scale (175505367836561220360) (sourceRows 93)) := by decide +kernel

theorem mergedZero87 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged87 x = 0 := by
  rw [mergeCheck87, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck88 : merged88 = Integer.Sparse.merge (Integer.Sparse.scale (1337936065263634137840) (sourceRows 91)) merged87 := by decide +kernel

theorem mergedZero88 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged88 x = 0 := by
  rw [mergeCheck88, Integer.Sparse.eval_merge]
  rw [mergedZero87 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck89 : merged89 = Integer.Sparse.merge merged86 merged88 := by decide +kernel

theorem mergedZero89 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged89 x = 0 := by
  rw [mergeCheck89, Integer.Sparse.eval_merge]
  rw [mergedZero86 x h, mergedZero88 x h]
  simp only [add_zero]

theorem mergeCheck90 : merged90 = Integer.Sparse.merge merged85 merged89 := by decide +kernel

theorem mergedZero90 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged90 x = 0 := by
  rw [mergeCheck90, Integer.Sparse.eval_merge]
  rw [mergedZero85 x h, mergedZero89 x h]
  simp only [add_zero]

theorem mergeCheck91 : merged91 = Integer.Sparse.merge merged81 merged90 := by decide +kernel

theorem mergedZero91 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged91 x = 0 := by
  rw [mergeCheck91, Integer.Sparse.eval_merge]
  rw [mergedZero81 x h, mergedZero90 x h]
  simp only [add_zero]

theorem mergeCheck92 : merged92 = Integer.Sparse.merge (Integer.Sparse.scale (-56877799073448039007860) (sourceRows 94)) (Integer.Sparse.scale (-3155011372683319285483200) (sourceRows 95)) := by decide +kernel

theorem mergedZero92 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged92 x = 0 := by
  rw [mergeCheck92, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck93 : merged93 = Integer.Sparse.merge (Integer.Sparse.scale (6125495253300791088361200) (sourceRows 96)) (Integer.Sparse.scale (40356737253047540850) (sourceRows 97)) := by decide +kernel

theorem mergedZero93 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged93 x = 0 := by
  rw [mergeCheck93, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck94 : merged94 = Integer.Sparse.merge merged92 merged93 := by decide +kernel

theorem mergedZero94 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged94 x = 0 := by
  rw [mergeCheck94, Integer.Sparse.eval_merge]
  rw [mergedZero92 x h, mergedZero93 x h]
  simp only [add_zero]

theorem mergeCheck95 : merged95 = Integer.Sparse.merge (Integer.Sparse.scale (41493697874256176430) (sourceRows 98)) (Integer.Sparse.scale (-6022622471620608000) (sourceRows 99)) := by decide +kernel

theorem mergedZero95 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged95 x = 0 := by
  rw [mergeCheck95, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck96 : merged96 = Integer.Sparse.merge (Integer.Sparse.scale (-20304430700002949850) (sourceRows 101)) (Integer.Sparse.scale (5377195335469226359204800) (sourceRows 102)) := by decide +kernel

theorem mergedZero96 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged96 x = 0 := by
  rw [mergeCheck96, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck97 : merged97 = Integer.Sparse.merge (Integer.Sparse.scale (1039814193241905433800) (sourceRows 100)) merged96 := by decide +kernel

theorem mergedZero97 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged97 x = 0 := by
  rw [mergeCheck97, Integer.Sparse.eval_merge]
  rw [mergedZero96 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck98 : merged98 = Integer.Sparse.merge merged95 merged97 := by decide +kernel

theorem mergedZero98 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged98 x = 0 := by
  rw [mergeCheck98, Integer.Sparse.eval_merge]
  rw [mergedZero95 x h, mergedZero97 x h]
  simp only [add_zero]

theorem mergeCheck99 : merged99 = Integer.Sparse.merge merged94 merged98 := by decide +kernel

theorem mergedZero99 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged99 x = 0 := by
  rw [mergeCheck99, Integer.Sparse.eval_merge]
  rw [mergedZero94 x h, mergedZero98 x h]
  simp only [add_zero]

theorem mergeCheck100 : merged100 = Integer.Sparse.merge (Integer.Sparse.scale (-276634243526994557215200) (sourceRows 103)) (Integer.Sparse.scale (827007201276590628554400) (sourceRows 104)) := by decide +kernel

theorem mergedZero100 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged100 x = 0 := by
  rw [mergeCheck100, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck101 : merged101 = Integer.Sparse.merge (Integer.Sparse.scale (275140773281033470188000) (sourceRows 106)) (Integer.Sparse.scale (-235022837585087810815200) (sourceRows 107)) := by decide +kernel

theorem mergedZero101 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged101 x = 0 := by
  rw [mergeCheck101, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck102 : merged102 = Integer.Sparse.merge (Integer.Sparse.scale (-631171747232298670053600) (sourceRows 105)) merged101 := by decide +kernel

theorem mergedZero102 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged102 x = 0 := by
  rw [mergeCheck102, Integer.Sparse.eval_merge]
  rw [mergedZero101 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck103 : merged103 = Integer.Sparse.merge merged100 merged102 := by decide +kernel

theorem mergedZero103 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged103 x = 0 := by
  rw [mergeCheck103, Integer.Sparse.eval_merge]
  rw [mergedZero100 x h, mergedZero102 x h]
  simp only [add_zero]

theorem mergeCheck104 : merged104 = Integer.Sparse.merge (Integer.Sparse.scale (191776656744334315332000) (sourceRows 108)) (Integer.Sparse.scale (-3432002413967769600) (sourceRows 109)) := by decide +kernel

theorem mergedZero104 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged104 x = 0 := by
  rw [mergeCheck104, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck105 : merged105 = Integer.Sparse.merge (Integer.Sparse.scale (-106205701875159161100) (sourceRows 111)) (Integer.Sparse.scale (-135560373450244870176000) (sourceRows 112)) := by decide +kernel

theorem mergedZero105 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged105 x = 0 := by
  rw [mergeCheck105, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck106 : merged106 = Integer.Sparse.merge (Integer.Sparse.scale (50227179561885312000) (sourceRows 110)) merged105 := by decide +kernel

theorem mergedZero106 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged106 x = 0 := by
  rw [mergeCheck106, Integer.Sparse.eval_merge]
  rw [mergedZero105 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck107 : merged107 = Integer.Sparse.merge merged104 merged106 := by decide +kernel

theorem mergedZero107 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged107 x = 0 := by
  rw [mergeCheck107, Integer.Sparse.eval_merge]
  rw [mergedZero104 x h, mergedZero106 x h]
  simp only [add_zero]

theorem mergeCheck108 : merged108 = Integer.Sparse.merge merged103 merged107 := by decide +kernel

theorem mergedZero108 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged108 x = 0 := by
  rw [mergeCheck108, Integer.Sparse.eval_merge]
  rw [mergedZero103 x h, mergedZero107 x h]
  simp only [add_zero]

theorem mergeCheck109 : merged109 = Integer.Sparse.merge merged99 merged108 := by decide +kernel

theorem mergedZero109 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged109 x = 0 := by
  rw [mergeCheck109, Integer.Sparse.eval_merge]
  rw [mergedZero99 x h, mergedZero108 x h]
  simp only [add_zero]

theorem mergeCheck110 : merged110 = Integer.Sparse.merge merged91 merged109 := by decide +kernel

theorem mergedZero110 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged110 x = 0 := by
  rw [mergeCheck110, Integer.Sparse.eval_merge]
  rw [mergedZero91 x h, mergedZero109 x h]
  simp only [add_zero]

theorem mergeCheck111 : merged111 = Integer.Sparse.merge (Integer.Sparse.scale (2056590515301578970) (sourceRows 113)) (Integer.Sparse.scale (2055425655797197530) (sourceRows 114)) := by decide +kernel

theorem mergedZero111 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged111 x = 0 := by
  rw [mergeCheck111, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck112 : merged112 = Integer.Sparse.merge (Integer.Sparse.scale (302078102370508800) (sourceRows 115)) (Integer.Sparse.scale (-7470330615398619620505) (sourceRows 116)) := by decide +kernel

theorem mergedZero112 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged112 x = 0 := by
  rw [mergeCheck112, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck113 : merged113 = Integer.Sparse.merge merged111 merged112 := by decide +kernel

theorem mergedZero113 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged113 x = 0 := by
  rw [mergeCheck113, Integer.Sparse.eval_merge]
  rw [mergedZero111 x h, mergedZero112 x h]
  simp only [add_zero]

theorem mergeCheck114 : merged114 = Integer.Sparse.merge (Integer.Sparse.scale (36774079167017780595) (sourceRows 117)) (Integer.Sparse.scale (10829845999793383805768400) (sourceRows 118)) := by decide +kernel

theorem mergedZero114 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged114 x = 0 := by
  rw [mergeCheck114, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck115 : merged115 = Integer.Sparse.merge (Integer.Sparse.scale (-29578005441505959409843200) (sourceRows 120)) (Integer.Sparse.scale (25902720496852763063623200) (sourceRows 121)) := by decide +kernel

theorem mergedZero115 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged115 x = 0 := by
  rw [mergeCheck115, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck116 : merged116 = Integer.Sparse.merge (Integer.Sparse.scale (16121856549096124184937600) (sourceRows 119)) merged115 := by decide +kernel

theorem mergedZero116 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged116 x = 0 := by
  rw [mergeCheck116, Integer.Sparse.eval_merge]
  rw [mergedZero115 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck117 : merged117 = Integer.Sparse.merge merged114 merged116 := by decide +kernel

theorem mergedZero117 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged117 x = 0 := by
  rw [mergeCheck117, Integer.Sparse.eval_merge]
  rw [mergedZero114 x h, mergedZero116 x h]
  simp only [add_zero]

theorem mergeCheck118 : merged118 = Integer.Sparse.merge merged113 merged117 := by decide +kernel

theorem mergedZero118 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged118 x = 0 := by
  rw [mergeCheck118, Integer.Sparse.eval_merge]
  rw [mergedZero113 x h, mergedZero117 x h]
  simp only [add_zero]

theorem mergeCheck119 : merged119 = Integer.Sparse.merge (Integer.Sparse.scale (-32586721972233053390539200) (sourceRows 122)) (Integer.Sparse.scale (32191887820293546646694400) (sourceRows 123)) := by decide +kernel

theorem mergedZero119 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged119 x = 0 := by
  rw [mergeCheck119, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck120 : merged120 = Integer.Sparse.merge (Integer.Sparse.scale (-760335186852391409280) (sourceRows 125)) (Integer.Sparse.scale (29031065994535819200) (sourceRows 126)) := by decide +kernel

theorem mergedZero120 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged120 x = 0 := by
  rw [mergeCheck120, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck121 : merged121 = Integer.Sparse.merge (Integer.Sparse.scale (-10749480611137745875902000) (sourceRows 124)) merged120 := by decide +kernel

theorem mergedZero121 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged121 x = 0 := by
  rw [mergeCheck121, Integer.Sparse.eval_merge]
  rw [mergedZero120 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck122 : merged122 = Integer.Sparse.merge merged119 merged121 := by decide +kernel

theorem mergedZero122 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged122 x = 0 := by
  rw [mergeCheck122, Integer.Sparse.eval_merge]
  rw [mergedZero119 x h, mergedZero121 x h]
  simp only [add_zero]

theorem mergeCheck123 : merged123 = Integer.Sparse.merge (Integer.Sparse.scale (123497840223589994400) (sourceRows 127)) (Integer.Sparse.scale (213155350991057446876800) (sourceRows 128)) := by decide +kernel

theorem mergedZero123 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged123 x = 0 := by
  rw [mergeCheck123, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck124 : merged124 = Integer.Sparse.merge (Integer.Sparse.scale (-243874236366732698919360) (sourceRows 130)) (Integer.Sparse.scale (21395805339215811772800) (sourceRows 131)) := by decide +kernel

theorem mergedZero124 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged124 x = 0 := by
  rw [mergeCheck124, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck125 : merged125 = Integer.Sparse.merge (Integer.Sparse.scale (11820688164378132480000) (sourceRows 129)) merged124 := by decide +kernel

theorem mergedZero125 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged125 x = 0 := by
  rw [mergeCheck125, Integer.Sparse.eval_merge]
  rw [mergedZero124 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck126 : merged126 = Integer.Sparse.merge merged123 merged125 := by decide +kernel

theorem mergedZero126 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged126 x = 0 := by
  rw [mergeCheck126, Integer.Sparse.eval_merge]
  rw [mergedZero123 x h, mergedZero125 x h]
  simp only [add_zero]

theorem mergeCheck127 : merged127 = Integer.Sparse.merge merged122 merged126 := by decide +kernel

theorem mergedZero127 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged127 x = 0 := by
  rw [mergeCheck127, Integer.Sparse.eval_merge]
  rw [mergedZero122 x h, mergedZero126 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck128 : merged128 = Integer.Sparse.merge merged118 merged127 := by decide +kernel

theorem mergedZero128 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged128 x = 0 := by
  rw [mergeCheck128, Integer.Sparse.eval_merge]
  rw [mergedZero118 x h, mergedZero127 x h]
  simp only [add_zero]

theorem mergeCheck129 : merged129 = Integer.Sparse.merge (Integer.Sparse.scale (-697947459009790186184400) (sourceRows 132)) (Integer.Sparse.scale (10823112331835798658283200) (sourceRows 133)) := by decide +kernel

theorem mergedZero129 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged129 x = 0 := by
  rw [mergeCheck129, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck130 : merged130 = Integer.Sparse.merge (Integer.Sparse.scale (276320629509039176443200) (sourceRows 134)) (Integer.Sparse.scale (-510597576316837483488000) (sourceRows 135)) := by decide +kernel

theorem mergedZero130 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged130 x = 0 := by
  rw [mergeCheck130, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck131 : merged131 = Integer.Sparse.merge merged129 merged130 := by decide +kernel

theorem mergedZero131 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged131 x = 0 := by
  rw [mergeCheck131, Integer.Sparse.eval_merge]
  rw [mergedZero129 x h, mergedZero130 x h]
  simp only [add_zero]

theorem mergeCheck132 : merged132 = Integer.Sparse.merge (Integer.Sparse.scale (543955438799684169753600) (sourceRows 136)) (Integer.Sparse.scale (-1098621558988800) (sourceRows 137)) := by decide +kernel

theorem mergedZero132 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged132 x = 0 := by
  rw [mergeCheck132, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck133 : merged133 = Integer.Sparse.merge (Integer.Sparse.scale (-30500965774566604800) (sourceRows 139)) (Integer.Sparse.scale (532419261013440231480) (sourceRows 140)) := by decide +kernel

theorem mergedZero133 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged133 x = 0 := by
  rw [mergeCheck133, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck134 : merged134 = Integer.Sparse.merge (Integer.Sparse.scale (3453186896535600) (sourceRows 138)) merged133 := by decide +kernel

theorem mergedZero134 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged134 x = 0 := by
  rw [mergeCheck134, Integer.Sparse.eval_merge]
  rw [mergedZero133 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck135 : merged135 = Integer.Sparse.merge merged132 merged134 := by decide +kernel

theorem mergedZero135 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged135 x = 0 := by
  rw [mergeCheck135, Integer.Sparse.eval_merge]
  rw [mergedZero132 x h, mergedZero134 x h]
  simp only [add_zero]

theorem mergeCheck136 : merged136 = Integer.Sparse.merge merged131 merged135 := by decide +kernel

theorem mergedZero136 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged136 x = 0 := by
  rw [mergeCheck136, Integer.Sparse.eval_merge]
  rw [mergedZero131 x h, mergedZero135 x h]
  simp only [add_zero]

theorem mergeCheck137 : merged137 = Integer.Sparse.merge (Integer.Sparse.scale (-4889414981608911069120) (sourceRows 141)) (Integer.Sparse.scale (-110144495008072704211200) (sourceRows 142)) := by decide +kernel

theorem mergedZero137 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged137 x = 0 := by
  rw [mergeCheck137, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck138 : merged138 = Integer.Sparse.merge (Integer.Sparse.scale (-21207577149439756768980) (sourceRows 144)) (Integer.Sparse.scale (-7423795056161271973046400) (sourceRows 145)) := by decide +kernel

theorem mergedZero138 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged138 x = 0 := by
  rw [mergeCheck138, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck139 : merged139 = Integer.Sparse.merge (Integer.Sparse.scale (-167341244175951824160) (sourceRows 143)) merged138 := by decide +kernel

theorem mergedZero139 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged139 x = 0 := by
  rw [mergeCheck139, Integer.Sparse.eval_merge]
  rw [mergedZero138 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck140 : merged140 = Integer.Sparse.merge merged137 merged139 := by decide +kernel

theorem mergedZero140 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged140 x = 0 := by
  rw [mergeCheck140, Integer.Sparse.eval_merge]
  rw [mergedZero137 x h, mergedZero139 x h]
  simp only [add_zero]

theorem mergeCheck141 : merged141 = Integer.Sparse.merge (Integer.Sparse.scale (-7362721177462020157804800) (sourceRows 146)) (Integer.Sparse.scale (-7330281164613553714545600) (sourceRows 147)) := by decide +kernel

theorem mergedZero141 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged141 x = 0 := by
  rw [mergeCheck141, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck142 : merged142 = Integer.Sparse.merge (Integer.Sparse.scale (-22022679368690087070816000) (sourceRows 149)) (Integer.Sparse.scale (529099463531994014318400) (sourceRows 150)) := by decide +kernel

theorem mergedZero142 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged142 x = 0 := by
  rw [mergeCheck142, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck143 : merged143 = Integer.Sparse.merge (Integer.Sparse.scale (-215354127307235623660800) (sourceRows 148)) merged142 := by decide +kernel

theorem mergedZero143 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged143 x = 0 := by
  rw [mergeCheck143, Integer.Sparse.eval_merge]
  rw [mergedZero142 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck144 : merged144 = Integer.Sparse.merge merged141 merged143 := by decide +kernel

theorem mergedZero144 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged144 x = 0 := by
  rw [mergeCheck144, Integer.Sparse.eval_merge]
  rw [mergedZero141 x h, mergedZero143 x h]
  simp only [add_zero]

theorem mergeCheck145 : merged145 = Integer.Sparse.merge merged140 merged144 := by decide +kernel

theorem mergedZero145 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged145 x = 0 := by
  rw [mergeCheck145, Integer.Sparse.eval_merge]
  rw [mergedZero140 x h, mergedZero144 x h]
  simp only [add_zero]

theorem mergeCheck146 : merged146 = Integer.Sparse.merge merged136 merged145 := by decide +kernel

theorem mergedZero146 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged146 x = 0 := by
  rw [mergeCheck146, Integer.Sparse.eval_merge]
  rw [mergedZero136 x h, mergedZero145 x h]
  simp only [add_zero]

theorem mergeCheck147 : merged147 = Integer.Sparse.merge merged128 merged146 := by decide +kernel

theorem mergedZero147 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged147 x = 0 := by
  rw [mergeCheck147, Integer.Sparse.eval_merge]
  rw [mergedZero128 x h, mergedZero146 x h]
  simp only [add_zero]

theorem mergeCheck148 : merged148 = Integer.Sparse.merge merged110 merged147 := by decide +kernel

theorem mergedZero148 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged148 x = 0 := by
  rw [mergeCheck148, Integer.Sparse.eval_merge]
  rw [mergedZero110 x h, mergedZero147 x h]
  simp only [add_zero]

theorem mergeCheck149 : merged149 = Integer.Sparse.merge merged73 merged148 := by decide +kernel

theorem mergedZero149 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged149 x = 0 := by
  rw [mergeCheck149, Integer.Sparse.eval_merge]
  rw [mergedZero73 x h, mergedZero148 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck301 : merged301 = Integer.Sparse.merge merged149 merged300 := by decide +kernel

theorem mergedZero301 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged301 x = 0 := by
  rw [mergeCheck301, Integer.Sparse.eval_merge]
  rw [mergedZero149 x h, mergedZero300_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck604 : merged604 = Integer.Sparse.merge merged301 merged603 := by decide +kernel

theorem mergedZero604 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged604 x = 0 := by
  rw [mergeCheck604, Integer.Sparse.eval_merge]
  rw [mergedZero301 x h, mergedZero603_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck755 : merged755 = Integer.Sparse.merge (Integer.Sparse.scale (-57729156710400) (sourceRows 757)) (Integer.Sparse.scale (64216586769710817960) (sourceRows 758)) := by decide +kernel

theorem mergedZero755 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged755 x = 0 := by
  rw [mergeCheck755, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck756 : merged756 = Integer.Sparse.merge (Integer.Sparse.scale (739989612068357280) (sourceRows 759)) (Integer.Sparse.scale (-1427496291517779291816000) (sourceRows 760)) := by decide +kernel

theorem mergedZero756 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged756 x = 0 := by
  rw [mergeCheck756, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck757 : merged757 = Integer.Sparse.merge merged755 merged756 := by decide +kernel

theorem mergedZero757 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged757 x = 0 := by
  rw [mergeCheck757, Integer.Sparse.eval_merge]
  rw [mergedZero755 x h, mergedZero756 x h]
  simp only [add_zero]

theorem mergeCheck758 : merged758 = Integer.Sparse.merge (Integer.Sparse.scale (1717180672935045489595200) (sourceRows 761)) (Integer.Sparse.scale (-2793627358584361777396800) (sourceRows 762)) := by decide +kernel

theorem mergedZero758 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged758 x = 0 := by
  rw [mergeCheck758, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck759 : merged759 = Integer.Sparse.merge (Integer.Sparse.scale (-1795826864749266295329600) (sourceRows 764)) (Integer.Sparse.scale (1714527620646912405230400) (sourceRows 765)) := by decide +kernel

theorem mergedZero759 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged759 x = 0 := by
  rw [mergeCheck759, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck760 : merged760 = Integer.Sparse.merge (Integer.Sparse.scale (2014211120045932748001600) (sourceRows 763)) merged759 := by decide +kernel

theorem mergedZero760 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged760 x = 0 := by
  rw [mergeCheck760, Integer.Sparse.eval_merge]
  rw [mergedZero759 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck761 : merged761 = Integer.Sparse.merge merged758 merged760 := by decide +kernel

theorem mergedZero761 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged761 x = 0 := by
  rw [mergeCheck761, Integer.Sparse.eval_merge]
  rw [mergedZero758 x h, mergedZero760 x h]
  simp only [add_zero]

theorem mergeCheck762 : merged762 = Integer.Sparse.merge merged757 merged761 := by decide +kernel

theorem mergedZero762 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged762 x = 0 := by
  rw [mergeCheck762, Integer.Sparse.eval_merge]
  rw [mergedZero757 x h, mergedZero761 x h]
  simp only [add_zero]

theorem mergeCheck763 : merged763 = Integer.Sparse.merge (Integer.Sparse.scale (-2035776663405588760372800) (sourceRows 766)) (Integer.Sparse.scale (748570019826589334337600) (sourceRows 767)) := by decide +kernel

theorem mergedZero763 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged763 x = 0 := by
  rw [mergeCheck763, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck764 : merged764 = Integer.Sparse.merge (Integer.Sparse.scale (50250788234640) (sourceRows 769)) (Integer.Sparse.scale (8486714658042030763382400) (sourceRows 770)) := by decide +kernel

theorem mergedZero764 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged764 x = 0 := by
  rw [mergeCheck764, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck765 : merged765 = Integer.Sparse.merge (Integer.Sparse.scale (-1715854146790978947412800) (sourceRows 768)) merged764 := by decide +kernel

theorem mergedZero765 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged765 x = 0 := by
  rw [mergeCheck765, Integer.Sparse.eval_merge]
  rw [mergedZero764 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck766 : merged766 = Integer.Sparse.merge merged763 merged765 := by decide +kernel

theorem mergedZero766 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged766 x = 0 := by
  rw [mergeCheck766, Integer.Sparse.eval_merge]
  rw [mergedZero763 x h, mergedZero765 x h]
  simp only [add_zero]

theorem mergeCheck767 : merged767 = Integer.Sparse.merge (Integer.Sparse.scale (116076446822423192716800) (sourceRows 771)) (Integer.Sparse.scale (-678514008163164503097600) (sourceRows 772)) := by decide +kernel

theorem mergedZero767 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged767 x = 0 := by
  rw [mergeCheck767, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck768 : merged768 = Integer.Sparse.merge (Integer.Sparse.scale (-2886617060888868479692800) (sourceRows 774)) (Integer.Sparse.scale (116076446822423192716800) (sourceRows 775)) := by decide +kernel

theorem mergedZero768 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged768 x = 0 := by
  rw [mergeCheck768, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck769 : merged769 = Integer.Sparse.merge (Integer.Sparse.scale (116076446822423192716800) (sourceRows 773)) merged768 := by decide +kernel

theorem mergedZero769 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged769 x = 0 := by
  rw [mergeCheck769, Integer.Sparse.eval_merge]
  rw [mergedZero768 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck770 : merged770 = Integer.Sparse.merge merged767 merged769 := by decide +kernel

theorem mergedZero770 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged770 x = 0 := by
  rw [mergeCheck770, Integer.Sparse.eval_merge]
  rw [mergedZero767 x h, mergedZero769 x h]
  simp only [add_zero]

theorem mergeCheck771 : merged771 = Integer.Sparse.merge merged766 merged770 := by decide +kernel

theorem mergedZero771 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged771 x = 0 := by
  rw [mergeCheck771, Integer.Sparse.eval_merge]
  rw [mergedZero766 x h, mergedZero770 x h]
  simp only [add_zero]

theorem mergeCheck772 : merged772 = Integer.Sparse.merge merged762 merged771 := by decide +kernel

theorem mergedZero772 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged772 x = 0 := by
  rw [mergeCheck772, Integer.Sparse.eval_merge]
  rw [mergedZero762 x h, mergedZero771 x h]
  simp only [add_zero]

theorem mergeCheck773 : merged773 = Integer.Sparse.merge (Integer.Sparse.scale (-116076446822423192716800) (sourceRows 776)) (Integer.Sparse.scale (-871557627649268029881600) (sourceRows 777)) := by decide +kernel

theorem mergedZero773 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged773 x = 0 := by
  rw [mergeCheck773, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck774 : merged774 = Integer.Sparse.merge (Integer.Sparse.scale (-116076446822423192716800) (sourceRows 778)) (Integer.Sparse.scale (-2119502840021280) (sourceRows 779)) := by decide +kernel

theorem mergedZero774 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged774 x = 0 := by
  rw [mergeCheck774, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck775 : merged775 = Integer.Sparse.merge merged773 merged774 := by decide +kernel

theorem mergedZero775 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged775 x = 0 := by
  rw [mergeCheck775, Integer.Sparse.eval_merge]
  rw [mergedZero773 x h, mergedZero774 x h]
  simp only [add_zero]

theorem mergeCheck776 : merged776 = Integer.Sparse.merge (Integer.Sparse.scale (283186915310880) (sourceRows 780)) (Integer.Sparse.scale (-1656330741190097524339200) (sourceRows 781)) := by decide +kernel

theorem mergedZero776 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged776 x = 0 := by
  rw [mergeCheck776, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck777 : merged777 = Integer.Sparse.merge (Integer.Sparse.scale (496458637580144062252800) (sourceRows 783)) (Integer.Sparse.scale (743754796142823986572800) (sourceRows 784)) := by decide +kernel

theorem mergedZero777 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged777 x = 0 := by
  rw [mergeCheck777, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck778 : merged778 = Integer.Sparse.merge (Integer.Sparse.scale (-743754796142823986572800) (sourceRows 782)) merged777 := by decide +kernel

theorem mergedZero778 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged778 x = 0 := by
  rw [mergeCheck778, Integer.Sparse.eval_merge]
  rw [mergedZero777 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck779 : merged779 = Integer.Sparse.merge merged776 merged778 := by decide +kernel

theorem mergedZero779 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged779 x = 0 := by
  rw [mergeCheck779, Integer.Sparse.eval_merge]
  rw [mergedZero776 x h, mergedZero778 x h]
  simp only [add_zero]

theorem mergeCheck780 : merged780 = Integer.Sparse.merge merged775 merged779 := by decide +kernel

theorem mergedZero780 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged780 x = 0 := by
  rw [mergeCheck780, Integer.Sparse.eval_merge]
  rw [mergedZero775 x h, mergedZero779 x h]
  simp only [add_zero]

theorem mergeCheck781 : merged781 = Integer.Sparse.merge (Integer.Sparse.scale (-743754796142823986572800) (sourceRows 785)) (Integer.Sparse.scale (1059751420010640) (sourceRows 786)) := by decide +kernel

theorem mergedZero781 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged781 x = 0 := by
  rw [mergeCheck781, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck782 : merged782 = Integer.Sparse.merge (Integer.Sparse.scale (2369186533253541568140) (sourceRows 788)) (Integer.Sparse.scale (-74351769367183523460) (sourceRows 789)) := by decide +kernel

theorem mergedZero782 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged782 x = 0 := by
  rw [mergeCheck782, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck783 : merged783 = Integer.Sparse.merge (Integer.Sparse.scale (-5646747569298179400) (sourceRows 787)) merged782 := by decide +kernel

theorem mergedZero783 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged783 x = 0 := by
  rw [mergeCheck783, Integer.Sparse.eval_merge]
  rw [mergedZero782 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck784 : merged784 = Integer.Sparse.merge merged781 merged783 := by decide +kernel

theorem mergedZero784 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged784 x = 0 := by
  rw [mergeCheck784, Integer.Sparse.eval_merge]
  rw [mergedZero781 x h, mergedZero783 x h]
  simp only [add_zero]

theorem mergeCheck785 : merged785 = Integer.Sparse.merge (Integer.Sparse.scale (254859934588901554080) (sourceRows 790)) (Integer.Sparse.scale (-66185566486379151840) (sourceRows 791)) := by decide +kernel

theorem mergedZero785 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged785 x = 0 := by
  rw [mergeCheck785, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck786 : merged786 = Integer.Sparse.merge (Integer.Sparse.scale (10461563036286269880) (sourceRows 793)) (Integer.Sparse.scale (3663161708338778808960) (sourceRows 794)) := by decide +kernel

theorem mergedZero786 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged786 x = 0 := by
  rw [mergeCheck786, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck787 : merged787 = Integer.Sparse.merge (Integer.Sparse.scale (-847524330056999700630) (sourceRows 792)) merged786 := by decide +kernel

theorem mergedZero787 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged787 x = 0 := by
  rw [mergeCheck787, Integer.Sparse.eval_merge]
  rw [mergedZero786 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck788 : merged788 = Integer.Sparse.merge merged785 merged787 := by decide +kernel

theorem mergedZero788 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged788 x = 0 := by
  rw [mergeCheck788, Integer.Sparse.eval_merge]
  rw [mergedZero785 x h, mergedZero787 x h]
  simp only [add_zero]

theorem mergeCheck789 : merged789 = Integer.Sparse.merge merged784 merged788 := by decide +kernel

theorem mergedZero789 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged789 x = 0 := by
  rw [mergeCheck789, Integer.Sparse.eval_merge]
  rw [mergedZero784 x h, mergedZero788 x h]
  simp only [add_zero]

theorem mergeCheck790 : merged790 = Integer.Sparse.merge merged780 merged789 := by decide +kernel

theorem mergedZero790 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged790 x = 0 := by
  rw [mergeCheck790, Integer.Sparse.eval_merge]
  rw [mergedZero780 x h, mergedZero789 x h]
  simp only [add_zero]

theorem mergeCheck791 : merged791 = Integer.Sparse.merge merged772 merged790 := by decide +kernel

theorem mergedZero791 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged791 x = 0 := by
  rw [mergeCheck791, Integer.Sparse.eval_merge]
  rw [mergedZero772 x h, mergedZero790 x h]
  simp only [add_zero]

theorem mergeCheck792 : merged792 = Integer.Sparse.merge (Integer.Sparse.scale (95795958738295814880) (sourceRows 795)) (Integer.Sparse.scale (-614976926798867976000) (sourceRows 796)) := by decide +kernel

theorem mergedZero792 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged792 x = 0 := by
  rw [mergeCheck792, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck793 : merged793 = Integer.Sparse.merge (Integer.Sparse.scale (-13530486600895137300) (sourceRows 797)) (Integer.Sparse.scale (7630465002984623521680) (sourceRows 798)) := by decide +kernel

theorem mergedZero793 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged793 x = 0 := by
  rw [mergeCheck793, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck794 : merged794 = Integer.Sparse.merge merged792 merged793 := by decide +kernel

theorem mergedZero794 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged794 x = 0 := by
  rw [mergeCheck794, Integer.Sparse.eval_merge]
  rw [mergedZero792 x h, mergedZero793 x h]
  simp only [add_zero]

theorem mergeCheck795 : merged795 = Integer.Sparse.merge (Integer.Sparse.scale (11746713852079520160) (sourceRows 799)) (Integer.Sparse.scale (1206392379051966694560) (sourceRows 800)) := by decide +kernel

theorem mergedZero795 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged795 x = 0 := by
  rw [mergeCheck795, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck796 : merged796 = Integer.Sparse.merge (Integer.Sparse.scale (388282252349880) (sourceRows 802)) (Integer.Sparse.scale (214627476203197610918400) (sourceRows 803)) := by decide +kernel

theorem mergedZero796 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged796 x = 0 := by
  rw [mergeCheck796, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck797 : merged797 = Integer.Sparse.merge (Integer.Sparse.scale (-69008955545537838600) (sourceRows 801)) merged796 := by decide +kernel

theorem mergedZero797 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged797 x = 0 := by
  rw [mergeCheck797, Integer.Sparse.eval_merge]
  rw [mergedZero796 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck798 : merged798 = Integer.Sparse.merge merged795 merged797 := by decide +kernel

theorem mergedZero798 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged798 x = 0 := by
  rw [mergeCheck798, Integer.Sparse.eval_merge]
  rw [mergedZero795 x h, mergedZero797 x h]
  simp only [add_zero]

theorem mergeCheck799 : merged799 = Integer.Sparse.merge merged794 merged798 := by decide +kernel

theorem mergedZero799 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged799 x = 0 := by
  rw [mergeCheck799, Integer.Sparse.eval_merge]
  rw [mergedZero794 x h, mergedZero798 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck800 : merged800 = Integer.Sparse.merge (Integer.Sparse.scale (-296859232267920) (sourceRows 804)) (Integer.Sparse.scale (195670980019200) (sourceRows 805)) := by decide +kernel

theorem mergedZero800 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged800 x = 0 := by
  rw [mergeCheck800, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck801 : merged801 = Integer.Sparse.merge (Integer.Sparse.scale (-2727980377560117444643200) (sourceRows 807)) (Integer.Sparse.scale (921124682331709685760000) (sourceRows 808)) := by decide +kernel

theorem mergedZero801 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged801 x = 0 := by
  rw [mergeCheck801, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck802 : merged802 = Integer.Sparse.merge (Integer.Sparse.scale (1326526144066542182400) (sourceRows 806)) merged801 := by decide +kernel

theorem mergedZero802 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged802 x = 0 := by
  rw [mergeCheck802, Integer.Sparse.eval_merge]
  rw [mergedZero801 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck803 : merged803 = Integer.Sparse.merge merged800 merged802 := by decide +kernel

theorem mergedZero803 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged803 x = 0 := by
  rw [mergeCheck803, Integer.Sparse.eval_merge]
  rw [mergedZero800 x h, mergedZero802 x h]
  simp only [add_zero]

theorem mergeCheck804 : merged804 = Integer.Sparse.merge (Integer.Sparse.scale (-1842272505216376066713600) (sourceRows 809)) (Integer.Sparse.scale (-1154205816317348231001600) (sourceRows 810)) := by decide +kernel

theorem mergedZero804 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged804 x = 0 := by
  rw [mergeCheck804, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck805 : merged805 = Integer.Sparse.merge (Integer.Sparse.scale (-857028321538622254425600) (sourceRows 812)) (Integer.Sparse.scale (-409886526510720) (sourceRows 813)) := by decide +kernel

theorem mergedZero805 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged805 x = 0 := by
  rw [mergeCheck805, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck806 : merged806 = Integer.Sparse.merge (Integer.Sparse.scale (-915748238468487554726400) (sourceRows 811)) merged805 := by decide +kernel

theorem mergedZero806 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged806 x = 0 := by
  rw [mergeCheck806, Integer.Sparse.eval_merge]
  rw [mergedZero805 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck807 : merged807 = Integer.Sparse.merge merged804 merged806 := by decide +kernel

theorem mergedZero807 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged807 x = 0 := by
  rw [mergeCheck807, Integer.Sparse.eval_merge]
  rw [mergedZero804 x h, mergedZero806 x h]
  simp only [add_zero]

theorem mergeCheck808 : merged808 = Integer.Sparse.merge merged803 merged807 := by decide +kernel

theorem mergedZero808 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged808 x = 0 := by
  rw [mergeCheck808, Integer.Sparse.eval_merge]
  rw [mergedZero803 x h, mergedZero807 x h]
  simp only [add_zero]

theorem mergeCheck809 : merged809 = Integer.Sparse.merge merged799 merged808 := by decide +kernel

theorem mergedZero809 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged809 x = 0 := by
  rw [mergeCheck809, Integer.Sparse.eval_merge]
  rw [mergedZero799 x h, mergedZero808 x h]
  simp only [add_zero]

theorem mergeCheck810 : merged810 = Integer.Sparse.merge (Integer.Sparse.scale (41992108552103895360) (sourceRows 814)) (Integer.Sparse.scale (-50385722691439461480) (sourceRows 815)) := by decide +kernel

theorem mergedZero810 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged810 x = 0 := by
  rw [mergeCheck810, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck811 : merged811 = Integer.Sparse.merge (Integer.Sparse.scale (28864578355200) (sourceRows 816)) (Integer.Sparse.scale (-32106068067291826860) (sourceRows 817)) := by decide +kernel

theorem mergedZero811 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged811 x = 0 := by
  rw [mergeCheck811, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck812 : merged812 = Integer.Sparse.merge merged810 merged811 := by decide +kernel

theorem mergedZero812 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged812 x = 0 := by
  rw [mergeCheck812, Integer.Sparse.eval_merge]
  rw [mergedZero810 x h, mergedZero811 x h]
  simp only [add_zero]

theorem mergeCheck813 : merged813 = Integer.Sparse.merge (Integer.Sparse.scale (-738295979548824480) (sourceRows 818)) (Integer.Sparse.scale (-57860072282562823929600) (sourceRows 819)) := by decide +kernel

theorem mergedZero813 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged813 x = 0 := by
  rw [mergeCheck813, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck814 : merged814 = Integer.Sparse.merge (Integer.Sparse.scale (-6010686259200) (sourceRows 821)) (Integer.Sparse.scale (-7134448672701153720) (sourceRows 822)) := by decide +kernel

theorem mergedZero814 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged814 x = 0 := by
  rw [mergeCheck814, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck815 : merged815 = Integer.Sparse.merge (Integer.Sparse.scale (-2080570010724100467936000) (sourceRows 820)) merged814 := by decide +kernel

theorem mergedZero815 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged815 x = 0 := by
  rw [mergeCheck815, Integer.Sparse.eval_merge]
  rw [mergedZero814 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck816 : merged816 = Integer.Sparse.merge merged813 merged815 := by decide +kernel

theorem mergedZero816 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged816 x = 0 := by
  rw [mergeCheck816, Integer.Sparse.eval_merge]
  rw [mergedZero813 x h, mergedZero815 x h]
  simp only [add_zero]

theorem mergeCheck817 : merged817 = Integer.Sparse.merge merged812 merged816 := by decide +kernel

theorem mergedZero817 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged817 x = 0 := by
  rw [mergeCheck817, Integer.Sparse.eval_merge]
  rw [mergedZero812 x h, mergedZero816 x h]
  simp only [add_zero]

theorem mergeCheck818 : merged818 = Integer.Sparse.merge (Integer.Sparse.scale (-2859337207667908800) (sourceRows 823)) (Integer.Sparse.scale (-3292924543415902311336000) (sourceRows 824)) := by decide +kernel

theorem mergedZero818 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged818 x = 0 := by
  rw [mergeCheck818, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck819 : merged819 = Integer.Sparse.merge (Integer.Sparse.scale (-413879832239725572638400) (sourceRows 826)) (Integer.Sparse.scale (-789608610526067578612800) (sourceRows 827)) := by decide +kernel

theorem mergedZero819 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged819 x = 0 := by
  rw [mergeCheck819, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck820 : merged820 = Integer.Sparse.merge (Integer.Sparse.scale (-789608610526067578612800) (sourceRows 825)) merged819 := by decide +kernel

theorem mergedZero820 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged820 x = 0 := by
  rw [mergeCheck820, Integer.Sparse.eval_merge]
  rw [mergedZero819 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck821 : merged821 = Integer.Sparse.merge merged818 merged820 := by decide +kernel

theorem mergedZero821 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged821 x = 0 := by
  rw [mergeCheck821, Integer.Sparse.eval_merge]
  rw [mergedZero818 x h, mergedZero820 x h]
  simp only [add_zero]

theorem mergeCheck822 : merged822 = Integer.Sparse.merge (Integer.Sparse.scale (1579217221052135157225600) (sourceRows 828)) (Integer.Sparse.scale (-2002514354718883849468800) (sourceRows 829)) := by decide +kernel

theorem mergedZero822 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged822 x = 0 := by
  rw [mergeCheck822, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck823 : merged823 = Integer.Sparse.merge (Integer.Sparse.scale (315634531951108896523200) (sourceRows 831)) (Integer.Sparse.scale (789608610526067578612800) (sourceRows 832)) := by decide +kernel

theorem mergedZero823 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged823 x = 0 := by
  rw [mergeCheck823, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck824 : merged824 = Integer.Sparse.merge (Integer.Sparse.scale (-1109115250400848558694400) (sourceRows 830)) merged823 := by decide +kernel

theorem mergedZero824 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged824 x = 0 := by
  rw [mergeCheck824, Integer.Sparse.eval_merge]
  rw [mergedZero823 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck825 : merged825 = Integer.Sparse.merge merged822 merged824 := by decide +kernel

theorem mergedZero825 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged825 x = 0 := by
  rw [mergeCheck825, Integer.Sparse.eval_merge]
  rw [mergedZero822 x h, mergedZero824 x h]
  simp only [add_zero]

theorem mergeCheck826 : merged826 = Integer.Sparse.merge merged821 merged825 := by decide +kernel

theorem mergedZero826 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged826 x = 0 := by
  rw [mergeCheck826, Integer.Sparse.eval_merge]
  rw [mergedZero821 x h, mergedZero825 x h]
  simp only [add_zero]

theorem mergeCheck827 : merged827 = Integer.Sparse.merge merged817 merged826 := by decide +kernel

theorem mergedZero827 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged827 x = 0 := by
  rw [mergeCheck827, Integer.Sparse.eval_merge]
  rw [mergedZero817 x h, mergedZero826 x h]
  simp only [add_zero]

theorem mergeCheck828 : merged828 = Integer.Sparse.merge merged809 merged827 := by decide +kernel

theorem mergedZero828 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged828 x = 0 := by
  rw [mergeCheck828, Integer.Sparse.eval_merge]
  rw [mergedZero809 x h, mergedZero827 x h]
  simp only [add_zero]

theorem mergeCheck829 : merged829 = Integer.Sparse.merge merged791 merged828 := by decide +kernel

theorem mergedZero829 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged829 x = 0 := by
  rw [mergeCheck829, Integer.Sparse.eval_merge]
  rw [mergedZero791 x h, mergedZero828 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck905 : merged905 = Integer.Sparse.merge merged829 merged904 := by decide +kernel

theorem mergedZero905 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged905 x = 0 := by
  rw [mergeCheck905, Integer.Sparse.eval_merge]
  rw [mergedZero829 x h, mergedZero904_e x h]
  simp only [add_zero]

theorem mergeCheck906 : merged906 = Integer.Sparse.merge merged754 merged905 := by decide +kernel

theorem mergedZero906 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged906 x = 0 := by
  rw [mergeCheck906, Integer.Sparse.eval_merge]
  rw [mergedZero754_e x h, mergedZero905 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1209 : merged1209 = Integer.Sparse.merge merged906 merged1208 := by decide +kernel

theorem mergedZero1209 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1209 x = 0 := by
  rw [mergeCheck1209, Integer.Sparse.eval_merge]
  rw [mergedZero906 x h, mergedZero1208_e x h]
  simp only [add_zero]

theorem mergeCheck1210 : merged1210 = Integer.Sparse.merge merged604 merged1209 := by decide +kernel

theorem mergedZero1210_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1210 x = 0 := by
  rw [mergeCheck1210, Integer.Sparse.eval_merge]
  rw [mergedZero604 x h, mergedZero1209 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1210_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1210_e_oai
