-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1056_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:27:08.085207+00:00
-- url     : https://prove2.me/submissions/495e0b01-09d1-40db-9bee-06b4637d1592

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E185
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck907 : merged907 = Integer.Sparse.merge (Integer.Sparse.scale (-394838639462400) (sourceRows 909)) (Integer.Sparse.scale (23766973150714905720) (sourceRows 910)) := by decide +kernel

theorem mergedZero907 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged907 x = 0 := by
  rw [mergeCheck907, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck908 : merged908 = Integer.Sparse.merge (Integer.Sparse.scale (12182630708142285300) (sourceRows 911)) (Integer.Sparse.scale (182891589135640) (sourceRows 912)) := by decide +kernel

theorem mergedZero908 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged908 x = 0 := by
  rw [mergeCheck908, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck909 : merged909 = Integer.Sparse.merge merged907 merged908 := by decide +kernel

theorem mergedZero909 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged909 x = 0 := by
  rw [mergeCheck909, Integer.Sparse.eval_merge]
  rw [mergedZero907 x h, mergedZero908 x h]
  simp only [add_zero]

theorem mergeCheck910 : merged910 = Integer.Sparse.merge (Integer.Sparse.scale (232489460833560) (sourceRows 913)) (Integer.Sparse.scale (-23858556048931046520) (sourceRows 914)) := by decide +kernel

theorem mergedZero910 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged910 x = 0 := by
  rw [mergeCheck910, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck911 : merged911 = Integer.Sparse.merge (Integer.Sparse.scale (3574706260362854400) (sourceRows 916)) (Integer.Sparse.scale (14882187374698371840) (sourceRows 917)) := by decide +kernel

theorem mergedZero911 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged911 x = 0 := by
  rw [mergeCheck911, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck912 : merged912 = Integer.Sparse.merge (Integer.Sparse.scale (15540870350020894200) (sourceRows 915)) merged911 := by decide +kernel

theorem mergedZero912 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged912 x = 0 := by
  rw [mergeCheck912, Integer.Sparse.eval_merge]
  rw [mergedZero911 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck913 : merged913 = Integer.Sparse.merge merged910 merged912 := by decide +kernel

theorem mergedZero913 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged913 x = 0 := by
  rw [mergeCheck913, Integer.Sparse.eval_merge]
  rw [mergedZero910 x h, mergedZero912 x h]
  simp only [add_zero]

theorem mergeCheck914 : merged914 = Integer.Sparse.merge merged909 merged913 := by decide +kernel

theorem mergedZero914 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged914 x = 0 := by
  rw [mergeCheck914, Integer.Sparse.eval_merge]
  rw [mergedZero909 x h, mergedZero913 x h]
  simp only [add_zero]

theorem mergeCheck915 : merged915 = Integer.Sparse.merge (Integer.Sparse.scale (-160005642783280) (sourceRows 918)) (Integer.Sparse.scale (-464978921667120) (sourceRows 919)) := by decide +kernel

theorem mergedZero915 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged915 x = 0 := by
  rw [mergeCheck915, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck916 : merged916 = Integer.Sparse.merge (Integer.Sparse.scale (-6927107237692531260) (sourceRows 920)) (Integer.Sparse.scale (32402594984665463880) (sourceRows 921)) := by decide +kernel

theorem mergedZero916 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged916 x = 0 := by
  rw [mergeCheck916, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck917 : merged917 = Integer.Sparse.merge merged915 merged916 := by decide +kernel

theorem mergedZero917 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged917 x = 0 := by
  rw [mergeCheck917, Integer.Sparse.eval_merge]
  rw [mergedZero915 x h, mergedZero916 x h]
  simp only [add_zero]

theorem mergeCheck918 : merged918 = Integer.Sparse.merge (Integer.Sparse.scale (3455421466291200) (sourceRows 922)) (Integer.Sparse.scale (-42243389416646985840) (sourceRows 923)) := by decide +kernel

theorem mergedZero918 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged918 x = 0 := by
  rw [mergeCheck918, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck919 : merged919 = Integer.Sparse.merge (Integer.Sparse.scale (6731098956082408320) (sourceRows 925)) (Integer.Sparse.scale (-1932334774807920) (sourceRows 926)) := by decide +kernel

theorem mergedZero919 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged919 x = 0 := by
  rw [mergeCheck919, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck920 : merged920 = Integer.Sparse.merge (Integer.Sparse.scale (1075781688945868800) (sourceRows 924)) merged919 := by decide +kernel

theorem mergedZero920 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged920 x = 0 := by
  rw [mergeCheck920, Integer.Sparse.eval_merge]
  rw [mergedZero919 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck921 : merged921 = Integer.Sparse.merge merged918 merged920 := by decide +kernel

theorem mergedZero921 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged921 x = 0 := by
  rw [mergeCheck921, Integer.Sparse.eval_merge]
  rw [mergedZero918 x h, mergedZero920 x h]
  simp only [add_zero]

theorem mergeCheck922 : merged922 = Integer.Sparse.merge merged917 merged921 := by decide +kernel

theorem mergedZero922 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged922 x = 0 := by
  rw [mergeCheck922, Integer.Sparse.eval_merge]
  rw [mergedZero917 x h, mergedZero921 x h]
  simp only [add_zero]

theorem mergeCheck923 : merged923 = Integer.Sparse.merge merged914 merged922 := by decide +kernel

theorem mergedZero923 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged923 x = 0 := by
  rw [mergeCheck923, Integer.Sparse.eval_merge]
  rw [mergedZero914 x h, mergedZero922 x h]
  simp only [add_zero]

theorem mergeCheck924 : merged924 = Integer.Sparse.merge (Integer.Sparse.scale (-103996859359680) (sourceRows 927)) (Integer.Sparse.scale (-4413840313688064000) (sourceRows 928)) := by decide +kernel

theorem mergedZero924 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged924 x = 0 := by
  rw [mergeCheck924, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck925 : merged925 = Integer.Sparse.merge (Integer.Sparse.scale (-23769744577770755760) (sourceRows 929)) (Integer.Sparse.scale (-115290380890208442240) (sourceRows 930)) := by decide +kernel

theorem mergedZero925 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged925 x = 0 := by
  rw [mergeCheck925, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck926 : merged926 = Integer.Sparse.merge merged924 merged925 := by decide +kernel

theorem mergedZero926 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged926 x = 0 := by
  rw [mergeCheck926, Integer.Sparse.eval_merge]
  rw [mergedZero924 x h, mergedZero925 x h]
  simp only [add_zero]

theorem mergeCheck927 : merged927 = Integer.Sparse.merge (Integer.Sparse.scale (115299673586383618080) (sourceRows 931)) (Integer.Sparse.scale (-40070416245771110640) (sourceRows 932)) := by decide +kernel

theorem mergedZero927 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged927 x = 0 := by
  rw [mergeCheck927, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck928 : merged928 = Integer.Sparse.merge (Integer.Sparse.scale (596595080417280) (sourceRows 934)) (Integer.Sparse.scale (23009653093449139320) (sourceRows 935)) := by decide +kernel

theorem mergedZero928 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged928 x = 0 := by
  rw [mergeCheck928, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck929 : merged929 = Integer.Sparse.merge (Integer.Sparse.scale (13013274322793763900) (sourceRows 933)) merged928 := by decide +kernel

theorem mergedZero929 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged929 x = 0 := by
  rw [mergeCheck929, Integer.Sparse.eval_merge]
  rw [mergedZero928 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck930 : merged930 = Integer.Sparse.merge merged927 merged929 := by decide +kernel

theorem mergedZero930 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged930 x = 0 := by
  rw [mergeCheck930, Integer.Sparse.eval_merge]
  rw [mergedZero927 x h, mergedZero929 x h]
  simp only [add_zero]

theorem mergeCheck931 : merged931 = Integer.Sparse.merge merged926 merged930 := by decide +kernel

theorem mergedZero931 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged931 x = 0 := by
  rw [mergeCheck931, Integer.Sparse.eval_merge]
  rw [mergedZero926 x h, mergedZero930 x h]
  simp only [add_zero]

theorem mergeCheck932 : merged932 = Integer.Sparse.merge (Integer.Sparse.scale (-2099869151308451880) (sourceRows 936)) (Integer.Sparse.scale (6340999830906720) (sourceRows 937)) := by decide +kernel

theorem mergedZero932 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged932 x = 0 := by
  rw [mergeCheck932, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck933 : merged933 = Integer.Sparse.merge (Integer.Sparse.scale (-5913280932428988090) (sourceRows 939)) (Integer.Sparse.scale (-5251622355270364640) (sourceRows 940)) := by decide +kernel

theorem mergedZero933 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged933 x = 0 := by
  rw [mergeCheck933, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck934 : merged934 = Integer.Sparse.merge (Integer.Sparse.scale (-2240075009468620800) (sourceRows 938)) merged933 := by decide +kernel

theorem mergedZero934 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged934 x = 0 := by
  rw [mergeCheck934, Integer.Sparse.eval_merge]
  rw [mergedZero933 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck935 : merged935 = Integer.Sparse.merge merged932 merged934 := by decide +kernel

theorem mergedZero935 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged935 x = 0 := by
  rw [mergeCheck935, Integer.Sparse.eval_merge]
  rw [mergedZero932 x h, mergedZero934 x h]
  simp only [add_zero]

theorem mergeCheck936 : merged936 = Integer.Sparse.merge (Integer.Sparse.scale (10284936214767321660) (sourceRows 941)) (Integer.Sparse.scale (-10019214895896593100) (sourceRows 942)) := by decide +kernel

theorem mergedZero936 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged936 x = 0 := by
  rw [mergeCheck936, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck937 : merged937 = Integer.Sparse.merge (Integer.Sparse.scale (4555310131543449600) (sourceRows 944)) (Integer.Sparse.scale (1595139479421290880) (sourceRows 945)) := by decide +kernel

theorem mergedZero937 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged937 x = 0 := by
  rw [mergeCheck937, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck938 : merged938 = Integer.Sparse.merge (Integer.Sparse.scale (-5251843091660252640) (sourceRows 943)) merged937 := by decide +kernel

theorem mergedZero938 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged938 x = 0 := by
  rw [mergeCheck938, Integer.Sparse.eval_merge]
  rw [mergedZero937 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck939 : merged939 = Integer.Sparse.merge merged936 merged938 := by decide +kernel

theorem mergedZero939 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged939 x = 0 := by
  rw [mergeCheck939, Integer.Sparse.eval_merge]
  rw [mergedZero936 x h, mergedZero938 x h]
  simp only [add_zero]

theorem mergeCheck940 : merged940 = Integer.Sparse.merge merged935 merged939 := by decide +kernel

theorem mergedZero940 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged940 x = 0 := by
  rw [mergeCheck940, Integer.Sparse.eval_merge]
  rw [mergedZero935 x h, mergedZero939 x h]
  simp only [add_zero]

theorem mergeCheck941 : merged941 = Integer.Sparse.merge merged931 merged940 := by decide +kernel

theorem mergedZero941 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged941 x = 0 := by
  rw [mergeCheck941, Integer.Sparse.eval_merge]
  rw [mergedZero931 x h, mergedZero940 x h]
  simp only [add_zero]

theorem mergeCheck942 : merged942 = Integer.Sparse.merge merged923 merged941 := by decide +kernel

theorem mergedZero942 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged942 x = 0 := by
  rw [mergeCheck942, Integer.Sparse.eval_merge]
  rw [mergedZero923 x h, mergedZero941 x h]
  simp only [add_zero]

theorem mergeCheck943 : merged943 = Integer.Sparse.merge (Integer.Sparse.scale (-125327049344000) (sourceRows 946)) (Integer.Sparse.scale (891750538325652384960) (sourceRows 947)) := by decide +kernel

theorem mergedZero943 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged943 x = 0 := by
  rw [mergeCheck943, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck944 : merged944 = Integer.Sparse.merge (Integer.Sparse.scale (32110620629799283740) (sourceRows 948)) (Integer.Sparse.scale (-16341904651409568) (sourceRows 949)) := by decide +kernel

theorem mergedZero944 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged944 x = 0 := by
  rw [mergeCheck944, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck945 : merged945 = Integer.Sparse.merge merged943 merged944 := by decide +kernel

theorem mergedZero945 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged945 x = 0 := by
  rw [mergeCheck945, Integer.Sparse.eval_merge]
  rw [mergedZero943 x h, mergedZero944 x h]
  simp only [add_zero]

theorem mergeCheck946 : merged946 = Integer.Sparse.merge (Integer.Sparse.scale (-17285978982041659680) (sourceRows 950)) (Integer.Sparse.scale (20980945616688434580) (sourceRows 951)) := by decide +kernel

theorem mergedZero946 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged946 x = 0 := by
  rw [mergeCheck946, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck947 : merged947 = Integer.Sparse.merge (Integer.Sparse.scale (-9864572067263692800) (sourceRows 953)) (Integer.Sparse.scale (409886526510720) (sourceRows 954)) := by decide +kernel

theorem mergedZero947 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged947 x = 0 := by
  rw [mergeCheck947, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck948 : merged948 = Integer.Sparse.merge (Integer.Sparse.scale (-5196070608925253400) (sourceRows 952)) merged947 := by decide +kernel

theorem mergedZero948 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged948 x = 0 := by
  rw [mergeCheck948, Integer.Sparse.eval_merge]
  rw [mergedZero947 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck949 : merged949 = Integer.Sparse.merge merged946 merged948 := by decide +kernel

theorem mergedZero949 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged949 x = 0 := by
  rw [mergeCheck949, Integer.Sparse.eval_merge]
  rw [mergedZero946 x h, mergedZero948 x h]
  simp only [add_zero]

theorem mergeCheck950 : merged950 = Integer.Sparse.merge merged945 merged949 := by decide +kernel

theorem mergedZero950 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged950 x = 0 := by
  rw [mergeCheck950, Integer.Sparse.eval_merge]
  rw [mergedZero945 x h, mergedZero949 x h]
  simp only [add_zero]

theorem mergeCheck951 : merged951 = Integer.Sparse.merge (Integer.Sparse.scale (64761027086355395040) (sourceRows 955)) (Integer.Sparse.scale (-110039720478625843920) (sourceRows 956)) := by decide +kernel

theorem mergedZero951 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged951 x = 0 := by
  rw [mergeCheck951, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck952 : merged952 = Integer.Sparse.merge (Integer.Sparse.scale (278640118713600) (sourceRows 958)) (Integer.Sparse.scale (-804629192451840) (sourceRows 959)) := by decide +kernel

theorem mergedZero952 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged952 x = 0 := by
  rw [mergeCheck952, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck953 : merged953 = Integer.Sparse.merge (Integer.Sparse.scale (-28679181021280512240) (sourceRows 957)) merged952 := by decide +kernel

theorem mergedZero953 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged953 x = 0 := by
  rw [mergeCheck953, Integer.Sparse.eval_merge]
  rw [mergedZero952 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck954 : merged954 = Integer.Sparse.merge merged951 merged953 := by decide +kernel

theorem mergedZero954 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged954 x = 0 := by
  rw [mergeCheck954, Integer.Sparse.eval_merge]
  rw [mergedZero951 x h, mergedZero953 x h]
  simp only [add_zero]

theorem mergeCheck955 : merged955 = Integer.Sparse.merge (Integer.Sparse.scale (38953163855840601780) (sourceRows 960)) (Integer.Sparse.scale (3378841321914777600) (sourceRows 961)) := by decide +kernel

theorem mergedZero955 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged955 x = 0 := by
  rw [mergeCheck955, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck956 : merged956 = Integer.Sparse.merge (Integer.Sparse.scale (12281041745336473200) (sourceRows 963)) (Integer.Sparse.scale (-38283606210828992580) (sourceRows 964)) := by decide +kernel

theorem mergedZero956 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged956 x = 0 := by
  rw [mergeCheck956, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck957 : merged957 = Integer.Sparse.merge (Integer.Sparse.scale (-70427906740227563100) (sourceRows 962)) merged956 := by decide +kernel

theorem mergedZero957 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged957 x = 0 := by
  rw [mergeCheck957, Integer.Sparse.eval_merge]
  rw [mergedZero956 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck958 : merged958 = Integer.Sparse.merge merged955 merged957 := by decide +kernel

theorem mergedZero958 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged958 x = 0 := by
  rw [mergeCheck958, Integer.Sparse.eval_merge]
  rw [mergedZero955 x h, mergedZero957 x h]
  simp only [add_zero]

theorem mergeCheck959 : merged959 = Integer.Sparse.merge merged954 merged958 := by decide +kernel

theorem mergedZero959 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged959 x = 0 := by
  rw [mergeCheck959, Integer.Sparse.eval_merge]
  rw [mergedZero954 x h, mergedZero958 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck960 : merged960 = Integer.Sparse.merge merged950 merged959 := by decide +kernel

theorem mergedZero960 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged960 x = 0 := by
  rw [mergeCheck960, Integer.Sparse.eval_merge]
  rw [mergedZero950 x h, mergedZero959 x h]
  simp only [add_zero]

theorem mergeCheck961 : merged961 = Integer.Sparse.merge (Integer.Sparse.scale (692749880524800) (sourceRows 965)) (Integer.Sparse.scale (21403155685635357480) (sourceRows 966)) := by decide +kernel

theorem mergedZero961 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged961 x = 0 := by
  rw [mergeCheck961, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck962 : merged962 = Integer.Sparse.merge (Integer.Sparse.scale (4711441436432673600) (sourceRows 967)) (Integer.Sparse.scale (7700999025677533800) (sourceRows 968)) := by decide +kernel

theorem mergedZero962 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged962 x = 0 := by
  rw [mergeCheck962, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck963 : merged963 = Integer.Sparse.merge merged961 merged962 := by decide +kernel

theorem mergedZero963 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged963 x = 0 := by
  rw [mergeCheck963, Integer.Sparse.eval_merge]
  rw [mergedZero961 x h, mergedZero962 x h]
  simp only [add_zero]

theorem mergeCheck964 : merged964 = Integer.Sparse.merge (Integer.Sparse.scale (-1226437147273800) (sourceRows 969)) (Integer.Sparse.scale (2602940477242279440) (sourceRows 970)) := by decide +kernel

theorem mergedZero964 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged964 x = 0 := by
  rw [mergeCheck964, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck965 : merged965 = Integer.Sparse.merge (Integer.Sparse.scale (18621375689152742520) (sourceRows 972)) (Integer.Sparse.scale (13215037253844492360) (sourceRows 973)) := by decide +kernel

theorem mergedZero965 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged965 x = 0 := by
  rw [mergeCheck965, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck966 : merged966 = Integer.Sparse.merge (Integer.Sparse.scale (-21654588488377320) (sourceRows 971)) merged965 := by decide +kernel

theorem mergedZero966 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged966 x = 0 := by
  rw [mergeCheck966, Integer.Sparse.eval_merge]
  rw [mergedZero965 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck967 : merged967 = Integer.Sparse.merge merged964 merged966 := by decide +kernel

theorem mergedZero967 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged967 x = 0 := by
  rw [mergeCheck967, Integer.Sparse.eval_merge]
  rw [mergedZero964 x h, mergedZero966 x h]
  simp only [add_zero]

theorem mergeCheck968 : merged968 = Integer.Sparse.merge merged963 merged967 := by decide +kernel

theorem mergedZero968 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged968 x = 0 := by
  rw [mergeCheck968, Integer.Sparse.eval_merge]
  rw [mergedZero963 x h, mergedZero967 x h]
  simp only [add_zero]

theorem mergeCheck969 : merged969 = Integer.Sparse.merge (Integer.Sparse.scale (1380375440717414400) (sourceRows 974)) (Integer.Sparse.scale (-4274918159073448320) (sourceRows 975)) := by decide +kernel

theorem mergedZero969 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged969 x = 0 := by
  rw [mergeCheck969, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck970 : merged970 = Integer.Sparse.merge (Integer.Sparse.scale (-7700981171444471400) (sourceRows 977)) (Integer.Sparse.scale (-2095895298235200) (sourceRows 978)) := by decide +kernel

theorem mergedZero970 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged970 x = 0 := by
  rw [mergeCheck970, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck971 : merged971 = Integer.Sparse.merge (Integer.Sparse.scale (-78774086894069498400) (sourceRows 976)) merged970 := by decide +kernel

theorem mergedZero971 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged971 x = 0 := by
  rw [mergeCheck971, Integer.Sparse.eval_merge]
  rw [mergedZero970 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck972 : merged972 = Integer.Sparse.merge merged969 merged971 := by decide +kernel

theorem mergedZero972 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged972 x = 0 := by
  rw [mergeCheck972, Integer.Sparse.eval_merge]
  rw [mergedZero969 x h, mergedZero971 x h]
  simp only [add_zero]

theorem mergeCheck973 : merged973 = Integer.Sparse.merge (Integer.Sparse.scale (-121738558950509482800) (sourceRows 979)) (Integer.Sparse.scale (-23031987284950041720) (sourceRows 980)) := by decide +kernel

theorem mergedZero973 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged973 x = 0 := by
  rw [mergeCheck973, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck974 : merged974 = Integer.Sparse.merge (Integer.Sparse.scale (78744589308937196400) (sourceRows 982)) (Integer.Sparse.scale (23190637742188280) (sourceRows 983)) := by decide +kernel

theorem mergedZero974 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged974 x = 0 := by
  rw [mergeCheck974, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck975 : merged975 = Integer.Sparse.merge (Integer.Sparse.scale (-15155216649334749960) (sourceRows 981)) merged974 := by decide +kernel

theorem mergedZero975 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged975 x = 0 := by
  rw [mergeCheck975, Integer.Sparse.eval_merge]
  rw [mergedZero974 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck976 : merged976 = Integer.Sparse.merge merged973 merged975 := by decide +kernel

theorem mergedZero976 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged976 x = 0 := by
  rw [mergeCheck976, Integer.Sparse.eval_merge]
  rw [mergedZero973 x h, mergedZero975 x h]
  simp only [add_zero]

theorem mergeCheck977 : merged977 = Integer.Sparse.merge merged972 merged976 := by decide +kernel

theorem mergedZero977 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged977 x = 0 := by
  rw [mergeCheck977, Integer.Sparse.eval_merge]
  rw [mergedZero972 x h, mergedZero976 x h]
  simp only [add_zero]

theorem mergeCheck978 : merged978 = Integer.Sparse.merge merged968 merged977 := by decide +kernel

theorem mergedZero978 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged978 x = 0 := by
  rw [mergeCheck978, Integer.Sparse.eval_merge]
  rw [mergedZero968 x h, mergedZero977 x h]
  simp only [add_zero]

theorem mergeCheck979 : merged979 = Integer.Sparse.merge merged960 merged978 := by decide +kernel

theorem mergedZero979 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged979 x = 0 := by
  rw [mergeCheck979, Integer.Sparse.eval_merge]
  rw [mergedZero960 x h, mergedZero978 x h]
  simp only [add_zero]

theorem mergeCheck980 : merged980 = Integer.Sparse.merge merged942 merged979 := by decide +kernel

theorem mergedZero980 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged980 x = 0 := by
  rw [mergeCheck980, Integer.Sparse.eval_merge]
  rw [mergedZero942 x h, mergedZero979 x h]
  simp only [add_zero]

theorem mergeCheck981 : merged981 = Integer.Sparse.merge (Integer.Sparse.scale (8877115633502937660) (sourceRows 984)) (Integer.Sparse.scale (2081320622087468580) (sourceRows 985)) := by decide +kernel

theorem mergedZero981 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged981 x = 0 := by
  rw [mergeCheck981, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck982 : merged982 = Integer.Sparse.merge (Integer.Sparse.scale (-2624571893522213880) (sourceRows 986)) (Integer.Sparse.scale (-65556023424325560) (sourceRows 987)) := by decide +kernel

theorem mergedZero982 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged982 x = 0 := by
  rw [mergeCheck982, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck983 : merged983 = Integer.Sparse.merge merged981 merged982 := by decide +kernel

theorem mergedZero983 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged983 x = 0 := by
  rw [mergeCheck983, Integer.Sparse.eval_merge]
  rw [mergedZero981 x h, mergedZero982 x h]
  simp only [add_zero]

theorem mergeCheck984 : merged984 = Integer.Sparse.merge (Integer.Sparse.scale (8920586497989542460) (sourceRows 988)) (Integer.Sparse.scale (-3938185655498221680) (sourceRows 989)) := by decide +kernel

theorem mergedZero984 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged984 x = 0 := by
  rw [mergeCheck984, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck985 : merged985 = Integer.Sparse.merge (Integer.Sparse.scale (16214435130724992) (sourceRows 991)) (Integer.Sparse.scale (1301310269946497020) (sourceRows 992)) := by decide +kernel

theorem mergedZero985 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged985 x = 0 := by
  rw [mergeCheck985, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck986 : merged986 = Integer.Sparse.merge (Integer.Sparse.scale (-78276282423651942840) (sourceRows 990)) merged985 := by decide +kernel

theorem mergedZero986 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged986 x = 0 := by
  rw [mergeCheck986, Integer.Sparse.eval_merge]
  rw [mergedZero985 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck987 : merged987 = Integer.Sparse.merge merged984 merged986 := by decide +kernel

theorem mergedZero987 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged987 x = 0 := by
  rw [mergeCheck987, Integer.Sparse.eval_merge]
  rw [mergedZero984 x h, mergedZero986 x h]
  simp only [add_zero]

theorem mergeCheck988 : merged988 = Integer.Sparse.merge merged983 merged987 := by decide +kernel

theorem mergedZero988 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged988 x = 0 := by
  rw [mergeCheck988, Integer.Sparse.eval_merge]
  rw [mergedZero983 x h, mergedZero987 x h]
  simp only [add_zero]

theorem mergeCheck989 : merged989 = Integer.Sparse.merge (Integer.Sparse.scale (-57324057593509728) (sourceRows 993)) (Integer.Sparse.scale (13742110045969291929600) (sourceRows 994)) := by decide +kernel

theorem mergedZero989 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged989 x = 0 := by
  rw [mergeCheck989, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck990 : merged990 = Integer.Sparse.merge (Integer.Sparse.scale (-27000240707066964825600) (sourceRows 996)) (Integer.Sparse.scale (-55778771592248773017600) (sourceRows 997)) := by decide +kernel

theorem mergedZero990 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged990 x = 0 := by
  rw [mergeCheck990, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck991 : merged991 = Integer.Sparse.merge (Integer.Sparse.scale (29056909249768657572000) (sourceRows 995)) merged990 := by decide +kernel

theorem mergedZero991 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged991 x = 0 := by
  rw [mergeCheck991, Integer.Sparse.eval_merge]
  rw [mergedZero990 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck992 : merged992 = Integer.Sparse.merge merged989 merged991 := by decide +kernel

theorem mergedZero992 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged992 x = 0 := by
  rw [mergeCheck992, Integer.Sparse.eval_merge]
  rw [mergedZero989 x h, mergedZero991 x h]
  simp only [add_zero]

theorem mergeCheck993 : merged993 = Integer.Sparse.merge (Integer.Sparse.scale (2220942473802420807600) (sourceRows 998)) (Integer.Sparse.scale (880523537557305600) (sourceRows 999)) := by decide +kernel

theorem mergedZero993 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged993 x = 0 := by
  rw [mergeCheck993, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck994 : merged994 = Integer.Sparse.merge (Integer.Sparse.scale (17025030956104985318400) (sourceRows 1001)) (Integer.Sparse.scale (-10836861063190396214400) (sourceRows 1002)) := by decide +kernel

theorem mergedZero994 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged994 x = 0 := by
  rw [mergeCheck994, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck995 : merged995 = Integer.Sparse.merge (Integer.Sparse.scale (185986649457035217100800) (sourceRows 1000)) merged994 := by decide +kernel

theorem mergedZero995 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged995 x = 0 := by
  rw [mergeCheck995, Integer.Sparse.eval_merge]
  rw [mergedZero994 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck996 : merged996 = Integer.Sparse.merge merged993 merged995 := by decide +kernel

theorem mergedZero996 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged996 x = 0 := by
  rw [mergeCheck996, Integer.Sparse.eval_merge]
  rw [mergedZero993 x h, mergedZero995 x h]
  simp only [add_zero]

theorem mergeCheck997 : merged997 = Integer.Sparse.merge merged992 merged996 := by decide +kernel

theorem mergedZero997 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged997 x = 0 := by
  rw [mergeCheck997, Integer.Sparse.eval_merge]
  rw [mergedZero992 x h, mergedZero996 x h]
  simp only [add_zero]

theorem mergeCheck998 : merged998 = Integer.Sparse.merge merged988 merged997 := by decide +kernel

theorem mergedZero998 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged998 x = 0 := by
  rw [mergeCheck998, Integer.Sparse.eval_merge]
  rw [mergedZero988 x h, mergedZero997 x h]
  simp only [add_zero]

theorem mergeCheck999 : merged999 = Integer.Sparse.merge (Integer.Sparse.scale (97279047194904933321600) (sourceRows 1003)) (Integer.Sparse.scale (-97272905682932727753600) (sourceRows 1004)) := by decide +kernel

theorem mergedZero999 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged999 x = 0 := by
  rw [mergeCheck999, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1000 : merged1000 = Integer.Sparse.merge (Integer.Sparse.scale (287047448064658030982400) (sourceRows 1005)) (Integer.Sparse.scale (-287047448064658030982400) (sourceRows 1006)) := by decide +kernel

theorem mergedZero1000 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1000 x = 0 := by
  rw [mergeCheck1000, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1001 : merged1001 = Integer.Sparse.merge merged999 merged1000 := by decide +kernel

theorem mergedZero1001 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1001 x = 0 := by
  rw [mergeCheck1001, Integer.Sparse.eval_merge]
  rw [mergedZero999 x h, mergedZero1000 x h]
  simp only [add_zero]

theorem mergeCheck1002 : merged1002 = Integer.Sparse.merge (Integer.Sparse.scale (11466832257216000) (sourceRows 1007)) (Integer.Sparse.scale (-241860983138241868800) (sourceRows 1008)) := by decide +kernel

theorem mergedZero1002 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1002 x = 0 := by
  rw [mergeCheck1002, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1003 : merged1003 = Integer.Sparse.merge (Integer.Sparse.scale (98224113355224998400) (sourceRows 1010)) (Integer.Sparse.scale (5816980531402967505600) (sourceRows 1011)) := by decide +kernel

theorem mergedZero1003 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1003 x = 0 := by
  rw [mergeCheck1003, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1004 : merged1004 = Integer.Sparse.merge (Integer.Sparse.scale (-73916976881664000) (sourceRows 1009)) merged1003 := by decide +kernel

theorem mergedZero1004 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1004 x = 0 := by
  rw [mergeCheck1004, Integer.Sparse.eval_merge]
  rw [mergedZero1003 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1005 : merged1005 = Integer.Sparse.merge merged1002 merged1004 := by decide +kernel

theorem mergedZero1005 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1005 x = 0 := by
  rw [mergeCheck1005, Integer.Sparse.eval_merge]
  rw [mergedZero1002 x h, mergedZero1004 x h]
  simp only [add_zero]

theorem mergeCheck1006 : merged1006 = Integer.Sparse.merge merged1001 merged1005 := by decide +kernel

theorem mergedZero1006 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1006 x = 0 := by
  rw [mergeCheck1006, Integer.Sparse.eval_merge]
  rw [mergedZero1001 x h, mergedZero1005 x h]
  simp only [add_zero]

theorem mergeCheck1007 : merged1007 = Integer.Sparse.merge (Integer.Sparse.scale (92076263110508544000) (sourceRows 1012)) (Integer.Sparse.scale (-47338378122204892800) (sourceRows 1013)) := by decide +kernel

theorem mergedZero1007 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1007 x = 0 := by
  rw [mergeCheck1007, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1008 : merged1008 = Integer.Sparse.merge (Integer.Sparse.scale (13653083709351620352000) (sourceRows 1015)) (Integer.Sparse.scale (-85413808869563804313600) (sourceRows 1016)) := by decide +kernel

theorem mergedZero1008 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1008 x = 0 := by
  rw [mergeCheck1008, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1009 : merged1009 = Integer.Sparse.merge (Integer.Sparse.scale (92049127426013184000) (sourceRows 1014)) merged1008 := by decide +kernel

theorem mergedZero1009 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1009 x = 0 := by
  rw [mergeCheck1009, Integer.Sparse.eval_merge]
  rw [mergedZero1008 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1010 : merged1010 = Integer.Sparse.merge merged1007 merged1009 := by decide +kernel

theorem mergedZero1010 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1010 x = 0 := by
  rw [mergeCheck1010, Integer.Sparse.eval_merge]
  rw [mergedZero1007 x h, mergedZero1009 x h]
  simp only [add_zero]

theorem mergeCheck1011 : merged1011 = Integer.Sparse.merge (Integer.Sparse.scale (56292462603027247564800) (sourceRows 1017)) (Integer.Sparse.scale (-12574890263324164608000) (sourceRows 1018)) := by decide +kernel

theorem mergedZero1011 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1011 x = 0 := by
  rw [mergeCheck1011, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1012 : merged1012 = Integer.Sparse.merge (Integer.Sparse.scale (41709164716800) (sourceRows 1020)) (Integer.Sparse.scale (-470964955502160) (sourceRows 1021)) := by decide +kernel

theorem mergedZero1012 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1012 x = 0 := by
  rw [mergeCheck1012, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1013 : merged1013 = Integer.Sparse.merge (Integer.Sparse.scale (39727937897514923212800) (sourceRows 1019)) merged1012 := by decide +kernel

theorem mergedZero1013 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1013 x = 0 := by
  rw [mergeCheck1013, Integer.Sparse.eval_merge]
  rw [mergedZero1012 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1014 : merged1014 = Integer.Sparse.merge merged1011 merged1013 := by decide +kernel

theorem mergedZero1014 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1014 x = 0 := by
  rw [mergeCheck1014, Integer.Sparse.eval_merge]
  rw [mergedZero1011 x h, mergedZero1013 x h]
  simp only [add_zero]

theorem mergeCheck1015 : merged1015 = Integer.Sparse.merge merged1010 merged1014 := by decide +kernel

theorem mergedZero1015 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1015 x = 0 := by
  rw [mergeCheck1015, Integer.Sparse.eval_merge]
  rw [mergedZero1010 x h, mergedZero1014 x h]
  simp only [add_zero]

theorem mergeCheck1016 : merged1016 = Integer.Sparse.merge merged1006 merged1015 := by decide +kernel

theorem mergedZero1016 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1016 x = 0 := by
  rw [mergeCheck1016, Integer.Sparse.eval_merge]
  rw [mergedZero1006 x h, mergedZero1015 x h]
  simp only [add_zero]

theorem mergeCheck1017 : merged1017 = Integer.Sparse.merge merged998 merged1016 := by decide +kernel

theorem mergedZero1017 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1017 x = 0 := by
  rw [mergeCheck1017, Integer.Sparse.eval_merge]
  rw [mergedZero998 x h, mergedZero1016 x h]
  simp only [add_zero]

theorem mergeCheck1018 : merged1018 = Integer.Sparse.merge (Integer.Sparse.scale (-5675083329278659968000) (sourceRows 1022)) (Integer.Sparse.scale (-16039480368823339780800) (sourceRows 1023)) := by decide +kernel

theorem mergedZero1018 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1018 x = 0 := by
  rw [mergeCheck1018, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1019 : merged1019 = Integer.Sparse.merge (Integer.Sparse.scale (225506864633299200) (sourceRows 1024)) (Integer.Sparse.scale (-3863659342985971200) (sourceRows 1025)) := by decide +kernel

theorem mergedZero1019 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1019 x = 0 := by
  rw [mergeCheck1019, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1020 : merged1020 = Integer.Sparse.merge merged1018 merged1019 := by decide +kernel

theorem mergedZero1020 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1020 x = 0 := by
  rw [mergeCheck1020, Integer.Sparse.eval_merge]
  rw [mergedZero1018 x h, mergedZero1019 x h]
  simp only [add_zero]

theorem mergeCheck1021 : merged1021 = Integer.Sparse.merge (Integer.Sparse.scale (211492341015097079347200) (sourceRows 1026)) (Integer.Sparse.scale (-34025955354424049184000) (sourceRows 1027)) := by decide +kernel

theorem mergedZero1021 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1021 x = 0 := by
  rw [mergeCheck1021, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1022 : merged1022 = Integer.Sparse.merge (Integer.Sparse.scale (-34034846648563750348800) (sourceRows 1029)) (Integer.Sparse.scale (-6119639328142956672000) (sourceRows 1030)) := by decide +kernel

theorem mergedZero1022 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1022 x = 0 := by
  rw [mergeCheck1022, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1023 : merged1023 = Integer.Sparse.merge (Integer.Sparse.scale (-211491258249555631872000) (sourceRows 1028)) merged1022 := by decide +kernel

theorem mergedZero1023 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1023 x = 0 := by
  rw [mergeCheck1023, Integer.Sparse.eval_merge]
  rw [mergedZero1022 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1024 : merged1024 = Integer.Sparse.merge merged1021 merged1023 := by decide +kernel

theorem mergedZero1024 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1024 x = 0 := by
  rw [mergeCheck1024, Integer.Sparse.eval_merge]
  rw [mergedZero1021 x h, mergedZero1023 x h]
  simp only [add_zero]

theorem mergeCheck1025 : merged1025 = Integer.Sparse.merge merged1020 merged1024 := by decide +kernel

theorem mergedZero1025 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1025 x = 0 := by
  rw [mergeCheck1025, Integer.Sparse.eval_merge]
  rw [mergedZero1020 x h, mergedZero1024 x h]
  simp only [add_zero]

theorem mergeCheck1026 : merged1026 = Integer.Sparse.merge (Integer.Sparse.scale (-6119400976128357120000) (sourceRows 1031)) (Integer.Sparse.scale (-2586047358112488345600) (sourceRows 1032)) := by decide +kernel

theorem mergedZero1026 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1026 x = 0 := by
  rw [mergeCheck1026, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1027 : merged1027 = Integer.Sparse.merge (Integer.Sparse.scale (-3278744462224627200) (sourceRows 1034)) (Integer.Sparse.scale (-3135125960300275200) (sourceRows 1035)) := by decide +kernel

theorem mergedZero1027 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1027 x = 0 := by
  rw [mergeCheck1027, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1028 : merged1028 = Integer.Sparse.merge (Integer.Sparse.scale (-162298817856000) (sourceRows 1033)) merged1027 := by decide +kernel

theorem mergedZero1028 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1028 x = 0 := by
  rw [mergeCheck1028, Integer.Sparse.eval_merge]
  rw [mergedZero1027 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1029 : merged1029 = Integer.Sparse.merge merged1026 merged1028 := by decide +kernel

theorem mergedZero1029 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1029 x = 0 := by
  rw [mergeCheck1029, Integer.Sparse.eval_merge]
  rw [mergedZero1026 x h, mergedZero1028 x h]
  simp only [add_zero]

theorem mergeCheck1030 : merged1030 = Integer.Sparse.merge (Integer.Sparse.scale (-2909619095666976000) (sourceRows 1036)) (Integer.Sparse.scale (-34036037252898849907200) (sourceRows 1037)) := by decide +kernel

theorem mergedZero1030 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1030 x = 0 := by
  rw [mergeCheck1030, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1031 : merged1031 = Integer.Sparse.merge (Integer.Sparse.scale (-30173004900864000) (sourceRows 1039)) (Integer.Sparse.scale (-1555112456522956800000) (sourceRows 1040)) := by decide +kernel

theorem mergedZero1031 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1031 x = 0 := by
  rw [mergeCheck1031, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1032 : merged1032 = Integer.Sparse.merge (Integer.Sparse.scale (-15224790808470536294400) (sourceRows 1038)) merged1031 := by decide +kernel

theorem mergedZero1032 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1032 x = 0 := by
  rw [mergeCheck1032, Integer.Sparse.eval_merge]
  rw [mergedZero1031 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1033 : merged1033 = Integer.Sparse.merge merged1030 merged1032 := by decide +kernel

theorem mergedZero1033 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1033 x = 0 := by
  rw [mergeCheck1033, Integer.Sparse.eval_merge]
  rw [mergedZero1030 x h, mergedZero1032 x h]
  simp only [add_zero]

theorem mergeCheck1034 : merged1034 = Integer.Sparse.merge merged1029 merged1033 := by decide +kernel

theorem mergedZero1034 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1034 x = 0 := by
  rw [mergeCheck1034, Integer.Sparse.eval_merge]
  rw [mergedZero1029 x h, mergedZero1033 x h]
  simp only [add_zero]

theorem mergeCheck1035 : merged1035 = Integer.Sparse.merge merged1025 merged1034 := by decide +kernel

theorem mergedZero1035 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1035 x = 0 := by
  rw [mergeCheck1035, Integer.Sparse.eval_merge]
  rw [mergedZero1025 x h, mergedZero1034 x h]
  simp only [add_zero]

theorem mergeCheck1036 : merged1036 = Integer.Sparse.merge (Integer.Sparse.scale (7552827555840000) (sourceRows 1041)) (Integer.Sparse.scale (-11299911170613861801600) (sourceRows 1042)) := by decide +kernel

theorem mergedZero1036 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1036 x = 0 := by
  rw [mergeCheck1036, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1037 : merged1037 = Integer.Sparse.merge (Integer.Sparse.scale (28238356030072868114400) (sourceRows 1043)) (Integer.Sparse.scale (-33124266012654183628800) (sourceRows 1044)) := by decide +kernel

theorem mergedZero1037 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1037 x = 0 := by
  rw [mergeCheck1037, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1038 : merged1038 = Integer.Sparse.merge merged1036 merged1037 := by decide +kernel

theorem mergedZero1038 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1038 x = 0 := by
  rw [mergeCheck1038, Integer.Sparse.eval_merge]
  rw [mergedZero1036 x h, mergedZero1037 x h]
  simp only [add_zero]

theorem mergeCheck1039 : merged1039 = Integer.Sparse.merge (Integer.Sparse.scale (-28126801140905288908800) (sourceRows 1045)) (Integer.Sparse.scale (22341565876800877056000) (sourceRows 1046)) := by decide +kernel

theorem mergedZero1039 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1039 x = 0 := by
  rw [mergeCheck1039, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1040 : merged1040 = Integer.Sparse.merge (Integer.Sparse.scale (-46122961004620174584000) (sourceRows 1048)) (Integer.Sparse.scale (-34489907629859349108000) (sourceRows 1049)) := by decide +kernel

theorem mergedZero1040 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1040 x = 0 := by
  rw [mergeCheck1040, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1041 : merged1041 = Integer.Sparse.merge (Integer.Sparse.scale (-6531306164169292800) (sourceRows 1047)) merged1040 := by decide +kernel

theorem mergedZero1041 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1041 x = 0 := by
  rw [mergeCheck1041, Integer.Sparse.eval_merge]
  rw [mergedZero1040 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1042 : merged1042 = Integer.Sparse.merge merged1039 merged1041 := by decide +kernel

theorem mergedZero1042 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1042 x = 0 := by
  rw [mergeCheck1042, Integer.Sparse.eval_merge]
  rw [mergedZero1039 x h, mergedZero1041 x h]
  simp only [add_zero]

theorem mergeCheck1043 : merged1043 = Integer.Sparse.merge merged1038 merged1042 := by decide +kernel

theorem mergedZero1043 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1043 x = 0 := by
  rw [mergeCheck1043, Integer.Sparse.eval_merge]
  rw [mergedZero1038 x h, mergedZero1042 x h]
  simp only [add_zero]

theorem mergeCheck1044 : merged1044 = Integer.Sparse.merge (Integer.Sparse.scale (67872300910007153817600) (sourceRows 1050)) (Integer.Sparse.scale (-43412522391413834803200) (sourceRows 1051)) := by decide +kernel

theorem mergedZero1044 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1044 x = 0 := by
  rw [mergeCheck1044, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1045 : merged1045 = Integer.Sparse.merge (Integer.Sparse.scale (880523537557305600) (sourceRows 1053)) (Integer.Sparse.scale (-59915627288947206100800) (sourceRows 1054)) := by decide +kernel

theorem mergedZero1045 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1045 x = 0 := by
  rw [mergeCheck1045, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1046 : merged1046 = Integer.Sparse.merge (Integer.Sparse.scale (87176869261278178284000) (sourceRows 1052)) merged1045 := by decide +kernel

theorem mergedZero1046 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1046 x = 0 := by
  rw [mergeCheck1046, Integer.Sparse.eval_merge]
  rw [mergedZero1045 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1047 : merged1047 = Integer.Sparse.merge merged1044 merged1046 := by decide +kernel

theorem mergedZero1047 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1047 x = 0 := by
  rw [mergeCheck1047, Integer.Sparse.eval_merge]
  rw [mergedZero1044 x h, mergedZero1046 x h]
  simp only [add_zero]

theorem mergeCheck1048 : merged1048 = Integer.Sparse.merge (Integer.Sparse.scale (50694589379139345309600) (sourceRows 1055)) (Integer.Sparse.scale (34024466343935054131200) (sourceRows 1056)) := by decide +kernel

theorem mergedZero1048 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1048 x = 0 := by
  rw [mergeCheck1048, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1049 : merged1049 = Integer.Sparse.merge (Integer.Sparse.scale (-6141511972205568000) (sourceRows 1058)) (Integer.Sparse.scale (-48881604363298269696000) (sourceRows 1059)) := by decide +kernel

theorem mergedZero1049 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1049 x = 0 := by
  rw [mergeCheck1049, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1050 : merged1050 = Integer.Sparse.merge (Integer.Sparse.scale (-854953460832996403200) (sourceRows 1057)) merged1049 := by decide +kernel

theorem mergedZero1050 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1050 x = 0 := by
  rw [mergeCheck1050, Integer.Sparse.eval_merge]
  rw [mergedZero1049 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1051 : merged1051 = Integer.Sparse.merge merged1048 merged1050 := by decide +kernel

theorem mergedZero1051 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1051 x = 0 := by
  rw [mergeCheck1051, Integer.Sparse.eval_merge]
  rw [mergedZero1048 x h, mergedZero1050 x h]
  simp only [add_zero]

theorem mergeCheck1052 : merged1052 = Integer.Sparse.merge merged1047 merged1051 := by decide +kernel

theorem mergedZero1052 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1052 x = 0 := by
  rw [mergeCheck1052, Integer.Sparse.eval_merge]
  rw [mergedZero1047 x h, mergedZero1051 x h]
  simp only [add_zero]

theorem mergeCheck1053 : merged1053 = Integer.Sparse.merge merged1043 merged1052 := by decide +kernel

theorem mergedZero1053 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1053 x = 0 := by
  rw [mergeCheck1053, Integer.Sparse.eval_merge]
  rw [mergedZero1043 x h, mergedZero1052 x h]
  simp only [add_zero]

theorem mergeCheck1054 : merged1054 = Integer.Sparse.merge merged1035 merged1053 := by decide +kernel

theorem mergedZero1054 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1054 x = 0 := by
  rw [mergeCheck1054, Integer.Sparse.eval_merge]
  rw [mergedZero1035 x h, mergedZero1053 x h]
  simp only [add_zero]

theorem mergeCheck1055 : merged1055 = Integer.Sparse.merge merged1017 merged1054 := by decide +kernel

theorem mergedZero1055 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1055 x = 0 := by
  rw [mergeCheck1055, Integer.Sparse.eval_merge]
  rw [mergedZero1017 x h, mergedZero1054 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1056 : merged1056 = Integer.Sparse.merge merged980 merged1055 := by decide +kernel

theorem mergedZero1056_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1056 x = 0 := by
  rw [mergeCheck1056, Integer.Sparse.eval_merge]
  rw [mergedZero980 x h, mergedZero1055 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1056_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1056_e_oai
