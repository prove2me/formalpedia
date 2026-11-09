-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1208_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:21:18.229975+00:00
-- url     : https://prove2.me/submissions/f76994b1-551c-4939-9c6d-ba149a46ee45

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E058
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1056_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1057 : merged1057 = Integer.Sparse.merge (Integer.Sparse.scale (-128159422325701046784000) (sourceRows 1060)) (Integer.Sparse.scale (4455431321137016623200) (sourceRows 1061)) := by decide +kernel

theorem mergedZero1057 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1057 x = 0 := by
  rw [mergeCheck1057, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1058 : merged1058 = Integer.Sparse.merge (Integer.Sparse.scale (-71703185183039637914400) (sourceRows 1062)) (Integer.Sparse.scale (80260553754098458675200) (sourceRows 1063)) := by decide +kernel

theorem mergedZero1058 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1058 x = 0 := by
  rw [mergeCheck1058, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1059 : merged1059 = Integer.Sparse.merge merged1057 merged1058 := by decide +kernel

theorem mergedZero1059 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1059 x = 0 := by
  rw [mergeCheck1059, Integer.Sparse.eval_merge]
  rw [mergedZero1057 x h, mergedZero1058 x h]
  simp only [add_zero]

theorem mergeCheck1060 : merged1060 = Integer.Sparse.merge (Integer.Sparse.scale (-63671503808991285043200) (sourceRows 1064)) (Integer.Sparse.scale (-44563645709533504512000) (sourceRows 1065)) := by decide +kernel

theorem mergedZero1060 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1060 x = 0 := by
  rw [mergeCheck1060, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1061 : merged1061 = Integer.Sparse.merge (Integer.Sparse.scale (-9662719411699200) (sourceRows 1067)) (Integer.Sparse.scale (33579944506755850291200) (sourceRows 1068)) := by decide +kernel

theorem mergedZero1061 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1061 x = 0 := by
  rw [mergeCheck1061, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1062 : merged1062 = Integer.Sparse.merge (Integer.Sparse.scale (-9772680138298560000) (sourceRows 1066)) merged1061 := by decide +kernel

theorem mergedZero1062 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1062 x = 0 := by
  rw [mergeCheck1062, Integer.Sparse.eval_merge]
  rw [mergedZero1061 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1063 : merged1063 = Integer.Sparse.merge merged1060 merged1062 := by decide +kernel

theorem mergedZero1063 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1063 x = 0 := by
  rw [mergeCheck1063, Integer.Sparse.eval_merge]
  rw [mergedZero1060 x h, mergedZero1062 x h]
  simp only [add_zero]

theorem mergeCheck1064 : merged1064 = Integer.Sparse.merge merged1059 merged1063 := by decide +kernel

theorem mergedZero1064 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1064 x = 0 := by
  rw [mergeCheck1064, Integer.Sparse.eval_merge]
  rw [mergedZero1059 x h, mergedZero1063 x h]
  simp only [add_zero]

theorem mergeCheck1065 : merged1065 = Integer.Sparse.merge (Integer.Sparse.scale (-110249053050412765440000) (sourceRows 1069)) (Integer.Sparse.scale (144185043974014239436800) (sourceRows 1070)) := by decide +kernel

theorem mergedZero1065 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1065 x = 0 := by
  rw [mergeCheck1065, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1066 : merged1066 = Integer.Sparse.merge (Integer.Sparse.scale (19478899242369810331200) (sourceRows 1072)) (Integer.Sparse.scale (45247330611271400623200) (sourceRows 1073)) := by decide +kernel

theorem mergedZero1066 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1066 x = 0 := by
  rw [mergeCheck1066, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1067 : merged1067 = Integer.Sparse.merge (Integer.Sparse.scale (-33952206586560759705600) (sourceRows 1071)) merged1066 := by decide +kernel

theorem mergedZero1067 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1067 x = 0 := by
  rw [mergeCheck1067, Integer.Sparse.eval_merge]
  rw [mergedZero1066 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1068 : merged1068 = Integer.Sparse.merge merged1065 merged1067 := by decide +kernel

theorem mergedZero1068 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1068 x = 0 := by
  rw [mergeCheck1068, Integer.Sparse.eval_merge]
  rw [mergedZero1065 x h, mergedZero1067 x h]
  simp only [add_zero]

theorem mergeCheck1069 : merged1069 = Integer.Sparse.merge (Integer.Sparse.scale (-111226958457519482222400) (sourceRows 1074)) (Integer.Sparse.scale (17011638558178823059200) (sourceRows 1075)) := by decide +kernel

theorem mergedZero1069 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1069 x = 0 := by
  rw [mergeCheck1069, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1070 : merged1070 = Integer.Sparse.merge (Integer.Sparse.scale (206657067412215995904000) (sourceRows 1077)) (Integer.Sparse.scale (75044812250892131020800) (sourceRows 1078)) := by decide +kernel

theorem mergedZero1070 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1070 x = 0 := by
  rw [mergeCheck1070, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1071 : merged1071 = Integer.Sparse.merge (Integer.Sparse.scale (97201279899533695536000) (sourceRows 1076)) merged1070 := by decide +kernel

theorem mergedZero1071 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1071 x = 0 := by
  rw [mergeCheck1071, Integer.Sparse.eval_merge]
  rw [mergedZero1070 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1072 : merged1072 = Integer.Sparse.merge merged1069 merged1071 := by decide +kernel

theorem mergedZero1072 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1072 x = 0 := by
  rw [mergeCheck1072, Integer.Sparse.eval_merge]
  rw [mergedZero1069 x h, mergedZero1071 x h]
  simp only [add_zero]

theorem mergeCheck1073 : merged1073 = Integer.Sparse.merge merged1068 merged1072 := by decide +kernel

theorem mergedZero1073 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1073 x = 0 := by
  rw [mergeCheck1073, Integer.Sparse.eval_merge]
  rw [mergedZero1068 x h, mergedZero1072 x h]
  simp only [add_zero]

theorem mergeCheck1074 : merged1074 = Integer.Sparse.merge merged1064 merged1073 := by decide +kernel

theorem mergedZero1074 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1074 x = 0 := by
  rw [mergeCheck1074, Integer.Sparse.eval_merge]
  rw [mergedZero1064 x h, mergedZero1073 x h]
  simp only [add_zero]

theorem mergeCheck1075 : merged1075 = Integer.Sparse.merge (Integer.Sparse.scale (-27699221334183475507200) (sourceRows 1079)) (Integer.Sparse.scale (53676069873930743500800) (sourceRows 1080)) := by decide +kernel

theorem mergedZero1075 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1075 x = 0 := by
  rw [mergeCheck1075, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1076 : merged1076 = Integer.Sparse.merge (Integer.Sparse.scale (107005693411203528412800) (sourceRows 1081)) (Integer.Sparse.scale (-68048932687870108262400) (sourceRows 1082)) := by decide +kernel

theorem mergedZero1076 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1076 x = 0 := by
  rw [mergeCheck1076, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1077 : merged1077 = Integer.Sparse.merge merged1075 merged1076 := by decide +kernel

theorem mergedZero1077 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1077 x = 0 := by
  rw [mergeCheck1077, Integer.Sparse.eval_merge]
  rw [mergedZero1075 x h, mergedZero1076 x h]
  simp only [add_zero]

theorem mergeCheck1078 : merged1078 = Integer.Sparse.merge (Integer.Sparse.scale (65227658909684858546400) (sourceRows 1083)) (Integer.Sparse.scale (34042129027415221708800) (sourceRows 1084)) := by decide +kernel

theorem mergedZero1078 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1078 x = 0 := by
  rw [mergeCheck1078, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1079 : merged1079 = Integer.Sparse.merge (Integer.Sparse.scale (573954180458419046361600) (sourceRows 1086)) (Integer.Sparse.scale (-15789974939756236800) (sourceRows 1087)) := by decide +kernel

theorem mergedZero1079 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1079 x = 0 := by
  rw [mergeCheck1079, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1080 : merged1080 = Integer.Sparse.merge (Integer.Sparse.scale (7932884794748928000) (sourceRows 1085)) merged1079 := by decide +kernel

theorem mergedZero1080 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1080 x = 0 := by
  rw [mergeCheck1080, Integer.Sparse.eval_merge]
  rw [mergedZero1079 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1081 : merged1081 = Integer.Sparse.merge merged1078 merged1080 := by decide +kernel

theorem mergedZero1081 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1081 x = 0 := by
  rw [mergeCheck1081, Integer.Sparse.eval_merge]
  rw [mergedZero1078 x h, mergedZero1080 x h]
  simp only [add_zero]

theorem mergeCheck1082 : merged1082 = Integer.Sparse.merge merged1077 merged1081 := by decide +kernel

theorem mergedZero1082 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1082 x = 0 := by
  rw [mergeCheck1082, Integer.Sparse.eval_merge]
  rw [mergedZero1077 x h, mergedZero1081 x h]
  simp only [add_zero]

theorem mergeCheck1083 : merged1083 = Integer.Sparse.merge (Integer.Sparse.scale (17921366125916198400) (sourceRows 1088)) (Integer.Sparse.scale (194550161505015117715200) (sourceRows 1089)) := by decide +kernel

theorem mergedZero1083 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1083 x = 0 := by
  rw [mergeCheck1083, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1084 : merged1084 = Integer.Sparse.merge (Integer.Sparse.scale (6403435625374905600) (sourceRows 1091)) (Integer.Sparse.scale (287047448064658030982400) (sourceRows 1092)) := by decide +kernel

theorem mergedZero1084 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1084 x = 0 := by
  rw [mergeCheck1084, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1085 : merged1085 = Integer.Sparse.merge (Integer.Sparse.scale (-6403435625374905600) (sourceRows 1090)) merged1084 := by decide +kernel

theorem mergedZero1085 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1085 x = 0 := by
  rw [mergeCheck1085, Integer.Sparse.eval_merge]
  rw [mergedZero1084 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1086 : merged1086 = Integer.Sparse.merge merged1083 merged1085 := by decide +kernel

theorem mergedZero1086 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1086 x = 0 := by
  rw [mergeCheck1086, Integer.Sparse.eval_merge]
  rw [mergedZero1083 x h, mergedZero1085 x h]
  simp only [add_zero]

theorem mergeCheck1087 : merged1087 = Integer.Sparse.merge (Integer.Sparse.scale (1608363659750400) (sourceRows 1093)) (Integer.Sparse.scale (92546309415035347200) (sourceRows 1094)) := by decide +kernel

theorem mergedZero1087 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1087 x = 0 := by
  rw [mergeCheck1087, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1088 : merged1088 = Integer.Sparse.merge (Integer.Sparse.scale (-111019006081340582400) (sourceRows 1096)) (Integer.Sparse.scale (-1085641740288000) (sourceRows 1097)) := by decide +kernel

theorem mergedZero1088 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1088 x = 0 := by
  rw [mergeCheck1088, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1089 : merged1089 = Integer.Sparse.merge (Integer.Sparse.scale (7646044605696000) (sourceRows 1095)) merged1088 := by decide +kernel

theorem mergedZero1089 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1089 x = 0 := by
  rw [mergeCheck1089, Integer.Sparse.eval_merge]
  rw [mergedZero1088 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1090 : merged1090 = Integer.Sparse.merge merged1087 merged1089 := by decide +kernel

theorem mergedZero1090 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1090 x = 0 := by
  rw [mergeCheck1090, Integer.Sparse.eval_merge]
  rw [mergedZero1087 x h, mergedZero1089 x h]
  simp only [add_zero]

theorem mergeCheck1091 : merged1091 = Integer.Sparse.merge merged1086 merged1090 := by decide +kernel

theorem mergedZero1091 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1091 x = 0 := by
  rw [mergeCheck1091, Integer.Sparse.eval_merge]
  rw [mergedZero1086 x h, mergedZero1090 x h]
  simp only [add_zero]

theorem mergeCheck1092 : merged1092 = Integer.Sparse.merge merged1082 merged1091 := by decide +kernel

theorem mergedZero1092 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1092 x = 0 := by
  rw [mergeCheck1092, Integer.Sparse.eval_merge]
  rw [mergedZero1082 x h, mergedZero1091 x h]
  simp only [add_zero]

theorem mergeCheck1093 : merged1093 = Integer.Sparse.merge merged1074 merged1092 := by decide +kernel

theorem mergedZero1093 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1093 x = 0 := by
  rw [mergeCheck1093, Integer.Sparse.eval_merge]
  rw [mergedZero1074 x h, mergedZero1092 x h]
  simp only [add_zero]

theorem mergeCheck1094 : merged1094 = Integer.Sparse.merge (Integer.Sparse.scale (67295537265188574720) (sourceRows 1098)) (Integer.Sparse.scale (-26475648817431436056000) (sourceRows 1099)) := by decide +kernel

theorem mergedZero1094 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1094 x = 0 := by
  rw [mergeCheck1094, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1095 : merged1095 = Integer.Sparse.merge (Integer.Sparse.scale (-30214112974628022115200) (sourceRows 1100)) (Integer.Sparse.scale (23512436154690674788800) (sourceRows 1101)) := by decide +kernel

theorem mergedZero1095 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1095 x = 0 := by
  rw [mergeCheck1095, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1096 : merged1096 = Integer.Sparse.merge merged1094 merged1095 := by decide +kernel

theorem mergedZero1096 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1096 x = 0 := by
  rw [mergeCheck1096, Integer.Sparse.eval_merge]
  rw [mergedZero1094 x h, mergedZero1095 x h]
  simp only [add_zero]

theorem mergeCheck1097 : merged1097 = Integer.Sparse.merge (Integer.Sparse.scale (-185804558775779328000) (sourceRows 1102)) (Integer.Sparse.scale (864452203812529920) (sourceRows 1103)) := by decide +kernel

theorem mergedZero1097 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1097 x = 0 := by
  rw [mergeCheck1097, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1098 : merged1098 = Integer.Sparse.merge (Integer.Sparse.scale (2423026464653120256000) (sourceRows 1105)) (Integer.Sparse.scale (2246156268653445120000) (sourceRows 1106)) := by decide +kernel

theorem mergedZero1098 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1098 x = 0 := by
  rw [mergeCheck1098, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1099 : merged1099 = Integer.Sparse.merge (Integer.Sparse.scale (-185778884573936640000) (sourceRows 1104)) merged1098 := by decide +kernel

theorem mergedZero1099 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1099 x = 0 := by
  rw [mergeCheck1099, Integer.Sparse.eval_merge]
  rw [mergedZero1098 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1100 : merged1100 = Integer.Sparse.merge merged1097 merged1099 := by decide +kernel

theorem mergedZero1100 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1100 x = 0 := by
  rw [mergeCheck1100, Integer.Sparse.eval_merge]
  rw [mergedZero1097 x h, mergedZero1099 x h]
  simp only [add_zero]

theorem mergeCheck1101 : merged1101 = Integer.Sparse.merge merged1096 merged1100 := by decide +kernel

theorem mergedZero1101 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1101 x = 0 := by
  rw [mergeCheck1101, Integer.Sparse.eval_merge]
  rw [mergedZero1096 x h, mergedZero1100 x h]
  simp only [add_zero]

theorem mergeCheck1102 : merged1102 = Integer.Sparse.merge (Integer.Sparse.scale (606438917347737600000) (sourceRows 1107)) (Integer.Sparse.scale (199470141561600) (sourceRows 1108)) := by decide +kernel

theorem mergedZero1102 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1102 x = 0 := by
  rw [mergeCheck1102, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1103 : merged1103 = Integer.Sparse.merge (Integer.Sparse.scale (8290021226739840) (sourceRows 1110)) (Integer.Sparse.scale (307066237052440320) (sourceRows 1111)) := by decide +kernel

theorem mergedZero1103 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1103 x = 0 := by
  rw [mergeCheck1103, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1104 : merged1104 = Integer.Sparse.merge (Integer.Sparse.scale (21145229585563754160) (sourceRows 1109)) merged1103 := by decide +kernel

theorem mergedZero1104 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1104 x = 0 := by
  rw [mergeCheck1104, Integer.Sparse.eval_merge]
  rw [mergedZero1103 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1105 : merged1105 = Integer.Sparse.merge merged1102 merged1104 := by decide +kernel

theorem mergedZero1105 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1105 x = 0 := by
  rw [mergeCheck1105, Integer.Sparse.eval_merge]
  rw [mergedZero1102 x h, mergedZero1104 x h]
  simp only [add_zero]

theorem mergeCheck1106 : merged1106 = Integer.Sparse.merge (Integer.Sparse.scale (-11367993179963788300800) (sourceRows 1112)) (Integer.Sparse.scale (-20011601790024768000) (sourceRows 1113)) := by decide +kernel

theorem mergedZero1106 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1106 x = 0 := by
  rw [mergeCheck1106, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1107 : merged1107 = Integer.Sparse.merge (Integer.Sparse.scale (-305567923332461207040) (sourceRows 1115)) (Integer.Sparse.scale (-5157394025968945152000) (sourceRows 1116)) := by decide +kernel

theorem mergedZero1107 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1107 x = 0 := by
  rw [mergeCheck1107, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1108 : merged1108 = Integer.Sparse.merge (Integer.Sparse.scale (-5157263251477757952000) (sourceRows 1114)) merged1107 := by decide +kernel

theorem mergedZero1108 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1108 x = 0 := by
  rw [mergeCheck1108, Integer.Sparse.eval_merge]
  rw [mergedZero1107 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1109 : merged1109 = Integer.Sparse.merge merged1106 merged1108 := by decide +kernel

theorem mergedZero1109 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1109 x = 0 := by
  rw [mergeCheck1109, Integer.Sparse.eval_merge]
  rw [mergedZero1106 x h, mergedZero1108 x h]
  simp only [add_zero]

theorem mergeCheck1110 : merged1110 = Integer.Sparse.merge merged1105 merged1109 := by decide +kernel

theorem mergedZero1110 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1110 x = 0 := by
  rw [mergeCheck1110, Integer.Sparse.eval_merge]
  rw [mergedZero1105 x h, mergedZero1109 x h]
  simp only [add_zero]

theorem mergeCheck1111 : merged1111 = Integer.Sparse.merge merged1101 merged1110 := by decide +kernel

theorem mergedZero1111 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1111 x = 0 := by
  rw [mergeCheck1111, Integer.Sparse.eval_merge]
  rw [mergedZero1101 x h, mergedZero1110 x h]
  simp only [add_zero]

theorem mergeCheck1112 : merged1112 = Integer.Sparse.merge (Integer.Sparse.scale (-185760909645081903820800) (sourceRows 1117)) (Integer.Sparse.scale (-470199129949768026931200) (sourceRows 1118)) := by decide +kernel

theorem mergedZero1112 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1112 x = 0 := by
  rw [mergeCheck1112, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1113 : merged1113 = Integer.Sparse.merge (Integer.Sparse.scale (-144674109717085638144000) (sourceRows 1119)) (Integer.Sparse.scale (78880488422400) (sourceRows 1120)) := by decide +kernel

theorem mergedZero1113 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1113 x = 0 := by
  rw [mergeCheck1113, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1114 : merged1114 = Integer.Sparse.merge merged1112 merged1113 := by decide +kernel

theorem mergedZero1114 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1114 x = 0 := by
  rw [mergeCheck1114, Integer.Sparse.eval_merge]
  rw [mergedZero1112 x h, mergedZero1113 x h]
  simp only [add_zero]

theorem mergeCheck1115 : merged1115 = Integer.Sparse.merge (Integer.Sparse.scale (444839060736000) (sourceRows 1121)) (Integer.Sparse.scale (-36497254546650438273600) (sourceRows 1122)) := by decide +kernel

theorem mergedZero1115 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1115 x = 0 := by
  rw [mergeCheck1115, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1116 : merged1116 = Integer.Sparse.merge (Integer.Sparse.scale (21300409627930016640) (sourceRows 1124)) (Integer.Sparse.scale (1611621893709886464000) (sourceRows 1125)) := by decide +kernel

theorem mergedZero1116 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1116 x = 0 := by
  rw [mergeCheck1116, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1117 : merged1117 = Integer.Sparse.merge (Integer.Sparse.scale (1611649167397355520000) (sourceRows 1123)) merged1116 := by decide +kernel

theorem mergedZero1117 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1117 x = 0 := by
  rw [mergeCheck1117, Integer.Sparse.eval_merge]
  rw [mergedZero1116 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1118 : merged1118 = Integer.Sparse.merge merged1115 merged1117 := by decide +kernel

theorem mergedZero1118 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1118 x = 0 := by
  rw [mergeCheck1118, Integer.Sparse.eval_merge]
  rw [mergedZero1115 x h, mergedZero1117 x h]
  simp only [add_zero]

theorem mergeCheck1119 : merged1119 = Integer.Sparse.merge merged1114 merged1118 := by decide +kernel

theorem mergedZero1119 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1119 x = 0 := by
  rw [mergeCheck1119, Integer.Sparse.eval_merge]
  rw [mergedZero1114 x h, mergedZero1118 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1120 : merged1120 = Integer.Sparse.merge (Integer.Sparse.scale (-13016701088541980928000) (sourceRows 1126)) (Integer.Sparse.scale (25670459125098902016000) (sourceRows 1127)) := by decide +kernel

theorem mergedZero1120 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1120 x = 0 := by
  rw [mergeCheck1120, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1121 : merged1121 = Integer.Sparse.merge (Integer.Sparse.scale (-89751275452784217888000) (sourceRows 1129)) (Integer.Sparse.scale (199470141561600) (sourceRows 1130)) := by decide +kernel

theorem mergedZero1121 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1121 x = 0 := by
  rw [mergeCheck1121, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1122 : merged1122 = Integer.Sparse.merge (Integer.Sparse.scale (-2713512723987824640000) (sourceRows 1128)) merged1121 := by decide +kernel

theorem mergedZero1122 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1122 x = 0 := by
  rw [mergeCheck1122, Integer.Sparse.eval_merge]
  rw [mergedZero1121 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1123 : merged1123 = Integer.Sparse.merge merged1120 merged1122 := by decide +kernel

theorem mergedZero1123 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1123 x = 0 := by
  rw [mergeCheck1123, Integer.Sparse.eval_merge]
  rw [mergedZero1120 x h, mergedZero1122 x h]
  simp only [add_zero]

theorem mergeCheck1124 : merged1124 = Integer.Sparse.merge (Integer.Sparse.scale (-313203978657360) (sourceRows 1131)) (Integer.Sparse.scale (-6719487960832819200) (sourceRows 1132)) := by decide +kernel

theorem mergedZero1124 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1124 x = 0 := by
  rw [mergeCheck1124, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1125 : merged1125 = Integer.Sparse.merge (Integer.Sparse.scale (5696442553423910400) (sourceRows 1134)) (Integer.Sparse.scale (7695955372738348800) (sourceRows 1135)) := by decide +kernel

theorem mergedZero1125 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1125 x = 0 := by
  rw [mergeCheck1125, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1126 : merged1126 = Integer.Sparse.merge (Integer.Sparse.scale (422910256741736969318400) (sourceRows 1133)) merged1125 := by decide +kernel

theorem mergedZero1126 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1126 x = 0 := by
  rw [mergeCheck1126, Integer.Sparse.eval_merge]
  rw [mergedZero1125 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1127 : merged1127 = Integer.Sparse.merge merged1124 merged1126 := by decide +kernel

theorem mergedZero1127 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1127 x = 0 := by
  rw [mergeCheck1127, Integer.Sparse.eval_merge]
  rw [mergedZero1124 x h, mergedZero1126 x h]
  simp only [add_zero]

theorem mergeCheck1128 : merged1128 = Integer.Sparse.merge merged1123 merged1127 := by decide +kernel

theorem mergedZero1128 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1128 x = 0 := by
  rw [mergeCheck1128, Integer.Sparse.eval_merge]
  rw [mergedZero1123 x h, mergedZero1127 x h]
  simp only [add_zero]

theorem mergeCheck1129 : merged1129 = Integer.Sparse.merge merged1119 merged1128 := by decide +kernel

theorem mergedZero1129 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1129 x = 0 := by
  rw [mergeCheck1129, Integer.Sparse.eval_merge]
  rw [mergedZero1119 x h, mergedZero1128 x h]
  simp only [add_zero]

theorem mergeCheck1130 : merged1130 = Integer.Sparse.merge merged1111 merged1129 := by decide +kernel

theorem mergedZero1130 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1130 x = 0 := by
  rw [mergeCheck1130, Integer.Sparse.eval_merge]
  rw [mergedZero1111 x h, mergedZero1129 x h]
  simp only [add_zero]

theorem mergeCheck1131 : merged1131 = Integer.Sparse.merge merged1093 merged1130 := by decide +kernel

theorem mergedZero1131 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1131 x = 0 := by
  rw [mergeCheck1131, Integer.Sparse.eval_merge]
  rw [mergedZero1093 x h, mergedZero1130 x h]
  simp only [add_zero]

theorem mergeCheck1132 : merged1132 = Integer.Sparse.merge (Integer.Sparse.scale (49153693364934335150400) (sourceRows 1136)) (Integer.Sparse.scale (536858118289785600) (sourceRows 1137)) := by decide +kernel

theorem mergedZero1132 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1132 x = 0 := by
  rw [mergeCheck1132, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1133 : merged1133 = Integer.Sparse.merge (Integer.Sparse.scale (-10819766500584652800) (sourceRows 1138)) (Integer.Sparse.scale (9799605206414553600) (sourceRows 1139)) := by decide +kernel

theorem mergedZero1133 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1133 x = 0 := by
  rw [mergeCheck1133, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1134 : merged1134 = Integer.Sparse.merge merged1132 merged1133 := by decide +kernel

theorem mergedZero1134 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1134 x = 0 := by
  rw [mergeCheck1134, Integer.Sparse.eval_merge]
  rw [mergedZero1132 x h, mergedZero1133 x h]
  simp only [add_zero]

theorem mergeCheck1135 : merged1135 = Integer.Sparse.merge (Integer.Sparse.scale (-13260950362186329600) (sourceRows 1140)) (Integer.Sparse.scale (13260950362186329600) (sourceRows 1141)) := by decide +kernel

theorem mergedZero1135 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1135 x = 0 := by
  rw [mergeCheck1135, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1136 : merged1136 = Integer.Sparse.merge (Integer.Sparse.scale (1073716236579571200) (sourceRows 1143)) (Integer.Sparse.scale (-9211968083624140800) (sourceRows 1144)) := by decide +kernel

theorem mergedZero1136 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1136 x = 0 := by
  rw [mergeCheck1136, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1137 : merged1137 = Integer.Sparse.merge (Integer.Sparse.scale (287058825563824550073600) (sourceRows 1142)) merged1136 := by decide +kernel

theorem mergedZero1137 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1137 x = 0 := by
  rw [mergeCheck1137, Integer.Sparse.eval_merge]
  rw [mergedZero1136 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1138 : merged1138 = Integer.Sparse.merge merged1135 merged1137 := by decide +kernel

theorem mergedZero1138 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1138 x = 0 := by
  rw [mergeCheck1138, Integer.Sparse.eval_merge]
  rw [mergedZero1135 x h, mergedZero1137 x h]
  simp only [add_zero]

theorem mergeCheck1139 : merged1139 = Integer.Sparse.merge merged1134 merged1138 := by decide +kernel

theorem mergedZero1139 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1139 x = 0 := by
  rw [mergeCheck1139, Integer.Sparse.eval_merge]
  rw [mergedZero1134 x h, mergedZero1138 x h]
  simp only [add_zero]

theorem mergeCheck1140 : merged1140 = Integer.Sparse.merge (Integer.Sparse.scale (422982516499111263744000) (sourceRows 1145)) (Integer.Sparse.scale (-97266995354371454438400) (sourceRows 1146)) := by decide +kernel

theorem mergedZero1140 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1140 x = 0 := by
  rw [mergeCheck1140, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1141 : merged1141 = Integer.Sparse.merge (Integer.Sparse.scale (92486321841900965731200) (sourceRows 1148)) (Integer.Sparse.scale (-92899968876009570441600) (sourceRows 1149)) := by decide +kernel

theorem mergedZero1141 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1141 x = 0 := by
  rw [mergeCheck1141, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1142 : merged1142 = Integer.Sparse.merge (Integer.Sparse.scale (-5520534369309590400) (sourceRows 1147)) merged1141 := by decide +kernel

theorem mergedZero1142 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1142 x = 0 := by
  rw [mergeCheck1142, Integer.Sparse.eval_merge]
  rw [mergedZero1141 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1143 : merged1143 = Integer.Sparse.merge merged1140 merged1142 := by decide +kernel

theorem mergedZero1143 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1143 x = 0 := by
  rw [mergeCheck1143, Integer.Sparse.eval_merge]
  rw [mergedZero1140 x h, mergedZero1142 x h]
  simp only [add_zero]

theorem mergeCheck1144 : merged1144 = Integer.Sparse.merge (Integer.Sparse.scale (-194535114566061752985600) (sourceRows 1150)) (Integer.Sparse.scale (-7331137563789446400) (sourceRows 1151)) := by decide +kernel

theorem mergedZero1144 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1144 x = 0 := by
  rw [mergeCheck1144, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1145 : merged1145 = Integer.Sparse.merge (Integer.Sparse.scale (-6181875485291116800) (sourceRows 1153)) (Integer.Sparse.scale (-138721510040765123808000) (sourceRows 1154)) := by decide +kernel

theorem mergedZero1145 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1145 x = 0 := by
  rw [mergeCheck1145, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1146 : merged1146 = Integer.Sparse.merge (Integer.Sparse.scale (-194578811390965787654400) (sourceRows 1152)) merged1145 := by decide +kernel

theorem mergedZero1146 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1146 x = 0 := by
  rw [mergeCheck1146, Integer.Sparse.eval_merge]
  rw [mergedZero1145 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1147 : merged1147 = Integer.Sparse.merge merged1144 merged1146 := by decide +kernel

theorem mergedZero1147 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1147 x = 0 := by
  rw [mergeCheck1147, Integer.Sparse.eval_merge]
  rw [mergedZero1144 x h, mergedZero1146 x h]
  simp only [add_zero]

theorem mergeCheck1148 : merged1148 = Integer.Sparse.merge merged1143 merged1147 := by decide +kernel

theorem mergedZero1148 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1148 x = 0 := by
  rw [mergeCheck1148, Integer.Sparse.eval_merge]
  rw [mergedZero1143 x h, mergedZero1147 x h]
  simp only [add_zero]

theorem mergeCheck1149 : merged1149 = Integer.Sparse.merge merged1139 merged1148 := by decide +kernel

theorem mergedZero1149 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1149 x = 0 := by
  rw [mergeCheck1149, Integer.Sparse.eval_merge]
  rw [mergedZero1139 x h, mergedZero1148 x h]
  simp only [add_zero]

theorem mergeCheck1150 : merged1150 = Integer.Sparse.merge (Integer.Sparse.scale (-405988826648887036800) (sourceRows 1155)) (Integer.Sparse.scale (-194582382023679867302400) (sourceRows 1156)) := by decide +kernel

theorem mergedZero1150 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1150 x = 0 := by
  rw [mergeCheck1150, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1151 : merged1151 = Integer.Sparse.merge (Integer.Sparse.scale (8715788742304224000) (sourceRows 1157)) (Integer.Sparse.scale (-1374396942622556160000) (sourceRows 1158)) := by decide +kernel

theorem mergedZero1151 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1151 x = 0 := by
  rw [mergeCheck1151, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1152 : merged1152 = Integer.Sparse.merge merged1150 merged1151 := by decide +kernel

theorem mergedZero1152 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1152 x = 0 := by
  rw [mergeCheck1152, Integer.Sparse.eval_merge]
  rw [mergedZero1150 x h, mergedZero1151 x h]
  simp only [add_zero]

theorem mergeCheck1153 : merged1153 = Integer.Sparse.merge (Integer.Sparse.scale (20081451544677321120) (sourceRows 1159)) (Integer.Sparse.scale (-1374278561398987776000) (sourceRows 1160)) := by decide +kernel

theorem mergedZero1153 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1153 x = 0 := by
  rw [mergeCheck1153, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1154 : merged1154 = Integer.Sparse.merge (Integer.Sparse.scale (-114126411674831286528000) (sourceRows 1162)) (Integer.Sparse.scale (40895770068328044441600) (sourceRows 1163)) := by decide +kernel

theorem mergedZero1154 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1154 x = 0 := by
  rw [mergeCheck1154, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1155 : merged1155 = Integer.Sparse.merge (Integer.Sparse.scale (64139689317133446912000) (sourceRows 1161)) merged1154 := by decide +kernel

theorem mergedZero1155 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1155 x = 0 := by
  rw [mergeCheck1155, Integer.Sparse.eval_merge]
  rw [mergedZero1154 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1156 : merged1156 = Integer.Sparse.merge merged1153 merged1155 := by decide +kernel

theorem mergedZero1156 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1156 x = 0 := by
  rw [mergeCheck1156, Integer.Sparse.eval_merge]
  rw [mergedZero1153 x h, mergedZero1155 x h]
  simp only [add_zero]

theorem mergeCheck1157 : merged1157 = Integer.Sparse.merge merged1152 merged1156 := by decide +kernel

theorem mergedZero1157 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1157 x = 0 := by
  rw [mergeCheck1157, Integer.Sparse.eval_merge]
  rw [mergedZero1152 x h, mergedZero1156 x h]
  simp only [add_zero]

theorem mergeCheck1158 : merged1158 = Integer.Sparse.merge (Integer.Sparse.scale (-17010263371428265881600) (sourceRows 1164)) (Integer.Sparse.scale (81149408928000) (sourceRows 1165)) := by decide +kernel

theorem mergedZero1158 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1158 x = 0 := by
  rw [mergeCheck1158, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1159 : merged1159 = Integer.Sparse.merge (Integer.Sparse.scale (49685742675152640) (sourceRows 1167)) (Integer.Sparse.scale (53489454307675601947200) (sourceRows 1168)) := by decide +kernel

theorem mergedZero1159 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1159 x = 0 := by
  rw [mergeCheck1159, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1160 : merged1160 = Integer.Sparse.merge (Integer.Sparse.scale (432968675328000) (sourceRows 1166)) merged1159 := by decide +kernel

theorem mergedZero1160 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1160 x = 0 := by
  rw [mergeCheck1160, Integer.Sparse.eval_merge]
  rw [mergedZero1159 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1161 : merged1161 = Integer.Sparse.merge merged1158 merged1160 := by decide +kernel

theorem mergedZero1161 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1161 x = 0 := by
  rw [mergeCheck1161, Integer.Sparse.eval_merge]
  rw [mergedZero1158 x h, mergedZero1160 x h]
  simp only [add_zero]

theorem mergeCheck1162 : merged1162 = Integer.Sparse.merge (Integer.Sparse.scale (6413183775433064448000) (sourceRows 1169)) (Integer.Sparse.scale (71245051454748326400) (sourceRows 1170)) := by decide +kernel

theorem mergedZero1162 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1162 x = 0 := by
  rw [mergeCheck1162, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1163 : merged1163 = Integer.Sparse.merge (Integer.Sparse.scale (-1403489724974817177600) (sourceRows 1172)) (Integer.Sparse.scale (93716011384988086886400) (sourceRows 1173)) := by decide +kernel

theorem mergedZero1163 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1163 x = 0 := by
  rw [mergeCheck1163, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1164 : merged1164 = Integer.Sparse.merge (Integer.Sparse.scale (6413695863840405504000) (sourceRows 1171)) merged1163 := by decide +kernel

theorem mergedZero1164 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1164 x = 0 := by
  rw [mergeCheck1164, Integer.Sparse.eval_merge]
  rw [mergedZero1163 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1165 : merged1165 = Integer.Sparse.merge merged1162 merged1164 := by decide +kernel

theorem mergedZero1165 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1165 x = 0 := by
  rw [mergeCheck1165, Integer.Sparse.eval_merge]
  rw [mergedZero1162 x h, mergedZero1164 x h]
  simp only [add_zero]

theorem mergeCheck1166 : merged1166 = Integer.Sparse.merge merged1161 merged1165 := by decide +kernel

theorem mergedZero1166 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1166 x = 0 := by
  rw [mergeCheck1166, Integer.Sparse.eval_merge]
  rw [mergedZero1161 x h, mergedZero1165 x h]
  simp only [add_zero]

theorem mergeCheck1167 : merged1167 = Integer.Sparse.merge merged1157 merged1166 := by decide +kernel

theorem mergedZero1167 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1167 x = 0 := by
  rw [mergeCheck1167, Integer.Sparse.eval_merge]
  rw [mergedZero1157 x h, mergedZero1166 x h]
  simp only [add_zero]

theorem mergeCheck1168 : merged1168 = Integer.Sparse.merge merged1149 merged1167 := by decide +kernel

theorem mergedZero1168 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1168 x = 0 := by
  rw [mergeCheck1168, Integer.Sparse.eval_merge]
  rw [mergedZero1149 x h, mergedZero1167 x h]
  simp only [add_zero]

theorem mergeCheck1169 : merged1169 = Integer.Sparse.merge (Integer.Sparse.scale (-19174230730402491340800) (sourceRows 1174)) (Integer.Sparse.scale (39227904062542940774400) (sourceRows 1175)) := by decide +kernel

theorem mergedZero1169 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1169 x = 0 := by
  rw [mergeCheck1169, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1170 : merged1170 = Integer.Sparse.merge (Integer.Sparse.scale (-11925882532469961216000) (sourceRows 1176)) (Integer.Sparse.scale (361768959417600) (sourceRows 1177)) := by decide +kernel

theorem mergedZero1170 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1170 x = 0 := by
  rw [mergeCheck1170, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1171 : merged1171 = Integer.Sparse.merge merged1169 merged1170 := by decide +kernel

theorem mergedZero1171 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1171 x = 0 := by
  rw [mergeCheck1171, Integer.Sparse.eval_merge]
  rw [mergedZero1169 x h, mergedZero1170 x h]
  simp only [add_zero]

theorem mergeCheck1172 : merged1172 = Integer.Sparse.merge (Integer.Sparse.scale (15753070312508309760) (sourceRows 1178)) (Integer.Sparse.scale (65629625967696752640) (sourceRows 1179)) := by decide +kernel

theorem mergedZero1172 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1172 x = 0 := by
  rw [mergeCheck1172, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1173 : merged1173 = Integer.Sparse.merge (Integer.Sparse.scale (-45674372425411608883200) (sourceRows 1181)) (Integer.Sparse.scale (-71625783399032217600) (sourceRows 1182)) := by decide +kernel

theorem mergedZero1173 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1173 x = 0 := by
  rw [mergeCheck1173, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1174 : merged1174 = Integer.Sparse.merge (Integer.Sparse.scale (-46234046458160945395200) (sourceRows 1180)) merged1173 := by decide +kernel

theorem mergedZero1174 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1174 x = 0 := by
  rw [mergeCheck1174, Integer.Sparse.eval_merge]
  rw [mergedZero1173 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1175 : merged1175 = Integer.Sparse.merge merged1172 merged1174 := by decide +kernel

theorem mergedZero1175 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1175 x = 0 := by
  rw [mergeCheck1175, Integer.Sparse.eval_merge]
  rw [mergedZero1172 x h, mergedZero1174 x h]
  simp only [add_zero]

theorem mergeCheck1176 : merged1176 = Integer.Sparse.merge merged1171 merged1175 := by decide +kernel

theorem mergedZero1176 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1176 x = 0 := by
  rw [mergeCheck1176, Integer.Sparse.eval_merge]
  rw [mergedZero1171 x h, mergedZero1175 x h]
  simp only [add_zero]

theorem mergeCheck1177 : merged1177 = Integer.Sparse.merge (Integer.Sparse.scale (21822397148115828633600) (sourceRows 1183)) (Integer.Sparse.scale (-429284816713318809600) (sourceRows 1184)) := by decide +kernel

theorem mergedZero1177 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1177 x = 0 := by
  rw [mergeCheck1177, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1178 : merged1178 = Integer.Sparse.merge (Integer.Sparse.scale (-68502663511462261670400) (sourceRows 1186)) (Integer.Sparse.scale (-20603868022082419200) (sourceRows 1187)) := by decide +kernel

theorem mergedZero1178 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1178 x = 0 := by
  rw [mergeCheck1178, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1179 : merged1179 = Integer.Sparse.merge (Integer.Sparse.scale (-574108841688358180377600) (sourceRows 1185)) merged1178 := by decide +kernel

theorem mergedZero1179 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1179 x = 0 := by
  rw [mergeCheck1179, Integer.Sparse.eval_merge]
  rw [mergedZero1178 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1180 : merged1180 = Integer.Sparse.merge merged1177 merged1179 := by decide +kernel

theorem mergedZero1180 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1180 x = 0 := by
  rw [mergeCheck1180, Integer.Sparse.eval_merge]
  rw [mergedZero1177 x h, mergedZero1179 x h]
  simp only [add_zero]

theorem mergeCheck1181 : merged1181 = Integer.Sparse.merge (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1188)) (Integer.Sparse.scale (21681282096458611200) (sourceRows 1189)) := by decide +kernel

theorem mergedZero1181 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1181 x = 0 := by
  rw [mergeCheck1181, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1182 : merged1182 = Integer.Sparse.merge (Integer.Sparse.scale (393115900254142464000) (sourceRows 1191)) (Integer.Sparse.scale (393033615201174528000) (sourceRows 1192)) := by decide +kernel

theorem mergedZero1182 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1182 x = 0 := by
  rw [mergeCheck1182, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1183 : merged1183 = Integer.Sparse.merge (Integer.Sparse.scale (68053263750035898163200) (sourceRows 1190)) merged1182 := by decide +kernel

theorem mergedZero1183 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1183 x = 0 := by
  rw [mergeCheck1183, Integer.Sparse.eval_merge]
  rw [mergedZero1182 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

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

theorem mergeCheck1184 : merged1184 = Integer.Sparse.merge merged1181 merged1183 := by decide +kernel

theorem mergedZero1184 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1184 x = 0 := by
  rw [mergeCheck1184, Integer.Sparse.eval_merge]
  rw [mergedZero1181 x h, mergedZero1183 x h]
  simp only [add_zero]

theorem mergeCheck1185 : merged1185 = Integer.Sparse.merge merged1180 merged1184 := by decide +kernel

theorem mergedZero1185 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1185 x = 0 := by
  rw [mergeCheck1185, Integer.Sparse.eval_merge]
  rw [mergedZero1180 x h, mergedZero1184 x h]
  simp only [add_zero]

theorem mergeCheck1186 : merged1186 = Integer.Sparse.merge merged1176 merged1185 := by decide +kernel

theorem mergedZero1186 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1186 x = 0 := by
  rw [mergeCheck1186, Integer.Sparse.eval_merge]
  rw [mergedZero1176 x h, mergedZero1185 x h]
  simp only [add_zero]

theorem mergeCheck1187 : merged1187 = Integer.Sparse.merge (Integer.Sparse.scale (-101707579937874926131200) (sourceRows 1193)) (Integer.Sparse.scale (-81149408928000) (sourceRows 1194)) := by decide +kernel

theorem mergedZero1187 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1187 x = 0 := by
  rw [mergeCheck1187, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1188 : merged1188 = Integer.Sparse.merge (Integer.Sparse.scale (25216391418065861529600) (sourceRows 1195)) (Integer.Sparse.scale (25217207614223447961600) (sourceRows 1196)) := by decide +kernel

theorem mergedZero1188 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1188 x = 0 := by
  rw [mergeCheck1188, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1189 : merged1189 = Integer.Sparse.merge merged1187 merged1188 := by decide +kernel

theorem mergedZero1189 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1189 x = 0 := by
  rw [mergeCheck1189, Integer.Sparse.eval_merge]
  rw [mergedZero1187 x h, mergedZero1188 x h]
  simp only [add_zero]

theorem mergeCheck1190 : merged1190 = Integer.Sparse.merge (Integer.Sparse.scale (28921066087254934118400) (sourceRows 1197)) (Integer.Sparse.scale (28921479784083836006400) (sourceRows 1198)) := by decide +kernel

theorem mergedZero1190 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1190 x = 0 := by
  rw [mergeCheck1190, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1191 : merged1191 = Integer.Sparse.merge (Integer.Sparse.scale (47573282894282243481600) (sourceRows 1200)) (Integer.Sparse.scale (-19478899242369810331200) (sourceRows 1201)) := by decide +kernel

theorem mergedZero1191 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1191 x = 0 := by
  rw [mergeCheck1191, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1192 : merged1192 = Integer.Sparse.merge (Integer.Sparse.scale (-1697571027004076179200) (sourceRows 1199)) merged1191 := by decide +kernel

theorem mergedZero1192 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1192 x = 0 := by
  rw [mergeCheck1192, Integer.Sparse.eval_merge]
  rw [mergedZero1191 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1193 : merged1193 = Integer.Sparse.merge merged1190 merged1192 := by decide +kernel

theorem mergedZero1193 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1193 x = 0 := by
  rw [mergeCheck1193, Integer.Sparse.eval_merge]
  rw [mergedZero1190 x h, mergedZero1192 x h]
  simp only [add_zero]

theorem mergeCheck1194 : merged1194 = Integer.Sparse.merge merged1189 merged1193 := by decide +kernel

theorem mergedZero1194 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1194 x = 0 := by
  rw [mergeCheck1194, Integer.Sparse.eval_merge]
  rw [mergedZero1189 x h, mergedZero1193 x h]
  simp only [add_zero]

theorem mergeCheck1195 : merged1195 = Integer.Sparse.merge (Integer.Sparse.scale (19478899242369810331200) (sourceRows 1202)) (Integer.Sparse.scale (-97281281880970749878400) (sourceRows 1203)) := by decide +kernel

theorem mergedZero1195 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1195 x = 0 := by
  rw [mergeCheck1195, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1196 : merged1196 = Integer.Sparse.merge (Integer.Sparse.scale (-712140841574265600) (sourceRows 1205)) (Integer.Sparse.scale (-536858118289785600) (sourceRows 1206)) := by decide +kernel

theorem mergedZero1196 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1196 x = 0 := by
  rw [mergeCheck1196, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1197 : merged1197 = Integer.Sparse.merge (Integer.Sparse.scale (-34032876376197030393600) (sourceRows 1204)) merged1196 := by decide +kernel

theorem mergedZero1197 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1197 x = 0 := by
  rw [mergeCheck1197, Integer.Sparse.eval_merge]
  rw [mergedZero1196 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1198 : merged1198 = Integer.Sparse.merge merged1195 merged1197 := by decide +kernel

theorem mergedZero1198 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1198 x = 0 := by
  rw [mergeCheck1198, Integer.Sparse.eval_merge]
  rw [mergedZero1195 x h, mergedZero1197 x h]
  simp only [add_zero]

theorem mergeCheck1199 : merged1199 = Integer.Sparse.merge (Integer.Sparse.scale (-1073716236579571200) (sourceRows 1207)) (Integer.Sparse.scale (1761047075114611200) (sourceRows 1208)) := by decide +kernel

theorem mergedZero1199 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1199 x = 0 := by
  rw [mergeCheck1199, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1200 : merged1200 = Integer.Sparse.merge (Integer.Sparse.scale (160007693479938391852800) (sourceRows 1210)) (Integer.Sparse.scale (-113979174967344568392000) (sourceRows 1211)) := by decide +kernel

theorem mergedZero1200 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1200 x = 0 := by
  rw [mergeCheck1200, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1201 : merged1201 = Integer.Sparse.merge (Integer.Sparse.scale (880523537557305600) (sourceRows 1209)) merged1200 := by decide +kernel

theorem mergedZero1201 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1201 x = 0 := by
  rw [mergeCheck1201, Integer.Sparse.eval_merge]
  rw [mergedZero1200 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1202 : merged1202 = Integer.Sparse.merge merged1199 merged1201 := by decide +kernel

theorem mergedZero1202 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1202 x = 0 := by
  rw [mergeCheck1202, Integer.Sparse.eval_merge]
  rw [mergedZero1199 x h, mergedZero1201 x h]
  simp only [add_zero]

theorem mergeCheck1203 : merged1203 = Integer.Sparse.merge merged1198 merged1202 := by decide +kernel

theorem mergedZero1203 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1203 x = 0 := by
  rw [mergeCheck1203, Integer.Sparse.eval_merge]
  rw [mergedZero1198 x h, mergedZero1202 x h]
  simp only [add_zero]

theorem mergeCheck1204 : merged1204 = Integer.Sparse.merge merged1194 merged1203 := by decide +kernel

theorem mergedZero1204 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1204 x = 0 := by
  rw [mergeCheck1204, Integer.Sparse.eval_merge]
  rw [mergedZero1194 x h, mergedZero1203 x h]
  simp only [add_zero]

theorem mergeCheck1205 : merged1205 = Integer.Sparse.merge merged1186 merged1204 := by decide +kernel

theorem mergedZero1205 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1205 x = 0 := by
  rw [mergeCheck1205, Integer.Sparse.eval_merge]
  rw [mergedZero1186 x h, mergedZero1204 x h]
  simp only [add_zero]

theorem mergeCheck1206 : merged1206 = Integer.Sparse.merge merged1168 merged1205 := by decide +kernel

theorem mergedZero1206 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1206 x = 0 := by
  rw [mergeCheck1206, Integer.Sparse.eval_merge]
  rw [mergedZero1168 x h, mergedZero1205 x h]
  simp only [add_zero]

theorem mergeCheck1207 : merged1207 = Integer.Sparse.merge merged1131 merged1206 := by decide +kernel

theorem mergedZero1207 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1207 x = 0 := by
  rw [mergeCheck1207, Integer.Sparse.eval_merge]
  rw [mergedZero1131 x h, mergedZero1206 x h]
  simp only [add_zero]

theorem mergeCheck1208 : merged1208 = Integer.Sparse.merge merged1056 merged1207 := by decide +kernel

theorem mergedZero1208_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1208 x = 0 := by
  rw [mergeCheck1208, Integer.Sparse.eval_merge]
  rw [mergedZero1056_e x h, mergedZero1207 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1208_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1208_e_oai
