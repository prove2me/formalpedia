-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero300_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:58:16.322878+00:00
-- url     : https://prove2.me/submissions/d91a3845-496f-4b35-81c8-898e3a5d7ca1

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E059
import Definitions.Def_OAIQ106E181
import Definitions.Def_OAIQ106E063
import Definitions.Def_OAIQ106E183
import Definitions.Def_OAIQ106E186
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck150 : merged150 = Integer.Sparse.merge (Integer.Sparse.scale (531651354063083377200) (sourceRows 151)) (Integer.Sparse.scale (353599295026714019640) (sourceRows 152)) := by decide +kernel

theorem mergedZero150 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged150 x = 0 := by
  rw [mergeCheck150, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck151 : merged151 = Integer.Sparse.merge (Integer.Sparse.scale (409886526510720) (sourceRows 153)) (Integer.Sparse.scale (3654130440375000456393600) (sourceRows 154)) := by decide +kernel

theorem mergedZero151 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged151 x = 0 := by
  rw [mergeCheck151, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck152 : merged152 = Integer.Sparse.merge merged150 merged151 := by decide +kernel

theorem mergedZero152 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged152 x = 0 := by
  rw [mergeCheck152, Integer.Sparse.eval_merge]
  rw [mergedZero150 x h, mergedZero151 x h]
  simp only [add_zero]

theorem mergeCheck153 : merged153 = Integer.Sparse.merge (Integer.Sparse.scale (-3018151436350409317929600) (sourceRows 155)) (Integer.Sparse.scale (3018151436350409317929600) (sourceRows 156)) := by decide +kernel

theorem mergedZero153 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged153 x = 0 := by
  rw [mergeCheck153, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck154 : merged154 = Integer.Sparse.merge (Integer.Sparse.scale (1864129517585769316377600) (sourceRows 158)) (Integer.Sparse.scale (-3018151436350409317929600) (sourceRows 159)) := by decide +kernel

theorem mergedZero154 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged154 x = 0 := by
  rw [mergeCheck154, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck155 : merged155 = Integer.Sparse.merge (Integer.Sparse.scale (-3018151436350409317929600) (sourceRows 157)) merged154 := by decide +kernel

theorem mergedZero155 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged155 x = 0 := by
  rw [mergeCheck155, Integer.Sparse.eval_merge]
  rw [mergedZero154 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck156 : merged156 = Integer.Sparse.merge merged153 merged155 := by decide +kernel

theorem mergedZero156 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged156 x = 0 := by
  rw [mergeCheck156, Integer.Sparse.eval_merge]
  rw [mergedZero153 x h, mergedZero155 x h]
  simp only [add_zero]

theorem mergeCheck157 : merged157 = Integer.Sparse.merge merged152 merged156 := by decide +kernel

theorem mergedZero157 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged157 x = 0 := by
  rw [mergeCheck157, Integer.Sparse.eval_merge]
  rw [mergedZero152 x h, mergedZero156 x h]
  simp only [add_zero]

theorem mergeCheck158 : merged158 = Integer.Sparse.merge (Integer.Sparse.scale (-1446699248702004154435200) (sourceRows 160)) (Integer.Sparse.scale (-3018151436350409317929600) (sourceRows 161)) := by decide +kernel

theorem mergedZero158 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged158 x = 0 := by
  rw [mergeCheck158, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck159 : merged159 = Integer.Sparse.merge (Integer.Sparse.scale (-407649785906160) (sourceRows 163)) (Integer.Sparse.scale (-2875581384789937714329600) (sourceRows 164)) := by decide +kernel

theorem mergedZero159 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged159 x = 0 := by
  rw [mergeCheck159, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck160 : merged160 = Integer.Sparse.merge (Integer.Sparse.scale (3018151436350409317929600) (sourceRows 162)) merged159 := by decide +kernel

theorem mergedZero160 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged160 x = 0 := by
  rw [mergeCheck160, Integer.Sparse.eval_merge]
  rw [mergedZero159 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck161 : merged161 = Integer.Sparse.merge merged158 merged160 := by decide +kernel

theorem mergedZero161 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged161 x = 0 := by
  rw [mergeCheck161, Integer.Sparse.eval_merge]
  rw [mergedZero158 x h, mergedZero160 x h]
  simp only [add_zero]

theorem mergeCheck162 : merged162 = Integer.Sparse.merge (Integer.Sparse.scale (166036705387268273913600) (sourceRows 165)) (Integer.Sparse.scale (-166036705387268273913600) (sourceRows 166)) := by decide +kernel

theorem mergedZero162 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged162 x = 0 := by
  rw [mergeCheck162, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck163 : merged163 = Integer.Sparse.merge (Integer.Sparse.scale (-332073410774536547827200) (sourceRows 168)) (Integer.Sparse.scale (-103817604810172902566400) (sourceRows 169)) := by decide +kernel

theorem mergedZero163 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged163 x = 0 := by
  rw [mergeCheck163, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck164 : merged164 = Integer.Sparse.merge (Integer.Sparse.scale (-767296615402756384041600) (sourceRows 167)) merged163 := by decide +kernel

theorem mergedZero164 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged164 x = 0 := by
  rw [mergeCheck164, Integer.Sparse.eval_merge]
  rw [mergedZero163 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck165 : merged165 = Integer.Sparse.merge merged162 merged164 := by decide +kernel

theorem mergedZero165 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged165 x = 0 := by
  rw [mergeCheck165, Integer.Sparse.eval_merge]
  rw [mergedZero162 x h, mergedZero164 x h]
  simp only [add_zero]

theorem mergeCheck166 : merged166 = Integer.Sparse.merge merged161 merged165 := by decide +kernel

theorem mergedZero166 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged166 x = 0 := by
  rw [mergeCheck166, Integer.Sparse.eval_merge]
  rw [mergedZero161 x h, mergedZero165 x h]
  simp only [add_zero]

theorem mergeCheck167 : merged167 = Integer.Sparse.merge merged157 merged166 := by decide +kernel

theorem mergedZero167 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged167 x = 0 := by
  rw [mergeCheck167, Integer.Sparse.eval_merge]
  rw [mergedZero157 x h, mergedZero166 x h]
  simp only [add_zero]

theorem mergeCheck168 : merged168 = Integer.Sparse.merge (Integer.Sparse.scale (-332073410774536547827200) (sourceRows 170)) (Integer.Sparse.scale (368765514765152436758400) (sourceRows 171)) := by decide +kernel

theorem mergedZero168 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged168 x = 0 := by
  rw [mergeCheck168, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck169 : merged169 = Integer.Sparse.merge (Integer.Sparse.scale (-292275755805984285686400) (sourceRows 172)) (Integer.Sparse.scale (9441103433707331746264800) (sourceRows 173)) := by decide +kernel

theorem mergedZero169 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged169 x = 0 := by
  rw [mergeCheck169, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck170 : merged170 = Integer.Sparse.merge merged168 merged169 := by decide +kernel

theorem mergedZero170 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged170 x = 0 := by
  rw [mergeCheck170, Integer.Sparse.eval_merge]
  rw [mergedZero168 x h, mergedZero169 x h]
  simp only [add_zero]

theorem mergeCheck171 : merged171 = Integer.Sparse.merge (Integer.Sparse.scale (-876827267417952857059200) (sourceRows 174)) (Integer.Sparse.scale (292275755805984285686400) (sourceRows 175)) := by decide +kernel

theorem mergedZero171 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged171 x = 0 := by
  rw [mergeCheck171, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck172 : merged172 = Integer.Sparse.merge (Integer.Sparse.scale (-1229739231584434981435200) (sourceRows 177)) (Integer.Sparse.scale (2288553837807702931200) (sourceRows 178)) := by decide +kernel

theorem mergedZero172 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged172 x = 0 := by
  rw [mergeCheck172, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck173 : merged173 = Integer.Sparse.merge (Integer.Sparse.scale (23635455212576675160) (sourceRows 176)) merged172 := by decide +kernel

theorem mergedZero173 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged173 x = 0 := by
  rw [mergeCheck173, Integer.Sparse.eval_merge]
  rw [mergedZero172 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck174 : merged174 = Integer.Sparse.merge merged171 merged173 := by decide +kernel

theorem mergedZero174 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged174 x = 0 := by
  rw [mergeCheck174, Integer.Sparse.eval_merge]
  rw [mergedZero171 x h, mergedZero173 x h]
  simp only [add_zero]

theorem mergeCheck175 : merged175 = Integer.Sparse.merge merged170 merged174 := by decide +kernel

theorem mergedZero175 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged175 x = 0 := by
  rw [mergeCheck175, Integer.Sparse.eval_merge]
  rw [mergedZero170 x h, mergedZero174 x h]
  simp only [add_zero]

theorem mergeCheck176 : merged176 = Integer.Sparse.merge (Integer.Sparse.scale (-6865661513423108793600) (sourceRows 179)) (Integer.Sparse.scale (-135426953039121851083200) (sourceRows 180)) := by decide +kernel

theorem mergedZero176 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged176 x = 0 := by
  rw [mergeCheck176, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck177 : merged177 = Integer.Sparse.merge (Integer.Sparse.scale (-505733989957293609590400) (sourceRows 182)) (Integer.Sparse.scale (-2288553837807702931200) (sourceRows 183)) := by decide +kernel

theorem mergedZero177 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged177 x = 0 := by
  rw [mergeCheck177, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck178 : merged178 = Integer.Sparse.merge (Integer.Sparse.scale (-2288553837807702931200) (sourceRows 181)) merged177 := by decide +kernel

theorem mergedZero178 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged178 x = 0 := by
  rw [mergeCheck178, Integer.Sparse.eval_merge]
  rw [mergedZero177 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck179 : merged179 = Integer.Sparse.merge merged176 merged178 := by decide +kernel

theorem mergedZero179 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged179 x = 0 := by
  rw [mergeCheck179, Integer.Sparse.eval_merge]
  rw [mergedZero176 x h, mergedZero178 x h]
  simp only [add_zero]

theorem mergeCheck180 : merged180 = Integer.Sparse.merge (Integer.Sparse.scale (-409886526510720) (sourceRows 184)) (Integer.Sparse.scale (-2147746555575129600) (sourceRows 185)) := by decide +kernel

theorem mergedZero180 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged180 x = 0 := by
  rw [mergeCheck180, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck181 : merged181 = Integer.Sparse.merge (Integer.Sparse.scale (-2629767482704223806291200) (sourceRows 187)) (Integer.Sparse.scale (-10490038272000) (sourceRows 188)) := by decide +kernel

theorem mergedZero181 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged181 x = 0 := by
  rw [mergeCheck181, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck182 : merged182 = Integer.Sparse.merge (Integer.Sparse.scale (-381639870777888722966400) (sourceRows 186)) merged181 := by decide +kernel

theorem mergedZero182 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged182 x = 0 := by
  rw [mergeCheck182, Integer.Sparse.eval_merge]
  rw [mergedZero181 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck183 : merged183 = Integer.Sparse.merge merged180 merged182 := by decide +kernel

theorem mergedZero183 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged183 x = 0 := by
  rw [mergeCheck183, Integer.Sparse.eval_merge]
  rw [mergedZero180 x h, mergedZero182 x h]
  simp only [add_zero]

theorem mergeCheck184 : merged184 = Integer.Sparse.merge merged179 merged183 := by decide +kernel

theorem mergedZero184 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged184 x = 0 := by
  rw [mergeCheck184, Integer.Sparse.eval_merge]
  rw [mergedZero179 x h, mergedZero183 x h]
  simp only [add_zero]

theorem mergeCheck185 : merged185 = Integer.Sparse.merge merged175 merged184 := by decide +kernel

theorem mergedZero185 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged185 x = 0 := by
  rw [mergeCheck185, Integer.Sparse.eval_merge]
  rw [mergedZero175 x h, mergedZero184 x h]
  simp only [add_zero]

theorem mergeCheck186 : merged186 = Integer.Sparse.merge merged167 merged185 := by decide +kernel

theorem mergedZero186 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged186 x = 0 := by
  rw [mergeCheck186, Integer.Sparse.eval_merge]
  rw [mergedZero167 x h, mergedZero185 x h]
  simp only [add_zero]

theorem mergeCheck187 : merged187 = Integer.Sparse.merge (Integer.Sparse.scale (144709735822206712063200) (sourceRows 189)) (Integer.Sparse.scale (6111519756902125610335200) (sourceRows 190)) := by decide +kernel

theorem mergedZero187 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged187 x = 0 := by
  rw [mergeCheck187, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck188 : merged188 = Integer.Sparse.merge (Integer.Sparse.scale (-6111519756902125610335200) (sourceRows 191)) (Integer.Sparse.scale (5531169153243822927703200) (sourceRows 192)) := by decide +kernel

theorem mergedZero188 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged188 x = 0 := by
  rw [mergeCheck188, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck189 : merged189 = Integer.Sparse.merge merged187 merged188 := by decide +kernel

theorem mergedZero189 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged189 x = 0 := by
  rw [mergeCheck189, Integer.Sparse.eval_merge]
  rw [mergedZero187 x h, mergedZero188 x h]
  simp only [add_zero]

theorem mergeCheck190 : merged190 = Integer.Sparse.merge (Integer.Sparse.scale (-12223039513804251220670400) (sourceRows 193)) (Integer.Sparse.scale (12224366039948317762852800) (sourceRows 194)) := by decide +kernel

theorem mergedZero190 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged190 x = 0 := by
  rw [mergeCheck190, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck191 : merged191 = Integer.Sparse.merge (Integer.Sparse.scale (6311354122080289105034400) (sourceRows 196)) (Integer.Sparse.scale (-6112183019974158881426400) (sourceRows 197)) := by decide +kernel

theorem mergedZero191 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged191 x = 0 := by
  rw [mergeCheck191, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck192 : merged192 = Integer.Sparse.merge (Integer.Sparse.scale (-6453929289023534493756000) (sourceRows 195)) merged191 := by decide +kernel

theorem mergedZero192 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged192 x = 0 := by
  rw [mergeCheck192, Integer.Sparse.eval_merge]
  rw [mergedZero191 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck193 : merged193 = Integer.Sparse.merge merged190 merged192 := by decide +kernel

theorem mergedZero193 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged193 x = 0 := by
  rw [mergeCheck193, Integer.Sparse.eval_merge]
  rw [mergedZero190 x h, mergedZero192 x h]
  simp only [add_zero]

theorem mergeCheck194 : merged194 = Integer.Sparse.merge merged189 merged193 := by decide +kernel

theorem mergedZero194 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged194 x = 0 := by
  rw [mergeCheck194, Integer.Sparse.eval_merge]
  rw [mergedZero189 x h, mergedZero193 x h]
  simp only [add_zero]

theorem mergeCheck195 : merged195 = Integer.Sparse.merge (Integer.Sparse.scale (2843292579724800) (sourceRows 198)) (Integer.Sparse.scale (414669634848000) (sourceRows 199)) := by decide +kernel

theorem mergedZero195 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged195 x = 0 := by
  rw [mergeCheck195, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck196 : merged196 = Integer.Sparse.merge (Integer.Sparse.scale (-25446233196432026843558400) (sourceRows 201)) (Integer.Sparse.scale (-217274008465362089404800) (sourceRows 202)) := by decide +kernel

theorem mergedZero196 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged196 x = 0 := by
  rw [mergeCheck196, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck197 : merged197 = Integer.Sparse.merge (Integer.Sparse.scale (20288133824018257693364400) (sourceRows 200)) merged196 := by decide +kernel

theorem mergedZero197 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged197 x = 0 := by
  rw [mergeCheck197, Integer.Sparse.eval_merge]
  rw [mergedZero196 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck198 : merged198 = Integer.Sparse.merge merged195 merged197 := by decide +kernel

theorem mergedZero198 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged198 x = 0 := by
  rw [mergeCheck198, Integer.Sparse.eval_merge]
  rw [mergedZero195 x h, mergedZero197 x h]
  simp only [add_zero]

theorem mergeCheck199 : merged199 = Integer.Sparse.merge (Integer.Sparse.scale (-25446233196432026843558400) (sourceRows 203)) (Integer.Sparse.scale (50644776025964657858227200) (sourceRows 204)) := by decide +kernel

theorem mergedZero199 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged199 x = 0 := by
  rw [mergeCheck199, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck200 : merged200 = Integer.Sparse.merge (Integer.Sparse.scale (25446233196432026843558400) (sourceRows 206)) (Integer.Sparse.scale (2622509568000) (sourceRows 207)) := by decide +kernel

theorem mergedZero200 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged200 x = 0 := by
  rw [mergeCheck200, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck201 : merged201 = Integer.Sparse.merge (Integer.Sparse.scale (-50148711596721229700544000) (sourceRows 205)) merged200 := by decide +kernel

theorem mergedZero201 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged201 x = 0 := by
  rw [mergeCheck201, Integer.Sparse.eval_merge]
  rw [mergedZero200 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck202 : merged202 = Integer.Sparse.merge merged199 merged201 := by decide +kernel

theorem mergedZero202 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged202 x = 0 := by
  rw [mergeCheck202, Integer.Sparse.eval_merge]
  rw [mergedZero199 x h, mergedZero201 x h]
  simp only [add_zero]

theorem mergeCheck203 : merged203 = Integer.Sparse.merge merged198 merged202 := by decide +kernel

theorem mergedZero203 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged203 x = 0 := by
  rw [mergeCheck203, Integer.Sparse.eval_merge]
  rw [mergedZero198 x h, mergedZero202 x h]
  simp only [add_zero]

theorem mergeCheck204 : merged204 = Integer.Sparse.merge merged194 merged203 := by decide +kernel

theorem mergedZero204 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged204 x = 0 := by
  rw [mergeCheck204, Integer.Sparse.eval_merge]
  rw [mergedZero194 x h, mergedZero203 x h]
  simp only [add_zero]

theorem mergeCheck205 : merged205 = Integer.Sparse.merge (Integer.Sparse.scale (-156947075505750713904000) (sourceRows 208)) (Integer.Sparse.scale (663263072033271091200) (sourceRows 209)) := by decide +kernel

theorem mergedZero205 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged205 x = 0 := by
  rw [mergeCheck205, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck206 : merged206 = Integer.Sparse.merge (Integer.Sparse.scale (-1326526144066542182400) (sourceRows 210)) (Integer.Sparse.scale (-555377120881223572814400) (sourceRows 211)) := by decide +kernel

theorem mergedZero206 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged206 x = 0 := by
  rw [mergeCheck206, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck207 : merged207 = Integer.Sparse.merge merged205 merged206 := by decide +kernel

theorem mergedZero207 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged207 x = 0 := by
  rw [mergeCheck207, Integer.Sparse.eval_merge]
  rw [mergedZero205 x h, mergedZero206 x h]
  simp only [add_zero]

theorem mergeCheck208 : merged208 = Integer.Sparse.merge (Integer.Sparse.scale (87011823157939014048000) (sourceRows 212)) (Integer.Sparse.scale (-146753235014400) (sourceRows 213)) := by decide +kernel

theorem mergedZero208 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged208 x = 0 := by
  rw [mergeCheck208, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck209 : merged209 = Integer.Sparse.merge (Integer.Sparse.scale (-4794046290554684523393600) (sourceRows 215)) (Integer.Sparse.scale (2473531117868584104004800) (sourceRows 216)) := by decide +kernel

theorem mergedZero209 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged209 x = 0 := by
  rw [mergeCheck209, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck210 : merged210 = Integer.Sparse.merge (Integer.Sparse.scale (1187436929071680) (sourceRows 214)) merged209 := by decide +kernel

theorem mergedZero210 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged210 x = 0 := by
  rw [mergeCheck210, Integer.Sparse.eval_merge]
  rw [mergedZero209 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck211 : merged211 = Integer.Sparse.merge merged208 merged210 := by decide +kernel

theorem mergedZero211 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged211 x = 0 := by
  rw [mergeCheck211, Integer.Sparse.eval_merge]
  rw [mergedZero208 x h, mergedZero210 x h]
  simp only [add_zero]

theorem mergeCheck212 : merged212 = Integer.Sparse.merge merged207 merged211 := by decide +kernel

theorem mergedZero212 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged212 x = 0 := by
  rw [mergeCheck212, Integer.Sparse.eval_merge]
  rw [mergedZero207 x h, mergedZero211 x h]
  simp only [add_zero]

theorem mergeCheck213 : merged213 = Integer.Sparse.merge (Integer.Sparse.scale (-2292724957233497349931200) (sourceRows 217)) (Integer.Sparse.scale (20013729284040907420454400) (sourceRows 218)) := by decide +kernel

theorem mergedZero213 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged213 x = 0 := by
  rw [mergeCheck213, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck214 : merged214 = Integer.Sparse.merge (Integer.Sparse.scale (4190711790803629593600000) (sourceRows 220)) (Integer.Sparse.scale (-2831945163326345220235200) (sourceRows 221)) := by decide +kernel

theorem mergedZero214 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged214 x = 0 := by
  rw [mergeCheck214, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck215 : merged215 = Integer.Sparse.merge (Integer.Sparse.scale (-4322652966002927924625600) (sourceRows 219)) merged214 := by decide +kernel

theorem mergedZero215 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged215 x = 0 := by
  rw [mergeCheck215, Integer.Sparse.eval_merge]
  rw [mergedZero214 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck216 : merged216 = Integer.Sparse.merge merged213 merged215 := by decide +kernel

theorem mergedZero216 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged216 x = 0 := by
  rw [mergeCheck216, Integer.Sparse.eval_merge]
  rw [mergedZero213 x h, mergedZero215 x h]
  simp only [add_zero]

theorem mergeCheck217 : merged217 = Integer.Sparse.merge (Integer.Sparse.scale (2473531117868584104004800) (sourceRows 222)) (Integer.Sparse.scale (-1912611347800802266564800) (sourceRows 223)) := by decide +kernel

theorem mergedZero217 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged217 x = 0 := by
  rw [mergeCheck217, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck218 : merged218 = Integer.Sparse.merge (Integer.Sparse.scale (-2474857644012650646187200) (sourceRows 225)) (Integer.Sparse.scale (25125394117320) (sourceRows 226)) := by decide +kernel

theorem mergedZero218 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged218 x = 0 := by
  rw [mergeCheck218, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck219 : merged219 = Integer.Sparse.merge (Integer.Sparse.scale (2834576525734102761796800) (sourceRows 224)) merged218 := by decide +kernel

theorem mergedZero219 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged219 x = 0 := by
  rw [mergeCheck219, Integer.Sparse.eval_merge]
  rw [mergedZero218 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck220 : merged220 = Integer.Sparse.merge merged217 merged219 := by decide +kernel

theorem mergedZero220 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged220 x = 0 := by
  rw [mergeCheck220, Integer.Sparse.eval_merge]
  rw [mergedZero217 x h, mergedZero219 x h]
  simp only [add_zero]

theorem mergeCheck221 : merged221 = Integer.Sparse.merge merged216 merged220 := by decide +kernel

theorem mergedZero221 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged221 x = 0 := by
  rw [mergeCheck221, Integer.Sparse.eval_merge]
  rw [mergedZero216 x h, mergedZero220 x h]
  simp only [add_zero]

theorem mergeCheck222 : merged222 = Integer.Sparse.merge merged212 merged221 := by decide +kernel

theorem mergedZero222 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged222 x = 0 := by
  rw [mergeCheck222, Integer.Sparse.eval_merge]
  rw [mergedZero212 x h, mergedZero221 x h]
  simp only [add_zero]

theorem mergeCheck223 : merged223 = Integer.Sparse.merge merged204 merged222 := by decide +kernel

theorem mergedZero223 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged223 x = 0 := by
  rw [mergeCheck223, Integer.Sparse.eval_merge]
  rw [mergedZero204 x h, mergedZero222 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck224 : merged224 = Integer.Sparse.merge merged186 merged223 := by decide +kernel

theorem mergedZero224 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged224 x = 0 := by
  rw [mergeCheck224, Integer.Sparse.eval_merge]
  rw [mergedZero186 x h, mergedZero223 x h]
  simp only [add_zero]

theorem mergeCheck225 : merged225 = Integer.Sparse.merge (Integer.Sparse.scale (59496716806586490421972800) (sourceRows 227)) (Integer.Sparse.scale (-58960774622564610969600) (sourceRows 228)) := by decide +kernel

theorem mergedZero225 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged225 x = 0 := by
  rw [mergeCheck225, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck226 : merged226 = Integer.Sparse.merge (Integer.Sparse.scale (-2847563696591576658057600) (sourceRows 229)) (Integer.Sparse.scale (-58960774622564610969600) (sourceRows 230)) := by decide +kernel

theorem mergedZero226 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged226 x = 0 := by
  rw [mergeCheck226, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck227 : merged227 = Integer.Sparse.merge merged225 merged226 := by decide +kernel

theorem mergedZero227 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged227 x = 0 := by
  rw [mergeCheck227, Integer.Sparse.eval_merge]
  rw [mergedZero225 x h, mergedZero226 x h]
  simp only [add_zero]

theorem mergeCheck228 : merged228 = Integer.Sparse.merge (Integer.Sparse.scale (37832262763056200409600) (sourceRows 231)) (Integer.Sparse.scale (-58960774622564610969600) (sourceRows 232)) := by decide +kernel

theorem mergedZero228 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged228 x = 0 := by
  rw [mergeCheck228, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck229 : merged229 = Integer.Sparse.merge (Integer.Sparse.scale (20646208053989290483200) (sourceRows 234)) (Integer.Sparse.scale (58960774622564610969600) (sourceRows 235)) := by decide +kernel

theorem mergedZero229 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged229 x = 0 := by
  rw [mergeCheck229, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck230 : merged230 = Integer.Sparse.merge (Integer.Sparse.scale (58960774622564610969600) (sourceRows 233)) merged229 := by decide +kernel

theorem mergedZero230 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged230 x = 0 := by
  rw [mergeCheck230, Integer.Sparse.eval_merge]
  rw [mergedZero229 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck231 : merged231 = Integer.Sparse.merge merged228 merged230 := by decide +kernel

theorem mergedZero231 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged231 x = 0 := by
  rw [mergeCheck231, Integer.Sparse.eval_merge]
  rw [mergedZero228 x h, mergedZero230 x h]
  simp only [add_zero]

theorem mergeCheck232 : merged232 = Integer.Sparse.merge merged227 merged231 := by decide +kernel

theorem mergedZero232 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged232 x = 0 := by
  rw [mergeCheck232, Integer.Sparse.eval_merge]
  rw [mergedZero227 x h, mergedZero231 x h]
  simp only [add_zero]

theorem mergeCheck233 : merged233 = Integer.Sparse.merge (Integer.Sparse.scale (-2622509568000) (sourceRows 236)) (Integer.Sparse.scale (651268840787665042521600) (sourceRows 237)) := by decide +kernel

theorem mergedZero233 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged233 x = 0 := by
  rw [mergeCheck233, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck234 : merged234 = Integer.Sparse.merge (Integer.Sparse.scale (6109459260561157967424000) (sourceRows 239)) (Integer.Sparse.scale (1326526144066542182400) (sourceRows 240)) := by decide +kernel

theorem mergedZero234 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged234 x = 0 := by
  rw [mergeCheck234, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck235 : merged235 = Integer.Sparse.merge (Integer.Sparse.scale (-385126741024497243273600) (sourceRows 238)) merged234 := by decide +kernel

theorem mergedZero235 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged235 x = 0 := by
  rw [mergeCheck235, Integer.Sparse.eval_merge]
  rw [mergedZero234 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck236 : merged236 = Integer.Sparse.merge merged233 merged235 := by decide +kernel

theorem mergedZero236 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged236 x = 0 := by
  rw [mergeCheck236, Integer.Sparse.eval_merge]
  rw [mergedZero233 x h, mergedZero235 x h]
  simp only [add_zero]

theorem mergeCheck237 : merged237 = Integer.Sparse.merge (Integer.Sparse.scale (-1326526144066542182400) (sourceRows 241)) (Integer.Sparse.scale (-13354397565093334873368000) (sourceRows 242)) := by decide +kernel

theorem mergedZero237 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged237 x = 0 := by
  rw [mergeCheck237, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck238 : merged238 = Integer.Sparse.merge (Integer.Sparse.scale (587478747583980) (sourceRows 244)) (Integer.Sparse.scale (-6041859930086400) (sourceRows 245)) := by decide +kernel

theorem mergedZero238 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged238 x = 0 := by
  rw [mergeCheck238, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck239 : merged239 = Integer.Sparse.merge (Integer.Sparse.scale (2034273902189108032857600) (sourceRows 243)) merged238 := by decide +kernel

theorem mergedZero239 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged239 x = 0 := by
  rw [mergeCheck239, Integer.Sparse.eval_merge]
  rw [mergedZero238 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck240 : merged240 = Integer.Sparse.merge merged237 merged239 := by decide +kernel

theorem mergedZero240 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged240 x = 0 := by
  rw [mergeCheck240, Integer.Sparse.eval_merge]
  rw [mergedZero237 x h, mergedZero239 x h]
  simp only [add_zero]

theorem mergeCheck241 : merged241 = Integer.Sparse.merge merged236 merged240 := by decide +kernel

theorem mergedZero241 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged241 x = 0 := by
  rw [mergeCheck241, Integer.Sparse.eval_merge]
  rw [mergedZero236 x h, mergedZero240 x h]
  simp only [add_zero]

theorem mergeCheck242 : merged242 = Integer.Sparse.merge merged232 merged241 := by decide +kernel

theorem mergedZero242 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged242 x = 0 := by
  rw [mergeCheck242, Integer.Sparse.eval_merge]
  rw [mergedZero232 x h, mergedZero241 x h]
  simp only [add_zero]

theorem mergeCheck243 : merged243 = Integer.Sparse.merge (Integer.Sparse.scale (7097040612521776254592800) (sourceRows 246)) (Integer.Sparse.scale (3069485604233667012038400) (sourceRows 247)) := by decide +kernel

theorem mergedZero243 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged243 x = 0 := by
  rw [mergeCheck243, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck244 : merged244 = Integer.Sparse.merge (Integer.Sparse.scale (-2325730808090843025465600) (sourceRows 248)) (Integer.Sparse.scale (3957631111781667362246400) (sourceRows 249)) := by decide +kernel

theorem mergedZero244 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged244 x = 0 := by
  rw [mergeCheck244, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck245 : merged245 = Integer.Sparse.merge merged243 merged244 := by decide +kernel

theorem mergedZero245 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged245 x = 0 := by
  rw [mergeCheck245, Integer.Sparse.eval_merge]
  rw [mergedZero243 x h, mergedZero244 x h]
  simp only [add_zero]

theorem mergeCheck246 : merged246 = Integer.Sparse.merge (Integer.Sparse.scale (-3069485604233667012038400) (sourceRows 250)) (Integer.Sparse.scale (3813240400376490998611200) (sourceRows 251)) := by decide +kernel

theorem mergedZero246 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged246 x = 0 := by
  rw [mergeCheck246, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck247 : merged247 = Integer.Sparse.merge (Integer.Sparse.scale (2325730808090843025465600) (sourceRows 253)) (Integer.Sparse.scale (-3069485604233667012038400) (sourceRows 254)) := by decide +kernel

theorem mergedZero247 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged247 x = 0 := by
  rw [mergeCheck247, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck248 : merged248 = Integer.Sparse.merge (Integer.Sparse.scale (18260605442512223233833600) (sourceRows 252)) merged247 := by decide +kernel

theorem mergedZero248 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged248 x = 0 := by
  rw [mergeCheck248, Integer.Sparse.eval_merge]
  rw [mergedZero247 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck249 : merged249 = Integer.Sparse.merge merged246 merged248 := by decide +kernel

theorem mergedZero249 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged249 x = 0 := by
  rw [mergeCheck249, Integer.Sparse.eval_merge]
  rw [mergedZero246 x h, mergedZero248 x h]
  simp only [add_zero]

theorem mergeCheck250 : merged250 = Integer.Sparse.merge merged245 merged249 := by decide +kernel

theorem mergedZero250 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged250 x = 0 := by
  rw [mergeCheck250, Integer.Sparse.eval_merge]
  rw [mergedZero245 x h, mergedZero249 x h]
  simp only [add_zero]

theorem mergeCheck251 : merged251 = Integer.Sparse.merge (Integer.Sparse.scale (-1811190530593080) (sourceRows 255)) (Integer.Sparse.scale (-12409879894877946032395200) (sourceRows 256)) := by decide +kernel

theorem mergedZero251 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged251 x = 0 := by
  rw [mergeCheck251, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck252 : merged252 = Integer.Sparse.merge (Integer.Sparse.scale (14076272547719806672080000) (sourceRows 258)) (Integer.Sparse.scale (-16142684586573828555417600) (sourceRows 259)) := by decide +kernel

theorem mergedZero252 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged252 x = 0 := by
  rw [mergeCheck252, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck253 : merged253 = Integer.Sparse.merge (Integer.Sparse.scale (-16213564582618941048268800) (sourceRows 257)) merged252 := by decide +kernel

theorem mergedZero253 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged253 x = 0 := by
  rw [mergeCheck253, Integer.Sparse.eval_merge]
  rw [mergedZero252 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck254 : merged254 = Integer.Sparse.merge merged251 merged253 := by decide +kernel

theorem mergedZero254 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged254 x = 0 := by
  rw [mergeCheck254, Integer.Sparse.eval_merge]
  rw [mergedZero251 x h, mergedZero253 x h]
  simp only [add_zero]

theorem mergeCheck255 : merged255 = Integer.Sparse.merge (Integer.Sparse.scale (16142684586573828555417600) (sourceRows 260)) (Integer.Sparse.scale (-16142684586573828555417600) (sourceRows 261)) := by decide +kernel

theorem mergedZero255 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged255 x = 0 := by
  rw [mergeCheck255, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck256 : merged256 = Integer.Sparse.merge (Integer.Sparse.scale (6036577878358405804003200) (sourceRows 263)) (Integer.Sparse.scale (16142684586573828555417600) (sourceRows 264)) := by decide +kernel

theorem mergedZero256 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged256 x = 0 := by
  rw [mergeCheck256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck257 : merged257 = Integer.Sparse.merge (Integer.Sparse.scale (16213564582618941048268800) (sourceRows 262)) merged256 := by decide +kernel

theorem mergedZero257 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged257 x = 0 := by
  rw [mergeCheck257, Integer.Sparse.eval_merge]
  rw [mergedZero256 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck258 : merged258 = Integer.Sparse.merge merged255 merged257 := by decide +kernel

theorem mergedZero258 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged258 x = 0 := by
  rw [mergeCheck258, Integer.Sparse.eval_merge]
  rw [mergedZero255 x h, mergedZero257 x h]
  simp only [add_zero]

theorem mergeCheck259 : merged259 = Integer.Sparse.merge merged254 merged258 := by decide +kernel

theorem mergedZero259 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged259 x = 0 := by
  rw [mergeCheck259, Integer.Sparse.eval_merge]
  rw [mergedZero254 x h, mergedZero258 x h]
  simp only [add_zero]

theorem mergeCheck260 : merged260 = Integer.Sparse.merge merged250 merged259 := by decide +kernel

theorem mergedZero260 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged260 x = 0 := by
  rw [mergeCheck260, Integer.Sparse.eval_merge]
  rw [mergedZero250 x h, mergedZero259 x h]
  simp only [add_zero]

theorem mergeCheck261 : merged261 = Integer.Sparse.merge merged242 merged260 := by decide +kernel

theorem mergedZero261 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged261 x = 0 := by
  rw [mergeCheck261, Integer.Sparse.eval_merge]
  rw [mergedZero242 x h, mergedZero260 x h]
  simp only [add_zero]

theorem mergeCheck262 : merged262 = Integer.Sparse.merge (Integer.Sparse.scale (-14951575285539024525926400) (sourceRows 265)) (Integer.Sparse.scale (16142684586573828555417600) (sourceRows 266)) := by decide +kernel

theorem mergedZero262 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged262 x = 0 := by
  rw [mergeCheck262, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck263 : merged263 = Integer.Sparse.merge (Integer.Sparse.scale (-144256470220800) (sourceRows 267)) (Integer.Sparse.scale (706294406432256600) (sourceRows 268)) := by decide +kernel

theorem mergedZero263 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged263 x = 0 := by
  rw [mergeCheck263, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck264 : merged264 = Integer.Sparse.merge merged262 merged263 := by decide +kernel

theorem mergedZero264 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged264 x = 0 := by
  rw [mergeCheck264, Integer.Sparse.eval_merge]
  rw [mergedZero262 x h, mergedZero263 x h]
  simp only [add_zero]

theorem mergeCheck265 : merged265 = Integer.Sparse.merge (Integer.Sparse.scale (10701520573262882580) (sourceRows 269)) (Integer.Sparse.scale (-1463241018521471748652800) (sourceRows 270)) := by decide +kernel

theorem mergedZero265 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged265 x = 0 := by
  rw [mergeCheck265, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck266 : merged266 = Integer.Sparse.merge (Integer.Sparse.scale (-2977140284511782055559200) (sourceRows 272)) (Integer.Sparse.scale (619369821537192521510400) (sourceRows 273)) := by decide +kernel

theorem mergedZero266 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged266 x = 0 := by
  rw [mergeCheck266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck267 : merged267 = Integer.Sparse.merge (Integer.Sparse.scale (469580435464271160758400) (sourceRows 271)) merged266 := by decide +kernel

theorem mergedZero267 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged267 x = 0 := by
  rw [mergeCheck267, Integer.Sparse.eval_merge]
  rw [mergedZero266 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck268 : merged268 = Integer.Sparse.merge merged265 merged267 := by decide +kernel

theorem mergedZero268 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged268 x = 0 := by
  rw [mergeCheck268, Integer.Sparse.eval_merge]
  rw [mergedZero265 x h, mergedZero267 x h]
  simp only [add_zero]

theorem mergeCheck269 : merged269 = Integer.Sparse.merge merged264 merged268 := by decide +kernel

theorem mergedZero269 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged269 x = 0 := by
  rw [mergeCheck269, Integer.Sparse.eval_merge]
  rw [mergedZero264 x h, mergedZero268 x h]
  simp only [add_zero]

theorem mergeCheck270 : merged270 = Integer.Sparse.merge (Integer.Sparse.scale (-2931544763376161040460800) (sourceRows 274)) (Integer.Sparse.scale (618043295393125979328000) (sourceRows 275)) := by decide +kernel

theorem mergedZero270 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged270 x = 0 := by
  rw [mergeCheck270, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck271 : merged271 = Integer.Sparse.merge (Integer.Sparse.scale (9135333843744461032310400) (sourceRows 277)) (Integer.Sparse.scale (-47201922997259408179200) (sourceRows 278)) := by decide +kernel

theorem mergedZero271 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged271 x = 0 := by
  rw [mergeCheck271, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck272 : merged272 = Integer.Sparse.merge (Integer.Sparse.scale (-618043295393125979328000) (sourceRows 276)) merged271 := by decide +kernel

theorem mergedZero272 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged272 x = 0 := by
  rw [mergeCheck272, Integer.Sparse.eval_merge]
  rw [mergedZero271 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck273 : merged273 = Integer.Sparse.merge merged270 merged272 := by decide +kernel

theorem mergedZero273 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged273 x = 0 := by
  rw [mergeCheck273, Integer.Sparse.eval_merge]
  rw [mergedZero270 x h, mergedZero272 x h]
  simp only [add_zero]

theorem mergeCheck274 : merged274 = Integer.Sparse.merge (Integer.Sparse.scale (1248071030699327343532800) (sourceRows 279)) (Integer.Sparse.scale (-1828116429657802316928000) (sourceRows 280)) := by decide +kernel

theorem mergedZero274 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged274 x = 0 := by
  rw [mergeCheck274, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck275 : merged275 = Integer.Sparse.merge (Integer.Sparse.scale (2013953310028800) (sourceRows 282)) (Integer.Sparse.scale (1424557199850478716960000) (sourceRows 283)) := by decide +kernel

theorem mergedZero275 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged275 x = 0 := by
  rw [mergeCheck275, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck276 : merged276 = Integer.Sparse.merge (Integer.Sparse.scale (-251744163753600) (sourceRows 281)) merged275 := by decide +kernel

theorem mergedZero276 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged276 x = 0 := by
  rw [mergeCheck276, Integer.Sparse.eval_merge]
  rw [mergedZero275 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck277 : merged277 = Integer.Sparse.merge merged274 merged276 := by decide +kernel

theorem mergedZero277 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged277 x = 0 := by
  rw [mergeCheck277, Integer.Sparse.eval_merge]
  rw [mergedZero274 x h, mergedZero276 x h]
  simp only [add_zero]

theorem mergeCheck278 : merged278 = Integer.Sparse.merge merged273 merged277 := by decide +kernel

theorem mergedZero278 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged278 x = 0 := by
  rw [mergeCheck278, Integer.Sparse.eval_merge]
  rw [mergedZero273 x h, mergedZero277 x h]
  simp only [add_zero]

theorem mergeCheck279 : merged279 = Integer.Sparse.merge merged269 merged278 := by decide +kernel

theorem mergedZero279 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged279 x = 0 := by
  rw [mergeCheck279, Integer.Sparse.eval_merge]
  rw [mergedZero269 x h, mergedZero278 x h]
  simp only [add_zero]

theorem mergeCheck280 : merged280 = Integer.Sparse.merge (Integer.Sparse.scale (743754796142823986572800) (sourceRows 284)) (Integer.Sparse.scale (-1429139075559704445283200) (sourceRows 285)) := by decide +kernel

theorem mergedZero280 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged280 x = 0 := by
  rw [mergeCheck280, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck281 : merged281 = Integer.Sparse.merge (Integer.Sparse.scale (-776564504699760) (sourceRows 286)) (Integer.Sparse.scale (-388282252349880) (sourceRows 287)) := by decide +kernel

theorem mergedZero281 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged281 x = 0 := by
  rw [mergeCheck281, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck282 : merged282 = Integer.Sparse.merge merged280 merged281 := by decide +kernel

theorem mergedZero282 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged282 x = 0 := by
  rw [mergeCheck282, Integer.Sparse.eval_merge]
  rw [mergedZero280 x h, mergedZero281 x h]
  simp only [add_zero]

theorem mergeCheck283 : merged283 = Integer.Sparse.merge (Integer.Sparse.scale (-8076533623454151213069600) (sourceRows 288)) (Integer.Sparse.scale (247690366899395828889600) (sourceRows 289)) := by decide +kernel

theorem mergedZero283 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged283 x = 0 := by
  rw [mergeCheck283, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck284 : merged284 = Integer.Sparse.merge (Integer.Sparse.scale (247690366899395828889600) (sourceRows 291)) (Integer.Sparse.scale (-247690366899395828889600) (sourceRows 292)) := by decide +kernel

theorem mergedZero284 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged284 x = 0 := by
  rw [mergeCheck284, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck285 : merged285 = Integer.Sparse.merge (Integer.Sparse.scale (-2030222078167261031424000) (sourceRows 290)) merged284 := by decide +kernel

theorem mergedZero285 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged285 x = 0 := by
  rw [mergeCheck285, Integer.Sparse.eval_merge]
  rw [mergedZero284 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck286 : merged286 = Integer.Sparse.merge merged283 merged285 := by decide +kernel

theorem mergedZero286 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged286 x = 0 := by
  rw [mergeCheck286, Integer.Sparse.eval_merge]
  rw [mergedZero283 x h, mergedZero285 x h]
  simp only [add_zero]

theorem mergeCheck287 : merged287 = Integer.Sparse.merge merged282 merged286 := by decide +kernel

theorem mergedZero287 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged287 x = 0 := by
  rw [mergeCheck287, Integer.Sparse.eval_merge]
  rw [mergedZero282 x h, mergedZero286 x h]
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

theorem mergeCheck288 : merged288 = Integer.Sparse.merge (Integer.Sparse.scale (-496064429243428157683200) (sourceRows 293)) (Integer.Sparse.scale (855979956176644652371200) (sourceRows 294)) := by decide +kernel

theorem mergedZero288 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged288 x = 0 := by
  rw [mergeCheck288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck289 : merged289 = Integer.Sparse.merge (Integer.Sparse.scale (2622509568000) (sourceRows 296)) (Integer.Sparse.scale (943420613633003780064000) (sourceRows 297)) := by decide +kernel

theorem mergedZero289 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged289 x = 0 := by
  rw [mergeCheck289, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck290 : merged290 = Integer.Sparse.merge (Integer.Sparse.scale (-247690366899395828889600) (sourceRows 295)) merged289 := by decide +kernel

theorem mergedZero290 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged290 x = 0 := by
  rw [mergeCheck290, Integer.Sparse.eval_merge]
  rw [mergedZero289 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck291 : merged291 = Integer.Sparse.merge merged288 merged290 := by decide +kernel

theorem mergedZero291 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged291 x = 0 := by
  rw [mergeCheck291, Integer.Sparse.eval_merge]
  rw [mergedZero288 x h, mergedZero290 x h]
  simp only [add_zero]

theorem mergeCheck292 : merged292 = Integer.Sparse.merge (Integer.Sparse.scale (392760897305398665724800) (sourceRows 298)) (Integer.Sparse.scale (1326526144066542182400) (sourceRows 299)) := by decide +kernel

theorem mergedZero292 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged292 x = 0 := by
  rw [mergeCheck292, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck293 : merged293 = Integer.Sparse.merge (Integer.Sparse.scale (-2598837378438000) (sourceRows 301)) (Integer.Sparse.scale (-32472953952595902424627200) (sourceRows 302)) := by decide +kernel

theorem mergedZero293 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged293 x = 0 := by
  rw [mergeCheck293, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck294 : merged294 = Integer.Sparse.merge (Integer.Sparse.scale (-1326526144066542182400) (sourceRows 300)) merged293 := by decide +kernel

theorem mergedZero294 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged294 x = 0 := by
  rw [mergeCheck294, Integer.Sparse.eval_merge]
  rw [mergedZero293 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck295 : merged295 = Integer.Sparse.merge merged292 merged294 := by decide +kernel

theorem mergedZero295 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged295 x = 0 := by
  rw [mergeCheck295, Integer.Sparse.eval_merge]
  rw [mergedZero292 x h, mergedZero294 x h]
  simp only [add_zero]

theorem mergeCheck296 : merged296 = Integer.Sparse.merge merged291 merged295 := by decide +kernel

theorem mergedZero296 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged296 x = 0 := by
  rw [mergeCheck296, Integer.Sparse.eval_merge]
  rw [mergedZero291 x h, mergedZero295 x h]
  simp only [add_zero]

theorem mergeCheck297 : merged297 = Integer.Sparse.merge merged287 merged296 := by decide +kernel

theorem mergedZero297 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged297 x = 0 := by
  rw [mergeCheck297, Integer.Sparse.eval_merge]
  rw [mergedZero287 x h, mergedZero296 x h]
  simp only [add_zero]

theorem mergeCheck298 : merged298 = Integer.Sparse.merge merged279 merged297 := by decide +kernel

theorem mergedZero298 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged298 x = 0 := by
  rw [mergeCheck298, Integer.Sparse.eval_merge]
  rw [mergedZero279 x h, mergedZero297 x h]
  simp only [add_zero]

theorem mergeCheck299 : merged299 = Integer.Sparse.merge merged261 merged298 := by decide +kernel

theorem mergedZero299 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged299 x = 0 := by
  rw [mergeCheck299, Integer.Sparse.eval_merge]
  rw [mergedZero261 x h, mergedZero298 x h]
  simp only [add_zero]

theorem mergeCheck300 : merged300 = Integer.Sparse.merge merged224 merged299 := by decide +kernel

theorem mergedZero300_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged300 x = 0 := by
  rw [mergeCheck300, Integer.Sparse.eval_merge]
  rw [mergedZero224 x h, mergedZero299 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero300_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero300_e_oai
