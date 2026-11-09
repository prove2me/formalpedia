-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero603_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:28:59.744202+00:00
-- url     : https://prove2.me/submissions/50071974-49a2-4eab-b120-6f93a92191ea

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E186
import Definitions.Def_OAIQ106E077
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero602_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck302 : merged302 = Integer.Sparse.merge (Integer.Sparse.scale (-1799238072013198711624800) (sourceRows 303)) (Integer.Sparse.scale (-4476257151543349851873600) (sourceRows 304)) := by decide +kernel

theorem mergedZero302 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged302 x = 0 := by
  rw [mergeCheck302, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck303 : merged303 = Integer.Sparse.merge (Integer.Sparse.scale (-1998891970977386476706400) (sourceRows 305)) (Integer.Sparse.scale (-14713452582064421805043200) (sourceRows 306)) := by decide +kernel

theorem mergedZero303 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged303 x = 0 := by
  rw [mergeCheck303, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck304 : merged304 = Integer.Sparse.merge merged302 merged303 := by decide +kernel

theorem mergedZero304 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged304 x = 0 := by
  rw [mergeCheck304, Integer.Sparse.eval_merge]
  rw [mergedZero302 x h, mergedZero303 x h]
  simp only [add_zero]

theorem mergeCheck305 : merged305 = Integer.Sparse.merge (Integer.Sparse.scale (-3598476144026397423249600) (sourceRows 307)) (Integer.Sparse.scale (1799238072013198711624800) (sourceRows 308)) := by decide +kernel

theorem mergedZero305 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged305 x = 0 := by
  rw [mergeCheck305, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck306 : merged306 = Integer.Sparse.merge (Integer.Sparse.scale (-706294406432256600) (sourceRows 310)) (Integer.Sparse.scale (-10701520573262882580) (sourceRows 311)) := by decide +kernel

theorem mergedZero306 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged306 x = 0 := by
  rw [mergeCheck306, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck307 : merged307 = Integer.Sparse.merge (Integer.Sparse.scale (144256470220800) (sourceRows 309)) merged306 := by decide +kernel

theorem mergedZero307 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged307 x = 0 := by
  rw [mergeCheck307, Integer.Sparse.eval_merge]
  rw [mergedZero306 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck308 : merged308 = Integer.Sparse.merge merged305 merged307 := by decide +kernel

theorem mergedZero308 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged308 x = 0 := by
  rw [mergeCheck308, Integer.Sparse.eval_merge]
  rw [mergedZero305 x h, mergedZero307 x h]
  simp only [add_zero]

theorem mergeCheck309 : merged309 = Integer.Sparse.merge merged304 merged308 := by decide +kernel

theorem mergedZero309 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged309 x = 0 := by
  rw [mergeCheck309, Integer.Sparse.eval_merge]
  rw [mergedZero304 x h, mergedZero308 x h]
  simp only [add_zero]

theorem mergeCheck310 : merged310 = Integer.Sparse.merge (Integer.Sparse.scale (-2017097415418773889958400) (sourceRows 312)) (Integer.Sparse.scale (1429834893097687129267200) (sourceRows 313)) := by decide +kernel

theorem mergedZero310 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged310 x = 0 := by
  rw [mergeCheck310, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck311 : merged311 = Integer.Sparse.merge (Integer.Sparse.scale (-10354128020550214873912800) (sourceRows 314)) (Integer.Sparse.scale (1156087470919484259475200) (sourceRows 315)) := by decide +kernel

theorem mergedZero311 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged311 x = 0 := by
  rw [mergeCheck311, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck312 : merged312 = Integer.Sparse.merge merged310 merged311 := by decide +kernel

theorem mergedZero312 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged312 x = 0 := by
  rw [mergeCheck312, Integer.Sparse.eval_merge]
  rw [mergedZero310 x h, mergedZero311 x h]
  simp only [add_zero]

theorem mergeCheck313 : merged313 = Integer.Sparse.merge (Integer.Sparse.scale (-350980111553459340960000) (sourceRows 316)) (Integer.Sparse.scale (1157406064178756052729600) (sourceRows 317)) := by decide +kernel

theorem mergedZero313 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged313 x = 0 := by
  rw [mergeCheck313, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck314 : merged314 = Integer.Sparse.merge (Integer.Sparse.scale (425878551747600) (sourceRows 319)) (Integer.Sparse.scale (-4594319062188585716599200) (sourceRows 320)) := by decide +kernel

theorem mergedZero314 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged314 x = 0 := by
  rw [mergeCheck314, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck315 : merged315 = Integer.Sparse.merge (Integer.Sparse.scale (-2151328821905619731692800) (sourceRows 318)) merged314 := by decide +kernel

theorem mergedZero315 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged315 x = 0 := by
  rw [mergeCheck315, Integer.Sparse.eval_merge]
  rw [mergedZero314 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck316 : merged316 = Integer.Sparse.merge merged313 merged315 := by decide +kernel

theorem mergedZero316 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged316 x = 0 := by
  rw [mergeCheck316, Integer.Sparse.eval_merge]
  rw [mergedZero313 x h, mergedZero315 x h]
  simp only [add_zero]

theorem mergeCheck317 : merged317 = Integer.Sparse.merge merged312 merged316 := by decide +kernel

theorem mergedZero317 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged317 x = 0 := by
  rw [mergeCheck317, Integer.Sparse.eval_merge]
  rw [mergedZero312 x h, mergedZero316 x h]
  simp only [add_zero]

theorem mergeCheck318 : merged318 = Integer.Sparse.merge merged309 merged317 := by decide +kernel

theorem mergedZero318 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged318 x = 0 := by
  rw [mergeCheck318, Integer.Sparse.eval_merge]
  rw [mergedZero309 x h, mergedZero317 x h]
  simp only [add_zero]

theorem mergeCheck319 : merged319 = Integer.Sparse.merge (Integer.Sparse.scale (175567971090376552060800) (sourceRows 321)) (Integer.Sparse.scale (8792019507952042658402400) (sourceRows 322)) := by decide +kernel

theorem mergedZero319 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged319 x = 0 := by
  rw [mergeCheck319, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck320 : merged320 = Integer.Sparse.merge (Integer.Sparse.scale (174154286218192767244800) (sourceRows 323)) (Integer.Sparse.scale (-116076446822423192716800) (sourceRows 324)) := by decide +kernel

theorem mergedZero320 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged320 x = 0 := by
  rw [mergeCheck320, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck321 : merged321 = Integer.Sparse.merge merged319 merged320 := by decide +kernel

theorem mergedZero321 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged321 x = 0 := by
  rw [mergeCheck321, Integer.Sparse.eval_merge]
  rw [mergedZero319 x h, mergedZero320 x h]
  simp only [add_zero]

theorem mergeCheck322 : merged322 = Integer.Sparse.merge (Integer.Sparse.scale (465370338643940423433600) (sourceRows 325)) (Integer.Sparse.scale (-28864578355200) (sourceRows 326)) := by decide +kernel

theorem mergedZero322 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged322 x = 0 := by
  rw [mergeCheck322, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck323 : merged323 = Integer.Sparse.merge (Integer.Sparse.scale (738295979548824480) (sourceRows 328)) (Integer.Sparse.scale (30001075596042234423667200) (sourceRows 329)) := by decide +kernel

theorem mergedZero323 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged323 x = 0 := by
  rw [mergeCheck323, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck324 : merged324 = Integer.Sparse.merge (Integer.Sparse.scale (32106068067291826860) (sourceRows 327)) merged323 := by decide +kernel

theorem mergedZero324 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged324 x = 0 := by
  rw [mergeCheck324, Integer.Sparse.eval_merge]
  rw [mergedZero323 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck325 : merged325 = Integer.Sparse.merge merged322 merged324 := by decide +kernel

theorem mergedZero325 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged325 x = 0 := by
  rw [mergeCheck325, Integer.Sparse.eval_merge]
  rw [mergedZero322 x h, mergedZero324 x h]
  simp only [add_zero]

theorem mergeCheck326 : merged326 = Integer.Sparse.merge merged321 merged325 := by decide +kernel

theorem mergedZero326 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged326 x = 0 := by
  rw [mergeCheck326, Integer.Sparse.eval_merge]
  rw [mergedZero321 x h, mergedZero325 x h]
  simp only [add_zero]

theorem mergeCheck327 : merged327 = Integer.Sparse.merge (Integer.Sparse.scale (10564255929754205280000) (sourceRows 330)) (Integer.Sparse.scale (-22341716822069935718400) (sourceRows 331)) := by decide +kernel

theorem mergedZero327 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged327 x = 0 := by
  rw [mergeCheck327, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck328 : merged328 = Integer.Sparse.merge (Integer.Sparse.scale (-71877434658137269459200) (sourceRows 333)) (Integer.Sparse.scale (-10564255929754205280000) (sourceRows 334)) := by decide +kernel

theorem mergedZero328 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged328 x = 0 := by
  rw [mergeCheck328, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck329 : merged329 = Integer.Sparse.merge (Integer.Sparse.scale (10564255929754205280000) (sourceRows 332)) merged328 := by decide +kernel

theorem mergedZero329 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged329 x = 0 := by
  rw [mergeCheck329, Integer.Sparse.eval_merge]
  rw [mergedZero328 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck330 : merged330 = Integer.Sparse.merge merged327 merged329 := by decide +kernel

theorem mergedZero330 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged330 x = 0 := by
  rw [mergeCheck330, Integer.Sparse.eval_merge]
  rw [mergedZero327 x h, mergedZero329 x h]
  simp only [add_zero]

theorem mergeCheck331 : merged331 = Integer.Sparse.merge (Integer.Sparse.scale (-5245019136000) (sourceRows 335)) (Integer.Sparse.scale (944613039479355583545600) (sourceRows 336)) := by decide +kernel

theorem mergedZero331 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged331 x = 0 := by
  rw [mergeCheck331, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck332 : merged332 = Integer.Sparse.merge (Integer.Sparse.scale (12410763815052455256784800) (sourceRows 338)) (Integer.Sparse.scale (30800139831816192180) (sourceRows 339)) := by decide +kernel

theorem mergedZero332 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged332 x = 0 := by
  rw [mergeCheck332, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck333 : merged333 = Integer.Sparse.merge (Integer.Sparse.scale (385354457841243924835200) (sourceRows 337)) merged332 := by decide +kernel

theorem mergedZero333 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged333 x = 0 := by
  rw [mergeCheck333, Integer.Sparse.eval_merge]
  rw [mergedZero332 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck334 : merged334 = Integer.Sparse.merge merged331 merged333 := by decide +kernel

theorem mergedZero334 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged334 x = 0 := by
  rw [mergeCheck334, Integer.Sparse.eval_merge]
  rw [mergedZero331 x h, mergedZero333 x h]
  simp only [add_zero]

theorem mergeCheck335 : merged335 = Integer.Sparse.merge merged330 merged334 := by decide +kernel

theorem mergedZero335 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged335 x = 0 := by
  rw [mergeCheck335, Integer.Sparse.eval_merge]
  rw [mergedZero330 x h, mergedZero334 x h]
  simp only [add_zero]

theorem mergeCheck336 : merged336 = Integer.Sparse.merge merged326 merged335 := by decide +kernel

theorem mergedZero336 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged336 x = 0 := by
  rw [mergeCheck336, Integer.Sparse.eval_merge]
  rw [mergedZero326 x h, mergedZero335 x h]
  simp only [add_zero]

theorem mergeCheck337 : merged337 = Integer.Sparse.merge merged318 merged336 := by decide +kernel

theorem mergedZero337 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged337 x = 0 := by
  rw [mergeCheck337, Integer.Sparse.eval_merge]
  rw [mergedZero318 x h, mergedZero336 x h]
  simp only [add_zero]

theorem mergeCheck338 : merged338 = Integer.Sparse.merge (Integer.Sparse.scale (-2378879193830566777560) (sourceRows 340)) (Integer.Sparse.scale (-96901159108239896760) (sourceRows 341)) := by decide +kernel

theorem mergedZero338 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged338 x = 0 := by
  rw [mergeCheck338, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck339 : merged339 = Integer.Sparse.merge (Integer.Sparse.scale (1823030771464065576000) (sourceRows 342)) (Integer.Sparse.scale (-5016226113768038400) (sourceRows 343)) := by decide +kernel

theorem mergedZero339 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged339 x = 0 := by
  rw [mergeCheck339, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck340 : merged340 = Integer.Sparse.merge merged338 merged339 := by decide +kernel

theorem mergedZero340 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged340 x = 0 := by
  rw [mergeCheck340, Integer.Sparse.eval_merge]
  rw [mergedZero338 x h, mergedZero339 x h]
  simp only [add_zero]

theorem mergeCheck341 : merged341 = Integer.Sparse.merge (Integer.Sparse.scale (839451629509028212740) (sourceRows 344)) (Integer.Sparse.scale (-2634183394814831298390) (sourceRows 345)) := by decide +kernel

theorem mergedZero341 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged341 x = 0 := by
  rw [mergeCheck341, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck342 : merged342 = Integer.Sparse.merge (Integer.Sparse.scale (-4936728484254888433047600) (sourceRows 347)) (Integer.Sparse.scale (4950810827182419753304800) (sourceRows 348)) := by decide +kernel

theorem mergedZero342 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged342 x = 0 := by
  rw [mergeCheck342, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck343 : merged343 = Integer.Sparse.merge (Integer.Sparse.scale (1523407916067093541422000) (sourceRows 346)) merged342 := by decide +kernel

theorem mergedZero343 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged343 x = 0 := by
  rw [mergeCheck343, Integer.Sparse.eval_merge]
  rw [mergedZero342 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck344 : merged344 = Integer.Sparse.merge merged341 merged343 := by decide +kernel

theorem mergedZero344 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged344 x = 0 := by
  rw [mergeCheck344, Integer.Sparse.eval_merge]
  rw [mergedZero341 x h, mergedZero343 x h]
  simp only [add_zero]

theorem mergeCheck345 : merged345 = Integer.Sparse.merge merged340 merged344 := by decide +kernel

theorem mergedZero345 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged345 x = 0 := by
  rw [mergeCheck345, Integer.Sparse.eval_merge]
  rw [mergedZero340 x h, mergedZero344 x h]
  simp only [add_zero]

theorem mergeCheck346 : merged346 = Integer.Sparse.merge (Integer.Sparse.scale (-10490038272000) (sourceRows 349)) (Integer.Sparse.scale (-221087690677757030400) (sourceRows 350)) := by decide +kernel

theorem mergedZero346 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged346 x = 0 := by
  rw [mergeCheck346, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck347 : merged347 = Integer.Sparse.merge (Integer.Sparse.scale (53783760885386691600000) (sourceRows 352)) (Integer.Sparse.scale (694356420212425010880) (sourceRows 353)) := by decide +kernel

theorem mergedZero347 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged347 x = 0 := by
  rw [mergeCheck347, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck348 : merged348 = Integer.Sparse.merge (Integer.Sparse.scale (663263072033271091200) (sourceRows 351)) merged347 := by decide +kernel

theorem mergedZero348 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged348 x = 0 := by
  rw [mergeCheck348, Integer.Sparse.eval_merge]
  rw [mergedZero347 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck349 : merged349 = Integer.Sparse.merge merged346 merged348 := by decide +kernel

theorem mergedZero349 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged349 x = 0 := by
  rw [mergeCheck349, Integer.Sparse.eval_merge]
  rw [mergedZero346 x h, mergedZero348 x h]
  simp only [add_zero]

theorem mergeCheck350 : merged350 = Integer.Sparse.merge (Integer.Sparse.scale (-117513592071062950375200) (sourceRows 354)) (Integer.Sparse.scale (253439931365283388320) (sourceRows 355)) := by decide +kernel

theorem mergedZero350 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged350 x = 0 := by
  rw [mergeCheck350, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck351 : merged351 = Integer.Sparse.merge (Integer.Sparse.scale (44021761095231096660) (sourceRows 357)) (Integer.Sparse.scale (-120056357559833822720880) (sourceRows 358)) := by decide +kernel

theorem mergedZero351 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged351 x = 0 := by
  rw [mergeCheck351, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck352 : merged352 = Integer.Sparse.merge (Integer.Sparse.scale (-12730672953709775517600) (sourceRows 356)) merged351 := by decide +kernel

theorem mergedZero352 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged352 x = 0 := by
  rw [mergeCheck352, Integer.Sparse.eval_merge]
  rw [mergedZero351 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck353 : merged353 = Integer.Sparse.merge merged350 merged352 := by decide +kernel

theorem mergedZero353 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged353 x = 0 := by
  rw [mergeCheck353, Integer.Sparse.eval_merge]
  rw [mergedZero350 x h, mergedZero352 x h]
  simp only [add_zero]

theorem mergeCheck354 : merged354 = Integer.Sparse.merge merged349 merged353 := by decide +kernel

theorem mergedZero354 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged354 x = 0 := by
  rw [mergeCheck354, Integer.Sparse.eval_merge]
  rw [mergedZero349 x h, mergedZero353 x h]
  simp only [add_zero]

theorem mergeCheck355 : merged355 = Integer.Sparse.merge merged345 merged354 := by decide +kernel

theorem mergedZero355 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged355 x = 0 := by
  rw [mergeCheck355, Integer.Sparse.eval_merge]
  rw [mergedZero345 x h, mergedZero354 x h]
  simp only [add_zero]

theorem mergeCheck356 : merged356 = Integer.Sparse.merge (Integer.Sparse.scale (-13246629875833360406400) (sourceRows 359)) (Integer.Sparse.scale (6571961319807426940689600) (sourceRows 360)) := by decide +kernel

theorem mergedZero356 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged356 x = 0 := by
  rw [mergeCheck356, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck357 : merged357 = Integer.Sparse.merge (Integer.Sparse.scale (5463219862873973906748000) (sourceRows 361)) (Integer.Sparse.scale (-5308916669374694847609600) (sourceRows 362)) := by decide +kernel

theorem mergedZero357 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged357 x = 0 := by
  rw [mergeCheck357, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck358 : merged358 = Integer.Sparse.merge merged356 merged357 := by decide +kernel

theorem mergedZero358 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged358 x = 0 := by
  rw [mergeCheck358, Integer.Sparse.eval_merge]
  rw [mergedZero356 x h, mergedZero357 x h]
  simp only [add_zero]

theorem mergeCheck359 : merged359 = Integer.Sparse.merge (Integer.Sparse.scale (3979953379251056625112800) (sourceRows 363)) (Integer.Sparse.scale (-1273510289112488817415200) (sourceRows 364)) := by decide +kernel

theorem mergedZero359 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged359 x = 0 := by
  rw [mergeCheck359, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck360 : merged360 = Integer.Sparse.merge (Integer.Sparse.scale (107824944080337392160) (sourceRows 366)) (Integer.Sparse.scale (-10702928871099372180) (sourceRows 367)) := by decide +kernel

theorem mergedZero360 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged360 x = 0 := by
  rw [mergeCheck360, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck361 : merged361 = Integer.Sparse.merge (Integer.Sparse.scale (30426315007541038320) (sourceRows 365)) merged360 := by decide +kernel

theorem mergedZero361 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged361 x = 0 := by
  rw [mergeCheck361, Integer.Sparse.eval_merge]
  rw [mergedZero360 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck362 : merged362 = Integer.Sparse.merge merged359 merged361 := by decide +kernel

theorem mergedZero362 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged362 x = 0 := by
  rw [mergeCheck362, Integer.Sparse.eval_merge]
  rw [mergedZero359 x h, mergedZero361 x h]
  simp only [add_zero]

theorem mergeCheck363 : merged363 = Integer.Sparse.merge merged358 merged362 := by decide +kernel

theorem mergedZero363 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged363 x = 0 := by
  rw [mergeCheck363, Integer.Sparse.eval_merge]
  rw [mergedZero358 x h, mergedZero362 x h]
  simp only [add_zero]

theorem mergeCheck364 : merged364 = Integer.Sparse.merge (Integer.Sparse.scale (-14955123278711879216730) (sourceRows 368)) (Integer.Sparse.scale (-32221810120670405340) (sourceRows 369)) := by decide +kernel

theorem mergedZero364 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged364 x = 0 := by
  rw [mergeCheck364, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck365 : merged365 = Integer.Sparse.merge (Integer.Sparse.scale (293506470028800) (sourceRows 371)) (Integer.Sparse.scale (3023752853782080) (sourceRows 372)) := by decide +kernel

theorem mergedZero365 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged365 x = 0 := by
  rw [mergeCheck365, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck366 : merged366 = Integer.Sparse.merge (Integer.Sparse.scale (1221710201988303414870) (sourceRows 370)) merged365 := by decide +kernel

theorem mergedZero366 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged366 x = 0 := by
  rw [mergeCheck366, Integer.Sparse.eval_merge]
  rw [mergedZero365 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck367 : merged367 = Integer.Sparse.merge merged364 merged366 := by decide +kernel

theorem mergedZero367 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged367 x = 0 := by
  rw [mergeCheck367, Integer.Sparse.eval_merge]
  rw [mergedZero364 x h, mergedZero366 x h]
  simp only [add_zero]

theorem mergeCheck368 : merged368 = Integer.Sparse.merge (Integer.Sparse.scale (11465903790618634462744800) (sourceRows 373)) (Integer.Sparse.scale (-25443452362872836719929600) (sourceRows 374)) := by decide +kernel

theorem mergedZero368 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged368 x = 0 := by
  rw [mergeCheck368, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck369 : merged369 = Integer.Sparse.merge (Integer.Sparse.scale (-50886904725745673439859200) (sourceRows 376)) (Integer.Sparse.scale (-25443452362872836719929600) (sourceRows 377)) := by decide +kernel

theorem mergedZero369 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged369 x = 0 := by
  rw [mergeCheck369, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck370 : merged370 = Integer.Sparse.merge (Integer.Sparse.scale (51067710886380760193932800) (sourceRows 375)) merged369 := by decide +kernel

theorem mergedZero370 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged370 x = 0 := by
  rw [mergeCheck370, Integer.Sparse.eval_merge]
  rw [mergedZero369 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck371 : merged371 = Integer.Sparse.merge merged368 merged370 := by decide +kernel

theorem mergedZero371 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged371 x = 0 := by
  rw [mergeCheck371, Integer.Sparse.eval_merge]
  rw [mergedZero368 x h, mergedZero370 x h]
  simp only [add_zero]

theorem mergeCheck372 : merged372 = Integer.Sparse.merge merged367 merged371 := by decide +kernel

theorem mergedZero372 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged372 x = 0 := by
  rw [mergeCheck372, Integer.Sparse.eval_merge]
  rw [mergedZero367 x h, mergedZero371 x h]
  simp only [add_zero]

theorem mergeCheck373 : merged373 = Integer.Sparse.merge merged363 merged372 := by decide +kernel

theorem mergedZero373 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged373 x = 0 := by
  rw [mergeCheck373, Integer.Sparse.eval_merge]
  rw [mergedZero363 x h, mergedZero372 x h]
  simp only [add_zero]

theorem mergeCheck374 : merged374 = Integer.Sparse.merge merged355 merged373 := by decide +kernel

theorem mergedZero374 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged374 x = 0 := by
  rw [mergeCheck374, Integer.Sparse.eval_merge]
  rw [mergedZero355 x h, mergedZero373 x h]
  simp only [add_zero]

theorem mergeCheck375 : merged375 = Integer.Sparse.merge merged337 merged374 := by decide +kernel

theorem mergedZero375 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged375 x = 0 := by
  rw [mergeCheck375, Integer.Sparse.eval_merge]
  rw [mergedZero337 x h, mergedZero374 x h]
  simp only [add_zero]

theorem mergeCheck376 : merged376 = Integer.Sparse.merge (Integer.Sparse.scale (24871374510518360703312000) (sourceRows 378)) (Integer.Sparse.scale (25478229097823359695264000) (sourceRows 379)) := by decide +kernel

theorem mergedZero376 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged376 x = 0 := by
  rw [mergeCheck376, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck377 : merged377 = Integer.Sparse.merge (Integer.Sparse.scale (-1261988380800) (sourceRows 380)) (Integer.Sparse.scale (10196556565971131738877600) (sourceRows 381)) := by decide +kernel

theorem mergedZero377 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged377 x = 0 := by
  rw [mergeCheck377, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck378 : merged378 = Integer.Sparse.merge merged376 merged377 := by decide +kernel

theorem mergedZero378 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged378 x = 0 := by
  rw [mergeCheck378, Integer.Sparse.eval_merge]
  rw [mergedZero376 x h, mergedZero377 x h]
  simp only [add_zero]

theorem mergeCheck379 : merged379 = Integer.Sparse.merge (Integer.Sparse.scale (-34357047678051804518400) (sourceRows 382)) (Integer.Sparse.scale (5317956418985980589836800) (sourceRows 383)) := by decide +kernel

theorem mergedZero379 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged379 x = 0 := by
  rw [mergeCheck379, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck380 : merged380 = Integer.Sparse.merge (Integer.Sparse.scale (34357047678051804518400) (sourceRows 385)) (Integer.Sparse.scale (76081808058994828540800) (sourceRows 386)) := by decide +kernel

theorem mergedZero380 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged380 x = 0 := by
  rw [mergeCheck380, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck381 : merged381 = Integer.Sparse.merge (Integer.Sparse.scale (17556719946291031347878400) (sourceRows 384)) merged380 := by decide +kernel

theorem mergedZero381 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged381 x = 0 := by
  rw [mergeCheck381, Integer.Sparse.eval_merge]
  rw [mergedZero380 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck382 : merged382 = Integer.Sparse.merge merged379 merged381 := by decide +kernel

theorem mergedZero382 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged382 x = 0 := by
  rw [mergeCheck382, Integer.Sparse.eval_merge]
  rw [mergedZero379 x h, mergedZero381 x h]
  simp only [add_zero]

theorem mergeCheck383 : merged383 = Integer.Sparse.merge merged378 merged382 := by decide +kernel

theorem mergedZero383 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged383 x = 0 := by
  rw [mergeCheck383, Integer.Sparse.eval_merge]
  rw [mergedZero378 x h, mergedZero382 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck384 : merged384 = Integer.Sparse.merge (Integer.Sparse.scale (34357047678051804518400) (sourceRows 387)) (Integer.Sparse.scale (10490038272000) (sourceRows 388)) := by decide +kernel

theorem mergedZero384 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged384 x = 0 := by
  rw [mergeCheck384, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck385 : merged385 = Integer.Sparse.merge (Integer.Sparse.scale (-190714104246358559966400) (sourceRows 390)) (Integer.Sparse.scale (-1678445822675160) (sourceRows 391)) := by decide +kernel

theorem mergedZero385 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged385 x = 0 := by
  rw [mergeCheck385, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck386 : merged386 = Integer.Sparse.merge (Integer.Sparse.scale (-219465001346349603398400) (sourceRows 389)) merged385 := by decide +kernel

theorem mergedZero386 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged386 x = 0 := by
  rw [mergeCheck386, Integer.Sparse.eval_merge]
  rw [mergedZero385 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck387 : merged387 = Integer.Sparse.merge merged384 merged386 := by decide +kernel

theorem mergedZero387 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged387 x = 0 := by
  rw [mergeCheck387, Integer.Sparse.eval_merge]
  rw [mergedZero384 x h, mergedZero386 x h]
  simp only [add_zero]

theorem mergeCheck388 : merged388 = Integer.Sparse.merge (Integer.Sparse.scale (6713783290700640) (sourceRows 392)) (Integer.Sparse.scale (4199567093524388640474000) (sourceRows 393)) := by decide +kernel

theorem mergedZero388 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged388 x = 0 := by
  rw [mergeCheck388, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck389 : merged389 = Integer.Sparse.merge (Integer.Sparse.scale (-755938213445520) (sourceRows 395)) (Integer.Sparse.scale (-293506470028800) (sourceRows 396)) := by decide +kernel

theorem mergedZero389 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged389 x = 0 := by
  rw [mergeCheck389, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck390 : merged390 = Integer.Sparse.merge (Integer.Sparse.scale (10702915240138086240676800) (sourceRows 394)) merged389 := by decide +kernel

theorem mergedZero390 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged390 x = 0 := by
  rw [mergeCheck390, Integer.Sparse.eval_merge]
  rw [mergedZero389 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck391 : merged391 = Integer.Sparse.merge merged388 merged390 := by decide +kernel

theorem mergedZero391 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged391 x = 0 := by
  rw [mergeCheck391, Integer.Sparse.eval_merge]
  rw [mergedZero388 x h, mergedZero390 x h]
  simp only [add_zero]

theorem mergeCheck392 : merged392 = Integer.Sparse.merge merged387 merged391 := by decide +kernel

theorem mergedZero392 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged392 x = 0 := by
  rw [mergeCheck392, Integer.Sparse.eval_merge]
  rw [mergedZero387 x h, mergedZero391 x h]
  simp only [add_zero]

theorem mergeCheck393 : merged393 = Integer.Sparse.merge merged383 merged392 := by decide +kernel

theorem mergedZero393 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged393 x = 0 := by
  rw [mergeCheck393, Integer.Sparse.eval_merge]
  rw [mergedZero383 x h, mergedZero392 x h]
  simp only [add_zero]

theorem mergeCheck394 : merged394 = Integer.Sparse.merge (Integer.Sparse.scale (14694800001038178827601600) (sourceRows 397)) (Integer.Sparse.scale (-34776734950522975334400) (sourceRows 398)) := by decide +kernel

theorem mergedZero394 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged394 x = 0 := by
  rw [mergeCheck394, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck395 : merged395 = Integer.Sparse.merge (Integer.Sparse.scale (-2653052288133084364800) (sourceRows 399)) (Integer.Sparse.scale (921124682331709685760000) (sourceRows 400)) := by decide +kernel

theorem mergedZero395 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged395 x = 0 := by
  rw [mergeCheck395, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck396 : merged396 = Integer.Sparse.merge merged394 merged395 := by decide +kernel

theorem mergedZero396 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged396 x = 0 := by
  rw [mergeCheck396, Integer.Sparse.eval_merge]
  rw [mergedZero394 x h, mergedZero395 x h]
  simp only [add_zero]

theorem mergeCheck397 : merged397 = Integer.Sparse.merge (Integer.Sparse.scale (10555242511325550682996800) (sourceRows 401)) (Integer.Sparse.scale (-857493500754328233264000) (sourceRows 402)) := by decide +kernel

theorem mergedZero397 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged397 x = 0 := by
  rw [mergeCheck397, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck398 : merged398 = Integer.Sparse.merge (Integer.Sparse.scale (-95475156164640) (sourceRows 404)) (Integer.Sparse.scale (-804890963829525447974400) (sourceRows 405)) := by decide +kernel

theorem mergedZero398 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged398 x = 0 := by
  rw [mergeCheck398, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck399 : merged399 = Integer.Sparse.merge (Integer.Sparse.scale (66737543607473807779200) (sourceRows 403)) merged398 := by decide +kernel

theorem mergedZero399 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged399 x = 0 := by
  rw [mergeCheck399, Integer.Sparse.eval_merge]
  rw [mergedZero398 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck400 : merged400 = Integer.Sparse.merge merged397 merged399 := by decide +kernel

theorem mergedZero400 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged400 x = 0 := by
  rw [mergeCheck400, Integer.Sparse.eval_merge]
  rw [mergedZero397 x h, mergedZero399 x h]
  simp only [add_zero]

theorem mergeCheck401 : merged401 = Integer.Sparse.merge merged396 merged400 := by decide +kernel

theorem mergedZero401 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged401 x = 0 := by
  rw [mergeCheck401, Integer.Sparse.eval_merge]
  rw [mergedZero396 x h, mergedZero400 x h]
  simp only [add_zero]

theorem mergeCheck402 : merged402 = Integer.Sparse.merge (Integer.Sparse.scale (-80102054559311588563200) (sourceRows 406)) (Integer.Sparse.scale (-631338395680678408531200) (sourceRows 407)) := by decide +kernel

theorem mergedZero402 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged402 x = 0 := by
  rw [mergeCheck402, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck403 : merged403 = Integer.Sparse.merge (Integer.Sparse.scale (315677130725133953193600) (sourceRows 409)) (Integer.Sparse.scale (-163539022040146815148800) (sourceRows 410)) := by decide +kernel

theorem mergedZero403 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged403 x = 0 := by
  rw [mergeCheck403, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck404 : merged404 = Integer.Sparse.merge (Integer.Sparse.scale (-315013867653100682102400) (sourceRows 408)) merged403 := by decide +kernel

theorem mergedZero404 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged404 x = 0 := by
  rw [mergeCheck404, Integer.Sparse.eval_merge]
  rw [mergedZero403 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck405 : merged405 = Integer.Sparse.merge merged402 merged404 := by decide +kernel

theorem mergedZero405 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged405 x = 0 := by
  rw [mergeCheck405, Integer.Sparse.eval_merge]
  rw [mergedZero402 x h, mergedZero404 x h]
  simp only [add_zero]

theorem mergeCheck406 : merged406 = Integer.Sparse.merge (Integer.Sparse.scale (45891113084332810560) (sourceRows 411)) (Integer.Sparse.scale (240781914422660349480) (sourceRows 412)) := by decide +kernel

theorem mergedZero406 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged406 x = 0 := by
  rw [mergeCheck406, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck407 : merged407 = Integer.Sparse.merge (Integer.Sparse.scale (15348944199003017806854000) (sourceRows 414)) (Integer.Sparse.scale (176656425391007861443200) (sourceRows 415)) := by decide +kernel

theorem mergedZero407 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged407 x = 0 := by
  rw [mergeCheck407, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck408 : merged408 = Integer.Sparse.merge (Integer.Sparse.scale (-46489943652658681560) (sourceRows 413)) merged407 := by decide +kernel

theorem mergedZero408 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged408 x = 0 := by
  rw [mergeCheck408, Integer.Sparse.eval_merge]
  rw [mergedZero407 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck409 : merged409 = Integer.Sparse.merge merged406 merged408 := by decide +kernel

theorem mergedZero409 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged409 x = 0 := by
  rw [mergeCheck409, Integer.Sparse.eval_merge]
  rw [mergedZero406 x h, mergedZero408 x h]
  simp only [add_zero]

theorem mergeCheck410 : merged410 = Integer.Sparse.merge merged405 merged409 := by decide +kernel

theorem mergedZero410 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged410 x = 0 := by
  rw [mergeCheck410, Integer.Sparse.eval_merge]
  rw [mergedZero405 x h, mergedZero409 x h]
  simp only [add_zero]

theorem mergeCheck411 : merged411 = Integer.Sparse.merge merged401 merged410 := by decide +kernel

theorem mergedZero411 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged411 x = 0 := by
  rw [mergeCheck411, Integer.Sparse.eval_merge]
  rw [mergedZero401 x h, mergedZero410 x h]
  simp only [add_zero]

theorem mergeCheck412 : merged412 = Integer.Sparse.merge merged393 merged411 := by decide +kernel

theorem mergedZero412 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged412 x = 0 := by
  rw [mergeCheck412, Integer.Sparse.eval_merge]
  rw [mergedZero393 x h, mergedZero411 x h]
  simp only [add_zero]

theorem mergeCheck413 : merged413 = Integer.Sparse.merge (Integer.Sparse.scale (800386563089721779539200) (sourceRows 416)) (Integer.Sparse.scale (44395758303925412160) (sourceRows 417)) := by decide +kernel

theorem mergedZero413 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged413 x = 0 := by
  rw [mergeCheck413, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck414 : merged414 = Integer.Sparse.merge (Integer.Sparse.scale (-47981554901888029800) (sourceRows 418)) (Integer.Sparse.scale (3064449611145720) (sourceRows 419)) := by decide +kernel

theorem mergedZero414 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged414 x = 0 := by
  rw [mergeCheck414, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck415 : merged415 = Integer.Sparse.merge merged413 merged414 := by decide +kernel

theorem mergedZero415 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged415 x = 0 := by
  rw [mergeCheck415, Integer.Sparse.eval_merge]
  rw [mergedZero413 x h, mergedZero414 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck416 : merged416 = Integer.Sparse.merge (Integer.Sparse.scale (-23117475923243609610780000) (sourceRows 420)) (Integer.Sparse.scale (6451063194646925115559200) (sourceRows 421)) := by decide +kernel

theorem mergedZero416 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged416 x = 0 := by
  rw [mergeCheck416, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck417 : merged417 = Integer.Sparse.merge (Integer.Sparse.scale (-30438138456736198621574400) (sourceRows 423)) (Integer.Sparse.scale (12902126389293850231118400) (sourceRows 424)) := by decide +kernel

theorem mergedZero417 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged417 x = 0 := by
  rw [mergeCheck417, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck418 : merged418 = Integer.Sparse.merge (Integer.Sparse.scale (6451063194646925115559200) (sourceRows 422)) merged417 := by decide +kernel

theorem mergedZero418 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged418 x = 0 := by
  rw [mergeCheck418, Integer.Sparse.eval_merge]
  rw [mergedZero417 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck419 : merged419 = Integer.Sparse.merge merged416 merged418 := by decide +kernel

theorem mergedZero419 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged419 x = 0 := by
  rw [mergeCheck419, Integer.Sparse.eval_merge]
  rw [mergedZero416 x h, mergedZero418 x h]
  simp only [add_zero]

theorem mergeCheck420 : merged420 = Integer.Sparse.merge merged415 merged419 := by decide +kernel

theorem mergedZero420 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged420 x = 0 := by
  rw [mergeCheck420, Integer.Sparse.eval_merge]
  rw [mergedZero415 x h, mergedZero419 x h]
  simp only [add_zero]

theorem mergeCheck421 : merged421 = Integer.Sparse.merge (Integer.Sparse.scale (-6486503192669481361984800) (sourceRows 425)) (Integer.Sparse.scale (-6010686259200) (sourceRows 426)) := by decide +kernel

theorem mergedZero421 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged421 x = 0 := by
  rw [mergeCheck421, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck422 : merged422 = Integer.Sparse.merge (Integer.Sparse.scale (-2860217727077995200) (sourceRows 428)) (Integer.Sparse.scale (2817055639625029892812800) (sourceRows 429)) := by decide +kernel

theorem mergedZero422 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged422 x = 0 := by
  rw [mergeCheck422, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck423 : merged423 = Integer.Sparse.merge (Integer.Sparse.scale (-10701673009051730580) (sourceRows 427)) merged422 := by decide +kernel

theorem mergedZero423 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged423 x = 0 := by
  rw [mergeCheck423, Integer.Sparse.eval_merge]
  rw [mergedZero422 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck424 : merged424 = Integer.Sparse.merge merged421 merged423 := by decide +kernel

theorem mergedZero424 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged424 x = 0 := by
  rw [mergeCheck424, Integer.Sparse.eval_merge]
  rw [mergedZero421 x h, mergedZero423 x h]
  simp only [add_zero]

theorem mergeCheck425 : merged425 = Integer.Sparse.merge (Integer.Sparse.scale (1729822396646491796476800) (sourceRows 430)) (Integer.Sparse.scale (-1800702392691604289328000) (sourceRows 431)) := by decide +kernel

theorem mergedZero425 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged425 x = 0 := by
  rw [mergeCheck425, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck426 : merged426 = Integer.Sparse.merge (Integer.Sparse.scale (-3601404785383208578656000) (sourceRows 433)) (Integer.Sparse.scale (24653028547930761169430400) (sourceRows 434)) := by decide +kernel

theorem mergedZero426 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged426 x = 0 := by
  rw [mergeCheck426, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck427 : merged427 = Integer.Sparse.merge (Integer.Sparse.scale (1800702392691604289328000) (sourceRows 432)) merged426 := by decide +kernel

theorem mergedZero427 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged427 x = 0 := by
  rw [mergeCheck427, Integer.Sparse.eval_merge]
  rw [mergedZero426 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck428 : merged428 = Integer.Sparse.merge merged425 merged427 := by decide +kernel

theorem mergedZero428 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged428 x = 0 := by
  rw [mergeCheck428, Integer.Sparse.eval_merge]
  rw [mergedZero425 x h, mergedZero427 x h]
  simp only [add_zero]

theorem mergeCheck429 : merged429 = Integer.Sparse.merge merged424 merged428 := by decide +kernel

theorem mergedZero429 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged429 x = 0 := by
  rw [mergeCheck429, Integer.Sparse.eval_merge]
  rw [mergedZero424 x h, mergedZero428 x h]
  simp only [add_zero]

theorem mergeCheck430 : merged430 = Integer.Sparse.merge merged420 merged429 := by decide +kernel

theorem mergedZero430 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged430 x = 0 := by
  rw [mergeCheck430, Integer.Sparse.eval_merge]
  rw [mergedZero420 x h, mergedZero429 x h]
  simp only [add_zero]

theorem mergeCheck431 : merged431 = Integer.Sparse.merge (Integer.Sparse.scale (-3730347817558651017187200) (sourceRows 435)) (Integer.Sparse.scale (838723659276649358217600) (sourceRows 436)) := by decide +kernel

theorem mergedZero431 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged431 x = 0 := by
  rw [mergeCheck431, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck432 : merged432 = Integer.Sparse.merge (Integer.Sparse.scale (-1800702392691604289328000) (sourceRows 437)) (Integer.Sparse.scale (47737578082320) (sourceRows 438)) := by decide +kernel

theorem mergedZero432 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged432 x = 0 := by
  rw [mergeCheck432, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck433 : merged433 = Integer.Sparse.merge merged431 merged432 := by decide +kernel

theorem mergedZero433 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged433 x = 0 := by
  rw [mergeCheck433, Integer.Sparse.eval_merge]
  rw [mergedZero431 x h, mergedZero432 x h]
  simp only [add_zero]

theorem mergeCheck434 : merged434 = Integer.Sparse.merge (Integer.Sparse.scale (-922608780491397877920000) (sourceRows 439)) (Integer.Sparse.scale (2637143357509429062739200) (sourceRows 440)) := by decide +kernel

theorem mergedZero434 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged434 x = 0 := by
  rw [mergeCheck434, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck435 : merged435 = Integer.Sparse.merge (Integer.Sparse.scale (-7932884794748928000) (sourceRows 442)) (Integer.Sparse.scale (310087018334057435654400) (sourceRows 443)) := by decide +kernel

theorem mergedZero435 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged435 x = 0 := by
  rw [mergeCheck435, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck436 : merged436 = Integer.Sparse.merge (Integer.Sparse.scale (7932884794748928000) (sourceRows 441)) merged435 := by decide +kernel

theorem mergedZero436 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged436 x = 0 := by
  rw [mergeCheck436, Integer.Sparse.eval_merge]
  rw [mergedZero435 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck437 : merged437 = Integer.Sparse.merge merged434 merged436 := by decide +kernel

theorem mergedZero437 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged437 x = 0 := by
  rw [mergeCheck437, Integer.Sparse.eval_merge]
  rw [mergedZero434 x h, mergedZero436 x h]
  simp only [add_zero]

theorem mergeCheck438 : merged438 = Integer.Sparse.merge merged433 merged437 := by decide +kernel

theorem mergedZero438 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged438 x = 0 := by
  rw [mergeCheck438, Integer.Sparse.eval_merge]
  rw [mergedZero433 x h, mergedZero437 x h]
  simp only [add_zero]

theorem mergeCheck439 : merged439 = Integer.Sparse.merge (Integer.Sparse.scale (1747080274942800) (sourceRows 444)) (Integer.Sparse.scale (1747080274942800) (sourceRows 445)) := by decide +kernel

theorem mergedZero439 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged439 x = 0 := by
  rw [mergeCheck439, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck440 : merged440 = Integer.Sparse.merge (Integer.Sparse.scale (-5958776069433994669695) (sourceRows 447)) (Integer.Sparse.scale (48541101338864167320) (sourceRows 448)) := by decide +kernel

theorem mergedZero440 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged440 x = 0 := by
  rw [mergeCheck440, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck441 : merged441 = Integer.Sparse.merge (Integer.Sparse.scale (24557639492288332920) (sourceRows 446)) merged440 := by decide +kernel

theorem mergedZero441 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged441 x = 0 := by
  rw [mergeCheck441, Integer.Sparse.eval_merge]
  rw [mergedZero440 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck442 : merged442 = Integer.Sparse.merge merged439 merged441 := by decide +kernel

theorem mergedZero442 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged442 x = 0 := by
  rw [mergeCheck442, Integer.Sparse.eval_merge]
  rw [mergedZero439 x h, mergedZero441 x h]
  simp only [add_zero]

theorem mergeCheck443 : merged443 = Integer.Sparse.merge (Integer.Sparse.scale (34414664506234117457133600) (sourceRows 449)) (Integer.Sparse.scale (-220202136755612531654400) (sourceRows 450)) := by decide +kernel

theorem mergedZero443 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged443 x = 0 := by
  rw [mergeCheck443, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck444 : merged444 = Integer.Sparse.merge (Integer.Sparse.scale (-89062004439624827520) (sourceRows 452)) (Integer.Sparse.scale (-448709289107560384680) (sourceRows 453)) := by decide +kernel

theorem mergedZero444 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged444 x = 0 := by
  rw [mergeCheck444, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck445 : merged445 = Integer.Sparse.merge (Integer.Sparse.scale (70619469198853927665600) (sourceRows 451)) merged444 := by decide +kernel

theorem mergedZero445 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged445 x = 0 := by
  rw [mergeCheck445, Integer.Sparse.eval_merge]
  rw [mergedZero444 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck446 : merged446 = Integer.Sparse.merge merged443 merged445 := by decide +kernel

theorem mergedZero446 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged446 x = 0 := by
  rw [mergeCheck446, Integer.Sparse.eval_merge]
  rw [mergedZero443 x h, mergedZero445 x h]
  simp only [add_zero]

theorem mergeCheck447 : merged447 = Integer.Sparse.merge merged442 merged446 := by decide +kernel

theorem mergedZero447 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged447 x = 0 := by
  rw [mergeCheck447, Integer.Sparse.eval_merge]
  rw [mergedZero442 x h, mergedZero446 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck448 : merged448 = Integer.Sparse.merge merged438 merged447 := by decide +kernel

theorem mergedZero448 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged448 x = 0 := by
  rw [mergeCheck448, Integer.Sparse.eval_merge]
  rw [mergedZero438 x h, mergedZero447 x h]
  simp only [add_zero]

theorem mergeCheck449 : merged449 = Integer.Sparse.merge merged430 merged448 := by decide +kernel

theorem mergedZero449 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged449 x = 0 := by
  rw [mergeCheck449, Integer.Sparse.eval_merge]
  rw [mergedZero430 x h, mergedZero448 x h]
  simp only [add_zero]

theorem mergeCheck450 : merged450 = Integer.Sparse.merge merged412 merged449 := by decide +kernel

theorem mergedZero450 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged450 x = 0 := by
  rw [mergeCheck450, Integer.Sparse.eval_merge]
  rw [mergedZero412 x h, mergedZero449 x h]
  simp only [add_zero]

theorem mergeCheck451 : merged451 = Integer.Sparse.merge merged375 merged450 := by decide +kernel

theorem mergedZero451 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged451 x = 0 := by
  rw [mergeCheck451, Integer.Sparse.eval_merge]
  rw [mergedZero375 x h, mergedZero450 x h]
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

theorem mergeCheck603 : merged603 = Integer.Sparse.merge merged451 merged602 := by decide +kernel

theorem mergedZero603_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged603 x = 0 := by
  rw [mergeCheck603, Integer.Sparse.eval_merge]
  rw [mergedZero451 x h, mergedZero602_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero603_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero603_e_oai
