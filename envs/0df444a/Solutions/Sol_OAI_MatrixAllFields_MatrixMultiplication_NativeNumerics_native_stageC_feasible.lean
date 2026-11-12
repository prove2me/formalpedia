-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:56:29.136871+00:00
-- url     : https://prove2.me/submissions/136de90f-34cd-4035-9c6e-80f779fb43ac

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_capacityABalls_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_initialProbs_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeBBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeLBBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_nativeTBall_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

namespace Ball

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma forall_fin3 {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma logN2_sound : logN2.Encloses (Real.log ((2 : ℝ))) := by
  exact checkLog_sound logTwoBall_sound ((by convert Ball.exact_sound (2 : ℚ) using 1; norm_num)) (w := logN2Witness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma nativeHighBall_sound : nativeHighBall.Encloses nativeHigh := by
  exact contains_sound (Ball.mul_sound nativeTBall_sound logN2_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeSharp
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma nativeLABall_sound_0 : (nativeLABall 0).Encloses (nativeLA 0) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 0)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 0))) (by decide +kernel)
lemma nativeLABall_sound_1 : (nativeLABall 1).Encloses (nativeLA 1) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 1)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 1))) (by decide +kernel)
lemma nativeLABall_sound_2 : (nativeLABall 2).Encloses (nativeLA 2) := by
  exact contains_sound (listSumBall_sound positiveInitial
    (fun s => .mul (initialProbs s) (capacityABalls s 2)) _
    (fun s hs => Ball.mul_sound (initialProbs_sound s (List.mem_filter.mp hs).1)
      (capacityABalls_sound s hs 2))) (by decide +kernel)
lemma nativeLABall_sound (i : Fin 3) : (nativeLABall i).Encloses (nativeLA i) := by
  revert i
  exact forall_fin3 nativeLABall_sound_0 nativeLABall_sound_1 nativeLABall_sound_2

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
open AllFieldTerminalRates AllFieldInitialEntropy
lemma nativeCstarBall_sound : nativeCstarBall.Encloses nativeCstar := by
  have hb := contains_sound (Ball.add_sound nativeBBall_sound
    (Ball.mul_sound (finSumBall_sound 3 (fun i => .add (nativeLABall i) (nativeLBBall i))
      (fun i => nativeLA i + nativeLB i)
      (fun i => Ball.add_sound (nativeLABall_sound i) (nativeLBBall_sound i)))
      (show (Ball.exact (1/3)).Encloses (1/(3 : ℝ)) by
        convert Ball.exact_sound (1/3) using 1
        all_goals try with_reducible_and_instances rfl
        norm_num)))
    (show contains (.add nativeBBall
      (.mul (finSumBall 3 (fun i => .add (nativeLABall i) (nativeLBBall i))) (.exact (1/3))))
      nativeCstarBall = true by decide +kernel)
  simpa only [nativeCstar, Staggering.totalCapacity, one_div, div_eq_mul_inv, one_mul] using hb
lemma nativeCBall_sound (i : Fin 3) :
    (nativeCBall i).Encloses (nativeCstar - (nativeLA i + nativeLB i)) := by
  have hcheck : contains (.add nativeCstarBall (.neg (.add (nativeLABall i) (nativeLBBall i))))
      (nativeCBall i) = true := by fin_cases i <;> decide +kernel
  simpa only [sub_eq_add_neg] using contains_sound (Ball.add_sound nativeCstarBall_sound
    (Ball.neg_sound (Ball.add_sound (nativeLABall_sound i) (nativeLBBall_sound i)))) hcheck

theorem native_stageC_feasible_oai (i : Fin 3) :
    nativeCstar - (nativeLA i + nativeLB i) < nativeHigh := by
  have hp : (nativeCBall i).upper < nativeHighBall.lower := by fin_cases i <;> decide +kernel
  have hp' : ((nativeCBall i).upper : ℝ) < nativeHighBall.lower := by exact_mod_cast hp
  exact (Ball.bounds (nativeCBall_sound i)).2.trans_lt
    (hp'.trans_le (Ball.bounds nativeHighBall_sound).1)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.native_stageC_feasible_oai
