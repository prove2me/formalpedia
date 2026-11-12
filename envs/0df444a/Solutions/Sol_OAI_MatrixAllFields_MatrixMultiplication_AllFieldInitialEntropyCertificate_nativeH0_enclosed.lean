-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:26.96028+00:00
-- url     : https://prove2.me/submissions/c4f3f910-0a47-4f8d-9886-1092d65b366a

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_roundedMarginal_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_totalLogBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_totalMarginalBall_sound

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

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma finSumBall_sound (n : ℕ) (b : Fin n → Ball) (v : Fin n → ℝ)
    (h : ∀ i, (b i).Encloses (v i)) :
    (finSumBall n b).Encloses (∑ i, v i) := by
  induction n with
  | zero => simpa [finSumBall] using Ball.exact_sound 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact Ball.add_sound (h 0) (ih _ _ (fun i => h i.succ))

lemma marginalLogBall_sound (k : Fin 17) :
    (marginalLogBall k).Encloses (Real.log (AllFieldInitialEntropy.nativeInitialMarginal k)) := by
  apply checkLog_sound logTwoBall_sound (roundedMarginal_sound k)
    (w := marginalLogWitness k)
  fin_cases k <;> decide +kernel

lemma entropySumBall_sound :
    entropySumBall.Encloses (MatrixMultiplication.Foundation.finiteEntropy
      AllFieldInitialEntropy.nativeInitialMarginal) := by
  apply finSumBall_sound
  intro k
  have h := Ball.neg_sound (Ball.mul_sound (roundedMarginal_sound k)
    (marginalLogBall_sound k))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold MatrixMultiplication.Foundation.entropyTerm
  ring

lemma initialEntropyRawBall_sound :
    initialEntropyRawBall.Encloses AllFieldInitialEntropy.nativeH0 := by
  exact Ball.add_sound (Ball.mul_sound totalMarginalBall_sound totalLogBall_sound)
    entropySumBall_sound
theorem nativeH0_enclosed_oai : initialEntropyBall.Encloses AllFieldInitialEntropy.nativeH0 := by
  exact contains_sound initialEntropyRawBall_sound (by decide +kernel)

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed_oai
