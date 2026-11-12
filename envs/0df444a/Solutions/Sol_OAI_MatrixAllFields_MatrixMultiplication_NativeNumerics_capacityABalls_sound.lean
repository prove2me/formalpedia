-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:17:44.215196+00:00
-- url     : https://prove2.me/submissions/af32a601-d8f5-4116-9648-4464abdc46f7

import Mathlib
import Definitions.Def_OAIQ254M008
import Definitions.Def_OAIQ254M009
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_1_14Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_2_13Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_3_12Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_5_10Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_7_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A3_6_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_4_8Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_5_7Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A4_6_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A5_5_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_1_14I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_2_13I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_2_13I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_3_12I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_4_11I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_4_11I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_4_11I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_5_10I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_5_10I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_2_12I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_2_12I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_2_12I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_3_11I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_3_11I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_3_11I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_4_10I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_4_10I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_4_10I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_7_7I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_7_7I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_3_10I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_4_9I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_5_8I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_5_8I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_5_8I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_6_7I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA3_6_7I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_4_8I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_4_8I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_5_7I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_5_7I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA4_6_6I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA5_5_6I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

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

end Ball

end MatrixMultiplication.AllFieldCertificates

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

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma marginalBall_sound (support : List Shape) (bs : Shape → Ball) (p : Shape → ℝ)
    (h : ∀ u ∈ support, (bs u).Encloses (p u)) (side : Fin 3) (k : Fin 17) :
    (marginalBall support bs side k).Encloses (marginal support p side k) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : u side = k.val
  · simpa only [hk, ite_true, if_true] using h u hu
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I0
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA1_1_14I0Raw_sound (a : Fin 17) :
    (CA1_1_14I0Raw a).Encloses (CA1_1_14I0Value a) := by
  exact marginalBall_sound (below (shape 1 1 14)) A1_1_14Law (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (fun u _ => A1_1_14Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA1_1_14I0Certificates_valid :
    CA1_1_14I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_1_14I0P_check : ∀ a : Fin 17, contains (CA1_1_14I0Raw a) (CA1_1_14I0P a) = true := by
  decide +kernel
lemma CA1_1_14I0P_sound (a : Fin 17) :
    (CA1_1_14I0P a).Encloses (CA1_1_14I0Value a) :=
  contains_sound (CA1_1_14I0Raw_sound a) (CA1_1_14I0P_check a)
lemma CA1_1_14I0Terms_sound (a : Fin 17) :
    (CA1_1_14I0Terms a).Encloses (Foundation.entropyTerm (CA1_1_14I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_1_14I0Certificates_valid
    (CA1_1_14I0CertificateIndex a) (CA1_1_14I0P_sound a)
lemma CA1_1_14I0Entropy_sound : CA1_1_14I0Entropy.Encloses (Foundation.finiteEntropy CA1_1_14I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_1_14I0Value CA1_1_14I0Terms CA1_1_14I0Terms_sound) (by decide +kernel)
lemma CA1_1_14I0Mass_sound : CA1_1_14I0Mass.Encloses (∑ a, CA1_1_14I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_1_14I0P CA1_1_14I0Value CA1_1_14I0P_sound) (by decide +kernel)
lemma CA1_1_14I0MassTermLog_sound : CA1_1_14I0MassTermLog.Encloses (Real.log ((∑ a, CA1_1_14I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_1_14I0Mass_sound) (w := CA1_1_14I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_1_14I0MassTerm_sound : CA1_1_14I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_1_14I0Mass_sound) CA1_1_14I0MassTermLog_sound) (by decide +kernel)
lemma CA1_1_14I0H_sound : CA1_1_14I0H.Encloses (homogeneousEntropy CA1_1_14I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I0Value CA1_1_14I0MassTerm_sound CA1_1_14I0Entropy_sound) (by decide +kernel)
lemma CA1_1_14I0_sound : CA1_1_14I0H.Encloses (stageACapacity (shape 1 1 14) 0) := by
  exact CA1_1_14I0H_sound

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA1_2_13I0Raw_sound (a : Fin 17) :
    (CA1_2_13I0Raw a).Encloses (CA1_2_13I0Value a) := by
  exact marginalBall_sound (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u _ => A1_2_13Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA1_2_13I0Certificates_valid :
    CA1_2_13I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_2_13I0P_check : ∀ a : Fin 17, contains (CA1_2_13I0Raw a) (CA1_2_13I0P a) = true := by
  decide +kernel
lemma CA1_2_13I0P_sound (a : Fin 17) :
    (CA1_2_13I0P a).Encloses (CA1_2_13I0Value a) :=
  contains_sound (CA1_2_13I0Raw_sound a) (CA1_2_13I0P_check a)
lemma CA1_2_13I0Terms_sound (a : Fin 17) :
    (CA1_2_13I0Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I0Certificates_valid
    (CA1_2_13I0CertificateIndex a) (CA1_2_13I0P_sound a)
lemma CA1_2_13I0Entropy_sound : CA1_2_13I0Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_2_13I0Value CA1_2_13I0Terms CA1_2_13I0Terms_sound) (by decide +kernel)
lemma CA1_2_13I0Mass_sound : CA1_2_13I0Mass.Encloses (∑ a, CA1_2_13I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_2_13I0P CA1_2_13I0Value CA1_2_13I0P_sound) (by decide +kernel)
lemma CA1_2_13I0MassTermLog_sound : CA1_2_13I0MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I0Mass_sound) (w := CA1_2_13I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_2_13I0MassTerm_sound : CA1_2_13I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I0Mass_sound) CA1_2_13I0MassTermLog_sound) (by decide +kernel)
lemma CA1_2_13I0H_sound : CA1_2_13I0H.Encloses (homogeneousEntropy CA1_2_13I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I0Value CA1_2_13I0MassTerm_sound CA1_2_13I0Entropy_sound) (by decide +kernel)
lemma CA1_2_13I0_sound : CA1_2_13I0H.Encloses (stageACapacity (shape 1 2 13) 0) := by
  exact CA1_2_13I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA1_3_12I0Raw_sound (a : Fin 17) :
    (CA1_3_12I0Raw a).Encloses (CA1_3_12I0Value a) := by
  exact marginalBall_sound (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (fun u _ => A1_3_12Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA1_3_12I0Certificates_valid :
    CA1_3_12I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_3_12I0P_check : ∀ a : Fin 17, contains (CA1_3_12I0Raw a) (CA1_3_12I0P a) = true := by
  decide +kernel
lemma CA1_3_12I0P_sound (a : Fin 17) :
    (CA1_3_12I0P a).Encloses (CA1_3_12I0Value a) :=
  contains_sound (CA1_3_12I0Raw_sound a) (CA1_3_12I0P_check a)
lemma CA1_3_12I0Terms_sound (a : Fin 17) :
    (CA1_3_12I0Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I0Certificates_valid
    (CA1_3_12I0CertificateIndex a) (CA1_3_12I0P_sound a)
lemma CA1_3_12I0Entropy_sound : CA1_3_12I0Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_3_12I0Value CA1_3_12I0Terms CA1_3_12I0Terms_sound) (by decide +kernel)
lemma CA1_3_12I0Mass_sound : CA1_3_12I0Mass.Encloses (∑ a, CA1_3_12I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_3_12I0P CA1_3_12I0Value CA1_3_12I0P_sound) (by decide +kernel)
lemma CA1_3_12I0MassTermLog_sound : CA1_3_12I0MassTermLog.Encloses (Real.log ((∑ a, CA1_3_12I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_3_12I0Mass_sound) (w := CA1_3_12I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_3_12I0MassTerm_sound : CA1_3_12I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_3_12I0Mass_sound) CA1_3_12I0MassTermLog_sound) (by decide +kernel)
lemma CA1_3_12I0H_sound : CA1_3_12I0H.Encloses (homogeneousEntropy CA1_3_12I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I0Value CA1_3_12I0MassTerm_sound CA1_3_12I0Entropy_sound) (by decide +kernel)
lemma CA1_3_12I0_sound : CA1_3_12I0H.Encloses (stageACapacity (shape 1 3 12) 0) := by
  exact CA1_3_12I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA1_5_10I0Raw_sound (a : Fin 17) :
    (CA1_5_10I0Raw a).Encloses (CA1_5_10I0Value a) := by
  exact marginalBall_sound (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u _ => A1_5_10Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA1_5_10I0Certificates_valid :
    CA1_5_10I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA1_5_10I0P_check : ∀ a : Fin 17, contains (CA1_5_10I0Raw a) (CA1_5_10I0P a) = true := by
  decide +kernel
lemma CA1_5_10I0P_sound (a : Fin 17) :
    (CA1_5_10I0P a).Encloses (CA1_5_10I0Value a) :=
  contains_sound (CA1_5_10I0Raw_sound a) (CA1_5_10I0P_check a)
lemma CA1_5_10I0Terms_sound (a : Fin 17) :
    (CA1_5_10I0Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I0Certificates_valid
    (CA1_5_10I0CertificateIndex a) (CA1_5_10I0P_sound a)
lemma CA1_5_10I0Entropy_sound : CA1_5_10I0Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_5_10I0Value CA1_5_10I0Terms CA1_5_10I0Terms_sound) (by decide +kernel)
lemma CA1_5_10I0Mass_sound : CA1_5_10I0Mass.Encloses (∑ a, CA1_5_10I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_5_10I0P CA1_5_10I0Value CA1_5_10I0P_sound) (by decide +kernel)
lemma CA1_5_10I0MassTermLog_sound : CA1_5_10I0MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I0Mass_sound) (w := CA1_5_10I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA1_5_10I0MassTerm_sound : CA1_5_10I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I0Mass_sound) CA1_5_10I0MassTermLog_sound) (by decide +kernel)
lemma CA1_5_10I0H_sound : CA1_5_10I0H.Encloses (homogeneousEntropy CA1_5_10I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I0Value CA1_5_10I0MassTerm_sound CA1_5_10I0Entropy_sound) (by decide +kernel)
lemma CA1_5_10I0_sound : CA1_5_10I0H.Encloses (stageACapacity (shape 1 5 10) 0) := by
  exact CA1_5_10I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA2_7_7I0Raw_sound (a : Fin 17) :
    (CA2_7_7I0Raw a).Encloses (CA2_7_7I0Value a) := by
  exact marginalBall_sound (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (fun u _ => A2_7_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA2_7_7I0Certificates_valid :
    CA2_7_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_7_7I0P_check : ∀ a : Fin 17, contains (CA2_7_7I0Raw a) (CA2_7_7I0P a) = true := by
  decide +kernel
lemma CA2_7_7I0P_sound (a : Fin 17) :
    (CA2_7_7I0P a).Encloses (CA2_7_7I0Value a) :=
  contains_sound (CA2_7_7I0Raw_sound a) (CA2_7_7I0P_check a)
lemma CA2_7_7I0Terms_sound (a : Fin 17) :
    (CA2_7_7I0Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I0Certificates_valid
    (CA2_7_7I0CertificateIndex a) (CA2_7_7I0P_sound a)
lemma CA2_7_7I0Entropy_sound : CA2_7_7I0Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_7_7I0Value CA2_7_7I0Terms CA2_7_7I0Terms_sound) (by decide +kernel)
lemma CA2_7_7I0Mass_sound : CA2_7_7I0Mass.Encloses (∑ a, CA2_7_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_7_7I0P CA2_7_7I0Value CA2_7_7I0P_sound) (by decide +kernel)
lemma CA2_7_7I0MassTermLog_sound : CA2_7_7I0MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I0Mass_sound) (w := CA2_7_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_7_7I0MassTerm_sound : CA2_7_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I0Mass_sound) CA2_7_7I0MassTermLog_sound) (by decide +kernel)
lemma CA2_7_7I0H_sound : CA2_7_7I0H.Encloses (homogeneousEntropy CA2_7_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I0Value CA2_7_7I0MassTerm_sound CA2_7_7I0Entropy_sound) (by decide +kernel)
lemma CA2_7_7I0_sound : CA2_7_7I0H.Encloses (stageACapacity (shape 2 7 7) 0) := by
  exact CA2_7_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA3_6_7I0Raw_sound (a : Fin 17) :
    (CA3_6_7I0Raw a).Encloses (CA3_6_7I0Value a) := by
  exact marginalBall_sound (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (fun u _ => A3_6_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA3_6_7I0Certificates_valid :
    CA3_6_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA3_6_7I0P_check : ∀ a : Fin 17, contains (CA3_6_7I0Raw a) (CA3_6_7I0P a) = true := by
  decide +kernel
lemma CA3_6_7I0P_sound (a : Fin 17) :
    (CA3_6_7I0P a).Encloses (CA3_6_7I0Value a) :=
  contains_sound (CA3_6_7I0Raw_sound a) (CA3_6_7I0P_check a)
lemma CA3_6_7I0Terms_sound (a : Fin 17) :
    (CA3_6_7I0Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I0Certificates_valid
    (CA3_6_7I0CertificateIndex a) (CA3_6_7I0P_sound a)
lemma CA3_6_7I0Entropy_sound : CA3_6_7I0Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_6_7I0Value CA3_6_7I0Terms CA3_6_7I0Terms_sound) (by decide +kernel)
lemma CA3_6_7I0Mass_sound : CA3_6_7I0Mass.Encloses (∑ a, CA3_6_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_6_7I0P CA3_6_7I0Value CA3_6_7I0P_sound) (by decide +kernel)
lemma CA3_6_7I0MassTermLog_sound : CA3_6_7I0MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I0Mass_sound) (w := CA3_6_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA3_6_7I0MassTerm_sound : CA3_6_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I0Mass_sound) CA3_6_7I0MassTermLog_sound) (by decide +kernel)
lemma CA3_6_7I0H_sound : CA3_6_7I0H.Encloses (homogeneousEntropy CA3_6_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I0Value CA3_6_7I0MassTerm_sound CA3_6_7I0Entropy_sound) (by decide +kernel)
lemma CA3_6_7I0_sound : CA3_6_7I0H.Encloses (stageACapacity (shape 3 6 7) 0) := by
  exact CA3_6_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_InitialProbabilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma positiveInitial_list : positiveInitial = [
  (shape 1 1 14),
  (shape 1 2 13),
  (shape 1 3 12),
  (shape 1 4 11),
  (shape 1 5 10),
  (shape 1 6 9),
  (shape 1 7 8),
  (shape 2 2 12),
  (shape 2 3 11),
  (shape 2 4 10),
  (shape 2 5 9),
  (shape 2 6 8),
  (shape 2 7 7),
  (shape 3 3 10),
  (shape 3 4 9),
  (shape 3 5 8),
  (shape 3 6 7),
  (shape 4 4 8),
  (shape 4 5 7),
  (shape 4 6 6),
  (shape 5 5 6)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA4_4_8I0Raw_sound (a : Fin 17) :
    (CA4_4_8I0Raw a).Encloses (CA4_4_8I0Value a) := by
  exact marginalBall_sound (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u _ => A4_4_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA4_4_8I0Certificates_valid :
    CA4_4_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_4_8I0P_check : ∀ a : Fin 17, contains (CA4_4_8I0Raw a) (CA4_4_8I0P a) = true := by
  decide +kernel
lemma CA4_4_8I0P_sound (a : Fin 17) :
    (CA4_4_8I0P a).Encloses (CA4_4_8I0Value a) :=
  contains_sound (CA4_4_8I0Raw_sound a) (CA4_4_8I0P_check a)
lemma CA4_4_8I0Terms_sound (a : Fin 17) :
    (CA4_4_8I0Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I0Certificates_valid
    (CA4_4_8I0CertificateIndex a) (CA4_4_8I0P_sound a)
lemma CA4_4_8I0Entropy_sound : CA4_4_8I0Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_4_8I0Value CA4_4_8I0Terms CA4_4_8I0Terms_sound) (by decide +kernel)
lemma CA4_4_8I0Mass_sound : CA4_4_8I0Mass.Encloses (∑ a, CA4_4_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_4_8I0P CA4_4_8I0Value CA4_4_8I0P_sound) (by decide +kernel)
lemma CA4_4_8I0MassTermLog_sound : CA4_4_8I0MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I0Mass_sound) (w := CA4_4_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_4_8I0MassTerm_sound : CA4_4_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I0Mass_sound) CA4_4_8I0MassTermLog_sound) (by decide +kernel)
lemma CA4_4_8I0H_sound : CA4_4_8I0H.Encloses (homogeneousEntropy CA4_4_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I0Value CA4_4_8I0MassTerm_sound CA4_4_8I0Entropy_sound) (by decide +kernel)
lemma CA4_4_8I0_sound : CA4_4_8I0H.Encloses (stageACapacity (shape 4 4 8) 0) := by
  exact CA4_4_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA4_5_7I0Raw_sound (a : Fin 17) :
    (CA4_5_7I0Raw a).Encloses (CA4_5_7I0Value a) := by
  exact marginalBall_sound (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (fun u _ => A4_5_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA4_5_7I0Certificates_valid :
    CA4_5_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_5_7I0P_check : ∀ a : Fin 17, contains (CA4_5_7I0Raw a) (CA4_5_7I0P a) = true := by
  decide +kernel
lemma CA4_5_7I0P_sound (a : Fin 17) :
    (CA4_5_7I0P a).Encloses (CA4_5_7I0Value a) :=
  contains_sound (CA4_5_7I0Raw_sound a) (CA4_5_7I0P_check a)
lemma CA4_5_7I0Terms_sound (a : Fin 17) :
    (CA4_5_7I0Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I0Certificates_valid
    (CA4_5_7I0CertificateIndex a) (CA4_5_7I0P_sound a)
lemma CA4_5_7I0Entropy_sound : CA4_5_7I0Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_5_7I0Value CA4_5_7I0Terms CA4_5_7I0Terms_sound) (by decide +kernel)
lemma CA4_5_7I0Mass_sound : CA4_5_7I0Mass.Encloses (∑ a, CA4_5_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_5_7I0P CA4_5_7I0Value CA4_5_7I0P_sound) (by decide +kernel)
lemma CA4_5_7I0MassTermLog_sound : CA4_5_7I0MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I0Mass_sound) (w := CA4_5_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_5_7I0MassTerm_sound : CA4_5_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I0Mass_sound) CA4_5_7I0MassTermLog_sound) (by decide +kernel)
lemma CA4_5_7I0H_sound : CA4_5_7I0H.Encloses (homogeneousEntropy CA4_5_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I0Value CA4_5_7I0MassTerm_sound CA4_5_7I0Entropy_sound) (by decide +kernel)
lemma CA4_5_7I0_sound : CA4_5_7I0H.Encloses (stageACapacity (shape 4 5 7) 0) := by
  exact CA4_5_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA4_6_6I0Raw_sound (a : Fin 17) :
    (CA4_6_6I0Raw a).Encloses (CA4_6_6I0Value a) := by
  exact marginalBall_sound (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (fun u _ => A4_6_6Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA4_6_6I0Certificates_valid :
    CA4_6_6I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA4_6_6I0P_check : ∀ a : Fin 17, contains (CA4_6_6I0Raw a) (CA4_6_6I0P a) = true := by
  decide +kernel
lemma CA4_6_6I0P_sound (a : Fin 17) :
    (CA4_6_6I0P a).Encloses (CA4_6_6I0Value a) :=
  contains_sound (CA4_6_6I0Raw_sound a) (CA4_6_6I0P_check a)
lemma CA4_6_6I0Terms_sound (a : Fin 17) :
    (CA4_6_6I0Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I0Certificates_valid
    (CA4_6_6I0CertificateIndex a) (CA4_6_6I0P_sound a)
lemma CA4_6_6I0Entropy_sound : CA4_6_6I0Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_6_6I0Value CA4_6_6I0Terms CA4_6_6I0Terms_sound) (by decide +kernel)
lemma CA4_6_6I0Mass_sound : CA4_6_6I0Mass.Encloses (∑ a, CA4_6_6I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_6_6I0P CA4_6_6I0Value CA4_6_6I0P_sound) (by decide +kernel)
lemma CA4_6_6I0MassTermLog_sound : CA4_6_6I0MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I0Mass_sound) (w := CA4_6_6I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA4_6_6I0MassTerm_sound : CA4_6_6I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I0Mass_sound) CA4_6_6I0MassTermLog_sound) (by decide +kernel)
lemma CA4_6_6I0H_sound : CA4_6_6I0H.Encloses (homogeneousEntropy CA4_6_6I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I0Value CA4_6_6I0MassTerm_sound CA4_6_6I0Entropy_sound) (by decide +kernel)
lemma CA4_6_6I0_sound : CA4_6_6I0H.Encloses (stageACapacity (shape 4 6 6) 0) := by
  exact CA4_6_6I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I0
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA5_5_6I0Raw_sound (a : Fin 17) :
    (CA5_5_6I0Raw a).Encloses (CA5_5_6I0Value a) := by
  exact marginalBall_sound (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (fun u _ => A5_5_6Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA5_5_6I0Certificates_valid :
    CA5_5_6I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA5_5_6I0P_check : ∀ a : Fin 17, contains (CA5_5_6I0Raw a) (CA5_5_6I0P a) = true := by
  decide +kernel
lemma CA5_5_6I0P_sound (a : Fin 17) :
    (CA5_5_6I0P a).Encloses (CA5_5_6I0Value a) :=
  contains_sound (CA5_5_6I0Raw_sound a) (CA5_5_6I0P_check a)
lemma CA5_5_6I0Terms_sound (a : Fin 17) :
    (CA5_5_6I0Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I0Certificates_valid
    (CA5_5_6I0CertificateIndex a) (CA5_5_6I0P_sound a)
lemma CA5_5_6I0Entropy_sound : CA5_5_6I0Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA5_5_6I0Value CA5_5_6I0Terms CA5_5_6I0Terms_sound) (by decide +kernel)
lemma CA5_5_6I0Mass_sound : CA5_5_6I0Mass.Encloses (∑ a, CA5_5_6I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA5_5_6I0P CA5_5_6I0Value CA5_5_6I0P_sound) (by decide +kernel)
lemma CA5_5_6I0MassTermLog_sound : CA5_5_6I0MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I0Mass_sound) (w := CA5_5_6I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA5_5_6I0MassTerm_sound : CA5_5_6I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I0Mass_sound) CA5_5_6I0MassTermLog_sound) (by decide +kernel)
lemma CA5_5_6I0H_sound : CA5_5_6I0H.Encloses (homogeneousEntropy CA5_5_6I0Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I0Value CA5_5_6I0MassTerm_sound CA5_5_6I0Entropy_sound) (by decide +kernel)
lemma CA5_5_6I0_sound : CA5_5_6I0H.Encloses (stageACapacity (shape 5 5 6) 0) := by
  exact CA5_5_6I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_NativeSharp
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
lemma capacityABalls_sound_oai (s : Shape) (hs : s ∈ positiveInitial) (i : Fin 3) :
    (capacityABalls s i).Encloses (stageACapacity s i) := by
  rw [positiveInitial_list] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · revert i
    exact forall_fin3 CA1_1_14I0_sound CA1_1_14I1_sound CA1_1_14I2_sound
  · revert i
    exact forall_fin3 CA1_2_13I0_sound CA1_2_13I1_sound CA1_2_13I2_sound
  · revert i
    exact forall_fin3 CA1_3_12I0_sound CA1_3_12I1_sound CA1_3_12I2_sound
  · revert i
    exact forall_fin3 CA1_4_11I0_sound CA1_4_11I1_sound CA1_4_11I2_sound
  · revert i
    exact forall_fin3 CA1_5_10I0_sound CA1_5_10I1_sound CA1_5_10I2_sound
  · revert i
    exact forall_fin3 CA1_6_9I0_sound CA1_6_9I1_sound CA1_6_9I2_sound
  · revert i
    exact forall_fin3 CA1_7_8I0_sound CA1_7_8I1_sound CA1_7_8I2_sound
  · revert i
    exact forall_fin3 CA2_2_12I0_sound CA2_2_12I1_sound CA2_2_12I2_sound
  · revert i
    exact forall_fin3 CA2_3_11I0_sound CA2_3_11I1_sound CA2_3_11I2_sound
  · revert i
    exact forall_fin3 CA2_4_10I0_sound CA2_4_10I1_sound CA2_4_10I2_sound
  · revert i
    exact forall_fin3 CA2_5_9I0_sound CA2_5_9I1_sound CA2_5_9I2_sound
  · revert i
    exact forall_fin3 CA2_6_8I0_sound CA2_6_8I1_sound CA2_6_8I2_sound
  · revert i
    exact forall_fin3 CA2_7_7I0_sound CA2_7_7I1_sound CA2_7_7I2_sound
  · revert i
    exact forall_fin3 CA3_3_10I0_sound CA3_3_10I1_sound CA3_3_10I2_sound
  · revert i
    exact forall_fin3 CA3_4_9I0_sound CA3_4_9I1_sound CA3_4_9I2_sound
  · revert i
    exact forall_fin3 CA3_5_8I0_sound CA3_5_8I1_sound CA3_5_8I2_sound
  · revert i
    exact forall_fin3 CA3_6_7I0_sound CA3_6_7I1_sound CA3_6_7I2_sound
  · revert i
    exact forall_fin3 CA4_4_8I0_sound CA4_4_8I1_sound CA4_4_8I2_sound
  · revert i
    exact forall_fin3 CA4_5_7I0_sound CA4_5_7I1_sound CA4_5_7I2_sound
  · revert i
    exact forall_fin3 CA4_6_6I0_sound CA4_6_6I1_sound CA4_6_6I2_sound
  · revert i
    exact forall_fin3 CA5_5_6I0_sound CA5_5_6I1_sound CA5_5_6I2_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound_oai
