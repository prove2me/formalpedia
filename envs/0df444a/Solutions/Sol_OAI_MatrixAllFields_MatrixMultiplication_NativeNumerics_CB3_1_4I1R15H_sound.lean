-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1R15H_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:37:34.384809+00:00
-- url     : https://prove2.me/submissions/170da2db-a238-4f4c-9123-f13424e50200

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I1R15Raw_sound
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

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma entropyTerm_zero_ball {p : ℝ} (hp : (Ball.exact 0).Encloses p) :
    (Ball.exact 0).Encloses (Foundation.entropyTerm p) := by
  have hb := Ball.bounds hp
  have h : p = 0 := by norm_num [Ball.lower, Ball.upper, Ball.exact] at hb <;> linarith
  simp only [h, Foundation.entropyTerm, neg_zero, zero_mul]
  simpa only [Rat.cast_zero] using Ball.exact_sound 0

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

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I1
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
lemma CB3_1_4I1R15Certificates_valid :
    CB3_1_4I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_1_4I1R15P_check : ∀ a : Fin 6, contains (CB3_1_4I1R15Raw a) (CB3_1_4I1R15P a) = true := by
  decide +kernel
lemma CB3_1_4I1R15P_sound (a : Fin 6) :
    (CB3_1_4I1R15P a).Encloses (CB3_1_4I1R15Value a) :=
  contains_sound (CB3_1_4I1R15Raw_sound a) (CB3_1_4I1R15P_check a)
lemma CB3_1_4I1R15Terms_sound (a : Fin 6) :
    (CB3_1_4I1R15Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I1R15Certificates_valid
    (CB3_1_4I1R15CertificateIndex a) (CB3_1_4I1R15P_sound a)
lemma CB3_1_4I1R15Entropy_sound : CB3_1_4I1R15Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I1R15Value CB3_1_4I1R15Terms CB3_1_4I1R15Terms_sound) (by decide +kernel)
lemma CB3_1_4I1R15Mass_sound : CB3_1_4I1R15Mass.Encloses (∑ a, CB3_1_4I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I1R15P CB3_1_4I1R15Value CB3_1_4I1R15P_sound) (by decide +kernel)
lemma CB3_1_4I1R15MassTerm_sound : CB3_1_4I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I1R15Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I1R15Mass_sound)
lemma CB3_1_4I1R15H_sound_oai : CB3_1_4I1R15H.Encloses (homogeneousEntropy CB3_1_4I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I1R15Value CB3_1_4I1R15MassTerm_sound CB3_1_4I1R15Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1R15H_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_1_4I1R15H_sound_oai
