-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:38:46.879197+00:00
-- url     : https://prove2.me/submissions/f1260870-2fbe-426c-8a90-1240569ead35

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_4_1Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R0MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R11MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R2MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R7H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R8H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2R9H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2Singleton_sound
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

lemma exact_rat_enclosed {q r : ℚ} (h : q = r) : (Ball.exact q).Encloses (r : ℝ) := by
  rw [h]
  exact Ball.exact_sound r

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma residualBall_sound_on {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (bq : Shape → A → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (hq : ∀ u ∈ support, ∀ a, (bq u a).Encloses (q u a)) (k : Fin 17) (a : A) :
    (residualBall support bs priority position bq k a).Encloses
      (residualLaw support p priority position q k a) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : ¬ designated priority position u ∧ u (priority position) = k.val
  · simpa only [ite_eq_left hk] using Ball.mul_sound (hp u hu) (hq u hu a)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_LittleB1_3_4
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
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal3_4_1
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
lemma B3_4_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 4 1) u = B3_4_1Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma B3_4_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_4_1Little u w i).Encloses (littleLaw (shape 3 4 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_4_1Little, hu, ite_true, if_true]
    apply exact_rat_enclosed
    simp only [B3_4_1LittleRat, littleLaw, B3_4_1Binary_eq u hu]
  · simp only [B3_4_1Little, hu, ite_false, if_false]
    exact Ball.exact_sound _

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I2
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
lemma CB3_4_1I2R0Raw_sound (a : Fin 6) :
    (CB3_4_1I2R0Raw a).Encloses (CB3_4_1I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 2)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 2) a) 0 a
lemma CB3_4_1I2R0Certificates_valid :
    CB3_4_1I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I2R0P_check : ∀ a : Fin 6, contains (CB3_4_1I2R0Raw a) (CB3_4_1I2R0P a) = true := by
  decide +kernel
lemma CB3_4_1I2R0P_sound (a : Fin 6) :
    (CB3_4_1I2R0P a).Encloses (CB3_4_1I2R0Value a) :=
  contains_sound (CB3_4_1I2R0Raw_sound a) (CB3_4_1I2R0P_check a)
lemma CB3_4_1I2R0Terms_sound (a : Fin 6) :
    (CB3_4_1I2R0Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I2R0Certificates_valid
    (CB3_4_1I2R0CertificateIndex a) (CB3_4_1I2R0P_sound a)
lemma CB3_4_1I2R0Entropy_sound : CB3_4_1I2R0Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I2R0Value CB3_4_1I2R0Terms CB3_4_1I2R0Terms_sound) (by decide +kernel)
lemma CB3_4_1I2R0H_sound : CB3_4_1I2R0H.Encloses (homogeneousEntropy CB3_4_1I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I2R0Value CB3_4_1I2R0MassTerm_sound CB3_4_1I2R0Entropy_sound) (by decide +kernel)
lemma CB3_4_1I2R2Raw_sound (a : Fin 6) :
    (CB3_4_1I2R2Raw a).Encloses (CB3_4_1I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 2)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 2) a) 2 a
lemma CB3_4_1I2R2Certificates_valid :
    CB3_4_1I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I2R2P_check : ∀ a : Fin 6, contains (CB3_4_1I2R2Raw a) (CB3_4_1I2R2P a) = true := by
  decide +kernel
lemma CB3_4_1I2R2P_sound (a : Fin 6) :
    (CB3_4_1I2R2P a).Encloses (CB3_4_1I2R2Value a) :=
  contains_sound (CB3_4_1I2R2Raw_sound a) (CB3_4_1I2R2P_check a)
lemma CB3_4_1I2R2Terms_sound (a : Fin 6) :
    (CB3_4_1I2R2Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I2R2Certificates_valid
    (CB3_4_1I2R2CertificateIndex a) (CB3_4_1I2R2P_sound a)
lemma CB3_4_1I2R2Entropy_sound : CB3_4_1I2R2Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I2R2Value CB3_4_1I2R2Terms CB3_4_1I2R2Terms_sound) (by decide +kernel)
lemma CB3_4_1I2R2H_sound : CB3_4_1I2R2H.Encloses (homogeneousEntropy CB3_4_1I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I2R2Value CB3_4_1I2R2MassTerm_sound CB3_4_1I2R2Entropy_sound) (by decide +kernel)
lemma CB3_4_1I2R11Raw_sound (a : Fin 6) :
    (CB3_4_1I2R11Raw a).Encloses (CB3_4_1I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 4 1)) B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u => B3_4_1Little u ((stageBPriority (shape 3 4 1)) 2)) (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) (fun u _ => B3_4_1Law_sound u) (fun u _ a => B3_4_1Little_sound u ((stageBPriority (shape 3 4 1)) 2) a) 11 a
lemma CB3_4_1I2R11Certificates_valid :
    CB3_4_1I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_4_1I2R11P_check : ∀ a : Fin 6, contains (CB3_4_1I2R11Raw a) (CB3_4_1I2R11P a) = true := by
  decide +kernel
lemma CB3_4_1I2R11P_sound (a : Fin 6) :
    (CB3_4_1I2R11P a).Encloses (CB3_4_1I2R11Value a) :=
  contains_sound (CB3_4_1I2R11Raw_sound a) (CB3_4_1I2R11P_check a)
lemma CB3_4_1I2R11Terms_sound (a : Fin 6) :
    (CB3_4_1I2R11Terms a).Encloses (Foundation.entropyTerm (CB3_4_1I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_4_1I2R11Certificates_valid
    (CB3_4_1I2R11CertificateIndex a) (CB3_4_1I2R11P_sound a)
lemma CB3_4_1I2R11Entropy_sound : CB3_4_1I2R11Entropy.Encloses (Foundation.finiteEntropy CB3_4_1I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_4_1I2R11Value CB3_4_1I2R11Terms CB3_4_1I2R11Terms_sound) (by decide +kernel)
lemma CB3_4_1I2R11H_sound : CB3_4_1I2R11H.Encloses (homogeneousEntropy CB3_4_1I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB3_4_1I2R11Value CB3_4_1I2R11MassTerm_sound CB3_4_1I2R11Entropy_sound) (by decide +kernel)
lemma CB3_4_1I2ResidualEntropies_sound (k : Fin 17) :
    (CB3_4_1I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_4_1I2R0H_sound
  · exact CB3_4_1I2R1H_sound
  · exact CB3_4_1I2R2H_sound
  · exact CB3_4_1I2R3H_sound
  · exact CB3_4_1I2R4H_sound
  · exact CB3_4_1I2R5H_sound
  · exact CB3_4_1I2R6H_sound
  · exact CB3_4_1I2R7H_sound
  · exact CB3_4_1I2R8H_sound
  · exact CB3_4_1I2R9H_sound
  · exact CB3_4_1I2R10H_sound
  · exact CB3_4_1I2R11H_sound
  · exact CB3_4_1I2R12H_sound
  · exact CB3_4_1I2R13H_sound
  · exact CB3_4_1I2R14H_sound
  · exact CB3_4_1I2R15H_sound
  · exact CB3_4_1I2R16H_sound
lemma CB3_4_1I2Group_sound : CB3_4_1I2Group.Encloses
    (groupedEntropy (below (shape 3 4 1)) (fun u => (stageBLaw (shape 3 4 1) u : ℝ)) (stageBPriority (shape 3 4 1)) 2 (fun u a => (littleLaw (shape 3 4 1) u ((stageBPriority (shape 3 4 1)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_4_1I2Singleton_sound
    (finSumBall_sound 17 CB3_4_1I2ResidualEntropies _ CB3_4_1I2ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB3_4_1I2_sound_oai : CB3_4_1I2H.Encloses (stageBCapacity (shape 3 4 1) 2) := by
  have hb := contains_sound (Ball.add_sound CB3_4_1I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_4_1I2Group_sound)))
    (show contains (.add CB3_4_1I2PairH (.neg (.mul (.exact 2) CB3_4_1I2Group))) CB3_4_1I2H = true by decide +kernel)
  unfold CB3_4_1I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_4_1I2_sound_oai
