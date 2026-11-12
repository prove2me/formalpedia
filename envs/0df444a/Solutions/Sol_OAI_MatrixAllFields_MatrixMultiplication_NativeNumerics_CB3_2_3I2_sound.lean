-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:27:20.208028+00:00
-- url     : https://prove2.me/submissions/b89bc087-7a68-4251-8aea-a8099095f3c2

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2PairH_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R0H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R10H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R11H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R12H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R13H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R14H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R15H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R16H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R1H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R2H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R3H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R4H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R5H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R6H_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R7Entropy_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R7MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R8MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R8Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R9MassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2R9Terms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2Singles_sound
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

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

lemma singletonBall_sound {A : Type*} [Fintype A] (support : List Shape)
    (bs : Shape → Ball) (p : Shape → ℝ) (priority : Placement) (position : Fin 3)
    (be : Shape → Ball) (q : Shape → A → ℝ)
    (hp : ∀ u ∈ support, (bs u).Encloses (p u))
    (he : ∀ u ∈ support, designated priority position u →
      (be u).Encloses (homogeneousEntropy (q u))) :
    (singletonBall support bs priority position be).Encloses
      (singletonEntropy support p priority position q) := by
  apply listSumBall_sound
  intro u hu
  by_cases hk : designated priority position u
  · simpa only [hk, ite_true, if_true] using Ball.mul_sound (hp u hu) (he u hu hk)
  · simpa only [hk, ite_false, if_false, Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I2
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
lemma CB3_2_3I2R7H_sound : CB3_2_3I2R7H.Encloses (homogeneousEntropy CB3_2_3I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2R7Value CB3_2_3I2R7MassTerm_sound CB3_2_3I2R7Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2R8Entropy_sound : CB3_2_3I2R8Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2R8Value CB3_2_3I2R8Terms CB3_2_3I2R8Terms_sound) (by decide +kernel)
lemma CB3_2_3I2R8H_sound : CB3_2_3I2R8H.Encloses (homogeneousEntropy CB3_2_3I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2R8Value CB3_2_3I2R8MassTerm_sound CB3_2_3I2R8Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2R9Entropy_sound : CB3_2_3I2R9Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I2R9Value CB3_2_3I2R9Terms CB3_2_3I2R9Terms_sound) (by decide +kernel)
lemma CB3_2_3I2R9H_sound : CB3_2_3I2R9H.Encloses (homogeneousEntropy CB3_2_3I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I2R9Value CB3_2_3I2R9MassTerm_sound CB3_2_3I2R9Entropy_sound) (by decide +kernel)
lemma CB3_2_3I2ResidualEntropies_sound (k : Fin 17) :
    (CB3_2_3I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_2_3I2R0H_sound
  · exact CB3_2_3I2R1H_sound
  · exact CB3_2_3I2R2H_sound
  · exact CB3_2_3I2R3H_sound
  · exact CB3_2_3I2R4H_sound
  · exact CB3_2_3I2R5H_sound
  · exact CB3_2_3I2R6H_sound
  · exact CB3_2_3I2R7H_sound
  · exact CB3_2_3I2R8H_sound
  · exact CB3_2_3I2R9H_sound
  · exact CB3_2_3I2R10H_sound
  · exact CB3_2_3I2R11H_sound
  · exact CB3_2_3I2R12H_sound
  · exact CB3_2_3I2R13H_sound
  · exact CB3_2_3I2R14H_sound
  · exact CB3_2_3I2R15H_sound
  · exact CB3_2_3I2R16H_sound
lemma CB3_2_3I2Singleton_sound : CB3_2_3I2Singleton.Encloses
    (singletonEntropy (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2
    CB3_2_3I2Singles (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ)) (fun u _ => B3_2_3Law_sound u) CB3_2_3I2Singles_sound) (by decide +kernel)
lemma CB3_2_3I2Group_sound : CB3_2_3I2Group.Encloses
    (groupedEntropy (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 2 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_2_3I2Singleton_sound
    (finSumBall_sound 17 CB3_2_3I2ResidualEntropies _ CB3_2_3I2ResidualEntropies_sound)) (by decide +kernel)

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
lemma CB3_2_3I2_sound_oai : CB3_2_3I2H.Encloses (stageBCapacity (shape 3 2 3) 2) := by
  have hb := contains_sound (Ball.add_sound CB3_2_3I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_2_3I2Group_sound)))
    (show contains (.add CB3_2_3I2PairH (.neg (.mul (.exact 2) CB3_2_3I2Group))) CB3_2_3I2H = true by decide +kernel)
  unfold CB3_2_3I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, if_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound_oai
