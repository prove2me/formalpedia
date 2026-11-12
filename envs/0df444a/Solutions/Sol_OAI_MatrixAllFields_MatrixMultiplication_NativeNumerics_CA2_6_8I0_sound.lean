-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I0_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:17:28.627463+00:00
-- url     : https://prove2.me/submissions/f703a9c0-7be0-4c15-9e78-a6ac46ac1960

import Mathlib
import Definitions.Def_OAIQ254M008
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_6_8Law_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I0
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
lemma CA2_6_8I0Raw_sound (a : Fin 17) :
    (CA2_6_8I0Raw a).Encloses (CA2_6_8I0Value a) := by
  exact marginalBall_sound (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (fun u _ => A2_6_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
lemma CA2_6_8I0Certificates_valid :
    CA2_6_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_6_8I0P_check : ∀ a : Fin 17, contains (CA2_6_8I0Raw a) (CA2_6_8I0P a) = true := by
  decide +kernel
lemma CA2_6_8I0P_sound (a : Fin 17) :
    (CA2_6_8I0P a).Encloses (CA2_6_8I0Value a) :=
  contains_sound (CA2_6_8I0Raw_sound a) (CA2_6_8I0P_check a)
lemma CA2_6_8I0Terms_sound (a : Fin 17) :
    (CA2_6_8I0Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I0Certificates_valid
    (CA2_6_8I0CertificateIndex a) (CA2_6_8I0P_sound a)
lemma CA2_6_8I0Entropy_sound : CA2_6_8I0Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_6_8I0Value CA2_6_8I0Terms CA2_6_8I0Terms_sound) (by decide +kernel)
lemma CA2_6_8I0Mass_sound : CA2_6_8I0Mass.Encloses (∑ a, CA2_6_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_6_8I0P CA2_6_8I0Value CA2_6_8I0P_sound) (by decide +kernel)
lemma CA2_6_8I0MassTermLog_sound : CA2_6_8I0MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I0Mass_sound) (w := CA2_6_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_6_8I0MassTerm_sound : CA2_6_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I0Mass_sound) CA2_6_8I0MassTermLog_sound) (by decide +kernel)
lemma CA2_6_8I0H_sound : CA2_6_8I0H.Encloses (homogeneousEntropy CA2_6_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I0Value CA2_6_8I0MassTerm_sound CA2_6_8I0Entropy_sound) (by decide +kernel)
lemma CA2_6_8I0_sound_oai : CA2_6_8I0H.Encloses (stageACapacity (shape 2 6 8) 0) := by
  exact CA2_6_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I0_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I0_sound_oai
