-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:59:28.598774+00:00
-- url     : https://prove2.me/submissions/af98d058-2f93-4ae9-b894-bbef6cbbbc68

import Mathlib
import Definitions.Def_OAIQ254M010
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_1_6Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_3_4Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_4_3Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_5_2Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B1_6_1Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_1_5Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_3_3Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B2_5_1Law_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_1_6I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_1_6I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_2_5I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_2_5I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_2_5I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_3_4I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_3_4I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_4_3I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_4_3I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_5_2I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_5_2I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_6_1I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_1_5I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_1_5I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_2_4I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_2_4I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_2_4I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_3_3I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_4_2I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_5_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB2_5_1I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_1_4I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_4_1I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_2_2I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_2_2I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_2_2I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_3_1I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_3_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_3_1I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_1_2I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_2_1I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_2_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB5_2_1I2_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB6_1_1I0_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB6_1_1I1_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB6_1_1I2_sound
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
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I0
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
lemma CB1_1_6I0Raw_sound (a : Fin 17) :
    (CB1_1_6I0Raw a).Encloses (CB1_1_6I0Value a) := by
  exact marginalBall_sound (below (shape 1 1 6)) B1_1_6Law (fun u => (stageBLaw (shape 1 1 6) u : ℝ)) (fun u _ => B1_1_6Law_sound u) ((stageBPriority (shape 1 1 6)) 0) a
lemma CB1_1_6I0Certificates_valid :
    CB1_1_6I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_1_6I0P_check : ∀ a : Fin 17, contains (CB1_1_6I0Raw a) (CB1_1_6I0P a) = true := by
  decide +kernel
lemma CB1_1_6I0P_sound (a : Fin 17) :
    (CB1_1_6I0P a).Encloses (CB1_1_6I0Value a) :=
  contains_sound (CB1_1_6I0Raw_sound a) (CB1_1_6I0P_check a)
lemma CB1_1_6I0Terms_sound (a : Fin 17) :
    (CB1_1_6I0Terms a).Encloses (Foundation.entropyTerm (CB1_1_6I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_1_6I0Certificates_valid
    (CB1_1_6I0CertificateIndex a) (CB1_1_6I0P_sound a)
lemma CB1_1_6I0Entropy_sound : CB1_1_6I0Entropy.Encloses (Foundation.finiteEntropy CB1_1_6I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_1_6I0Value CB1_1_6I0Terms CB1_1_6I0Terms_sound) (by decide +kernel)
lemma CB1_1_6I0Mass_sound : CB1_1_6I0Mass.Encloses (∑ a, CB1_1_6I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_1_6I0P CB1_1_6I0Value CB1_1_6I0P_sound) (by decide +kernel)
lemma CB1_1_6I0MassTermLog_sound : CB1_1_6I0MassTermLog.Encloses (Real.log ((∑ a, CB1_1_6I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_1_6I0Mass_sound) (w := CB1_1_6I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_1_6I0MassTerm_sound : CB1_1_6I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_1_6I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_1_6I0Mass_sound) CB1_1_6I0MassTermLog_sound) (by decide +kernel)
lemma CB1_1_6I0H_sound : CB1_1_6I0H.Encloses (homogeneousEntropy CB1_1_6I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_1_6I0Value CB1_1_6I0MassTerm_sound CB1_1_6I0Entropy_sound) (by decide +kernel)
lemma CB1_1_6I0_sound : CB1_1_6I0H.Encloses (stageBCapacity (shape 1 1 6) 0) := by
  exact CB1_1_6I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I0
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
lemma CB1_3_4I0Raw_sound (a : Fin 17) :
    (CB1_3_4I0Raw a).Encloses (CB1_3_4I0Value a) := by
  exact marginalBall_sound (below (shape 1 3 4)) B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ)) (fun u _ => B1_3_4Law_sound u) ((stageBPriority (shape 1 3 4)) 0) a
lemma CB1_3_4I0Certificates_valid :
    CB1_3_4I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_3_4I0P_check : ∀ a : Fin 17, contains (CB1_3_4I0Raw a) (CB1_3_4I0P a) = true := by
  decide +kernel
lemma CB1_3_4I0P_sound (a : Fin 17) :
    (CB1_3_4I0P a).Encloses (CB1_3_4I0Value a) :=
  contains_sound (CB1_3_4I0Raw_sound a) (CB1_3_4I0P_check a)
lemma CB1_3_4I0Terms_sound (a : Fin 17) :
    (CB1_3_4I0Terms a).Encloses (Foundation.entropyTerm (CB1_3_4I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_3_4I0Certificates_valid
    (CB1_3_4I0CertificateIndex a) (CB1_3_4I0P_sound a)
lemma CB1_3_4I0Entropy_sound : CB1_3_4I0Entropy.Encloses (Foundation.finiteEntropy CB1_3_4I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_3_4I0Value CB1_3_4I0Terms CB1_3_4I0Terms_sound) (by decide +kernel)
lemma CB1_3_4I0Mass_sound : CB1_3_4I0Mass.Encloses (∑ a, CB1_3_4I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_3_4I0P CB1_3_4I0Value CB1_3_4I0P_sound) (by decide +kernel)
lemma CB1_3_4I0MassTermLog_sound : CB1_3_4I0MassTermLog.Encloses (Real.log ((∑ a, CB1_3_4I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_3_4I0Mass_sound) (w := CB1_3_4I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_3_4I0MassTerm_sound : CB1_3_4I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_3_4I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_3_4I0Mass_sound) CB1_3_4I0MassTermLog_sound) (by decide +kernel)
lemma CB1_3_4I0H_sound : CB1_3_4I0H.Encloses (homogeneousEntropy CB1_3_4I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_3_4I0Value CB1_3_4I0MassTerm_sound CB1_3_4I0Entropy_sound) (by decide +kernel)
lemma CB1_3_4I0_sound : CB1_3_4I0H.Encloses (stageBCapacity (shape 1 3 4) 0) := by
  exact CB1_3_4I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I0
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
lemma CB1_4_3I0Raw_sound (a : Fin 17) :
    (CB1_4_3I0Raw a).Encloses (CB1_4_3I0Value a) := by
  exact marginalBall_sound (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (fun u _ => B1_4_3Law_sound u) ((stageBPriority (shape 1 4 3)) 0) a
lemma CB1_4_3I0Certificates_valid :
    CB1_4_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_4_3I0P_check : ∀ a : Fin 17, contains (CB1_4_3I0Raw a) (CB1_4_3I0P a) = true := by
  decide +kernel
lemma CB1_4_3I0P_sound (a : Fin 17) :
    (CB1_4_3I0P a).Encloses (CB1_4_3I0Value a) :=
  contains_sound (CB1_4_3I0Raw_sound a) (CB1_4_3I0P_check a)
lemma CB1_4_3I0Terms_sound (a : Fin 17) :
    (CB1_4_3I0Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I0Certificates_valid
    (CB1_4_3I0CertificateIndex a) (CB1_4_3I0P_sound a)
lemma CB1_4_3I0Entropy_sound : CB1_4_3I0Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_4_3I0Value CB1_4_3I0Terms CB1_4_3I0Terms_sound) (by decide +kernel)
lemma CB1_4_3I0Mass_sound : CB1_4_3I0Mass.Encloses (∑ a, CB1_4_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_4_3I0P CB1_4_3I0Value CB1_4_3I0P_sound) (by decide +kernel)
lemma CB1_4_3I0MassTermLog_sound : CB1_4_3I0MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I0Mass_sound) (w := CB1_4_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_4_3I0MassTerm_sound : CB1_4_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I0Mass_sound) CB1_4_3I0MassTermLog_sound) (by decide +kernel)
lemma CB1_4_3I0H_sound : CB1_4_3I0H.Encloses (homogeneousEntropy CB1_4_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I0Value CB1_4_3I0MassTerm_sound CB1_4_3I0Entropy_sound) (by decide +kernel)
lemma CB1_4_3I0_sound : CB1_4_3I0H.Encloses (stageBCapacity (shape 1 4 3) 0) := by
  exact CB1_4_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I0
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
lemma CB1_5_2I0Raw_sound (a : Fin 17) :
    (CB1_5_2I0Raw a).Encloses (CB1_5_2I0Value a) := by
  exact marginalBall_sound (below (shape 1 5 2)) B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ)) (fun u _ => B1_5_2Law_sound u) ((stageBPriority (shape 1 5 2)) 0) a
lemma CB1_5_2I0Certificates_valid :
    CB1_5_2I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_5_2I0P_check : ∀ a : Fin 17, contains (CB1_5_2I0Raw a) (CB1_5_2I0P a) = true := by
  decide +kernel
lemma CB1_5_2I0P_sound (a : Fin 17) :
    (CB1_5_2I0P a).Encloses (CB1_5_2I0Value a) :=
  contains_sound (CB1_5_2I0Raw_sound a) (CB1_5_2I0P_check a)
lemma CB1_5_2I0Terms_sound (a : Fin 17) :
    (CB1_5_2I0Terms a).Encloses (Foundation.entropyTerm (CB1_5_2I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_5_2I0Certificates_valid
    (CB1_5_2I0CertificateIndex a) (CB1_5_2I0P_sound a)
lemma CB1_5_2I0Entropy_sound : CB1_5_2I0Entropy.Encloses (Foundation.finiteEntropy CB1_5_2I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_5_2I0Value CB1_5_2I0Terms CB1_5_2I0Terms_sound) (by decide +kernel)
lemma CB1_5_2I0Mass_sound : CB1_5_2I0Mass.Encloses (∑ a, CB1_5_2I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_5_2I0P CB1_5_2I0Value CB1_5_2I0P_sound) (by decide +kernel)
lemma CB1_5_2I0MassTermLog_sound : CB1_5_2I0MassTermLog.Encloses (Real.log ((∑ a, CB1_5_2I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_5_2I0Mass_sound) (w := CB1_5_2I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_5_2I0MassTerm_sound : CB1_5_2I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_5_2I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_5_2I0Mass_sound) CB1_5_2I0MassTermLog_sound) (by decide +kernel)
lemma CB1_5_2I0H_sound : CB1_5_2I0H.Encloses (homogeneousEntropy CB1_5_2I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_5_2I0Value CB1_5_2I0MassTerm_sound CB1_5_2I0Entropy_sound) (by decide +kernel)
lemma CB1_5_2I0_sound : CB1_5_2I0H.Encloses (stageBCapacity (shape 1 5 2) 0) := by
  exact CB1_5_2I0H_sound

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
lemma positiveSecond_list : positiveSecond = [
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 6 1 1)] := by decide +kernel

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I0
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
lemma CB1_6_1I0Raw_sound (a : Fin 17) :
    (CB1_6_1I0Raw a).Encloses (CB1_6_1I0Value a) := by
  exact marginalBall_sound (below (shape 1 6 1)) B1_6_1Law (fun u => (stageBLaw (shape 1 6 1) u : ℝ)) (fun u _ => B1_6_1Law_sound u) ((stageBPriority (shape 1 6 1)) 0) a
lemma CB1_6_1I0Certificates_valid :
    CB1_6_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_6_1I0P_check : ∀ a : Fin 17, contains (CB1_6_1I0Raw a) (CB1_6_1I0P a) = true := by
  decide +kernel
lemma CB1_6_1I0P_sound (a : Fin 17) :
    (CB1_6_1I0P a).Encloses (CB1_6_1I0Value a) :=
  contains_sound (CB1_6_1I0Raw_sound a) (CB1_6_1I0P_check a)
lemma CB1_6_1I0Terms_sound (a : Fin 17) :
    (CB1_6_1I0Terms a).Encloses (Foundation.entropyTerm (CB1_6_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_6_1I0Certificates_valid
    (CB1_6_1I0CertificateIndex a) (CB1_6_1I0P_sound a)
lemma CB1_6_1I0Entropy_sound : CB1_6_1I0Entropy.Encloses (Foundation.finiteEntropy CB1_6_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_6_1I0Value CB1_6_1I0Terms CB1_6_1I0Terms_sound) (by decide +kernel)
lemma CB1_6_1I0Mass_sound : CB1_6_1I0Mass.Encloses (∑ a, CB1_6_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_6_1I0P CB1_6_1I0Value CB1_6_1I0P_sound) (by decide +kernel)
lemma CB1_6_1I0MassTermLog_sound : CB1_6_1I0MassTermLog.Encloses (Real.log ((∑ a, CB1_6_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_6_1I0Mass_sound) (w := CB1_6_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB1_6_1I0MassTerm_sound : CB1_6_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_6_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_6_1I0Mass_sound) CB1_6_1I0MassTermLog_sound) (by decide +kernel)
lemma CB1_6_1I0H_sound : CB1_6_1I0H.Encloses (homogeneousEntropy CB1_6_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_6_1I0Value CB1_6_1I0MassTerm_sound CB1_6_1I0Entropy_sound) (by decide +kernel)
lemma CB1_6_1I0_sound : CB1_6_1I0H.Encloses (stageBCapacity (shape 1 6 1) 0) := by
  exact CB1_6_1I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I0
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
lemma CB2_1_5I0Raw_sound (a : Fin 17) :
    (CB2_1_5I0Raw a).Encloses (CB2_1_5I0Value a) := by
  exact marginalBall_sound (below (shape 2 1 5)) B2_1_5Law (fun u => (stageBLaw (shape 2 1 5) u : ℝ)) (fun u _ => B2_1_5Law_sound u) ((stageBPriority (shape 2 1 5)) 0) a
lemma CB2_1_5I0Certificates_valid :
    CB2_1_5I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_1_5I0P_check : ∀ a : Fin 17, contains (CB2_1_5I0Raw a) (CB2_1_5I0P a) = true := by
  decide +kernel
lemma CB2_1_5I0P_sound (a : Fin 17) :
    (CB2_1_5I0P a).Encloses (CB2_1_5I0Value a) :=
  contains_sound (CB2_1_5I0Raw_sound a) (CB2_1_5I0P_check a)
lemma CB2_1_5I0Terms_sound (a : Fin 17) :
    (CB2_1_5I0Terms a).Encloses (Foundation.entropyTerm (CB2_1_5I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_1_5I0Certificates_valid
    (CB2_1_5I0CertificateIndex a) (CB2_1_5I0P_sound a)
lemma CB2_1_5I0Entropy_sound : CB2_1_5I0Entropy.Encloses (Foundation.finiteEntropy CB2_1_5I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_1_5I0Value CB2_1_5I0Terms CB2_1_5I0Terms_sound) (by decide +kernel)
lemma CB2_1_5I0Mass_sound : CB2_1_5I0Mass.Encloses (∑ a, CB2_1_5I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_1_5I0P CB2_1_5I0Value CB2_1_5I0P_sound) (by decide +kernel)
lemma CB2_1_5I0MassTermLog_sound : CB2_1_5I0MassTermLog.Encloses (Real.log ((∑ a, CB2_1_5I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_1_5I0Mass_sound) (w := CB2_1_5I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB2_1_5I0MassTerm_sound : CB2_1_5I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_1_5I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_1_5I0Mass_sound) CB2_1_5I0MassTermLog_sound) (by decide +kernel)
lemma CB2_1_5I0H_sound : CB2_1_5I0H.Encloses (homogeneousEntropy CB2_1_5I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_1_5I0Value CB2_1_5I0MassTerm_sound CB2_1_5I0Entropy_sound) (by decide +kernel)
lemma CB2_1_5I0_sound : CB2_1_5I0H.Encloses (stageBCapacity (shape 2 1 5) 0) := by
  exact CB2_1_5I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I0
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
lemma CB2_3_3I0Raw_sound (a : Fin 17) :
    (CB2_3_3I0Raw a).Encloses (CB2_3_3I0Value a) := by
  exact marginalBall_sound (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (fun u _ => B2_3_3Law_sound u) ((stageBPriority (shape 2 3 3)) 0) a
lemma CB2_3_3I0Certificates_valid :
    CB2_3_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_3_3I0P_check : ∀ a : Fin 17, contains (CB2_3_3I0Raw a) (CB2_3_3I0P a) = true := by
  decide +kernel
lemma CB2_3_3I0P_sound (a : Fin 17) :
    (CB2_3_3I0P a).Encloses (CB2_3_3I0Value a) :=
  contains_sound (CB2_3_3I0Raw_sound a) (CB2_3_3I0P_check a)
lemma CB2_3_3I0Terms_sound (a : Fin 17) :
    (CB2_3_3I0Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I0Certificates_valid
    (CB2_3_3I0CertificateIndex a) (CB2_3_3I0P_sound a)
lemma CB2_3_3I0Entropy_sound : CB2_3_3I0Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_3_3I0Value CB2_3_3I0Terms CB2_3_3I0Terms_sound) (by decide +kernel)
lemma CB2_3_3I0Mass_sound : CB2_3_3I0Mass.Encloses (∑ a, CB2_3_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_3_3I0P CB2_3_3I0Value CB2_3_3I0P_sound) (by decide +kernel)
lemma CB2_3_3I0MassTermLog_sound : CB2_3_3I0MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I0Mass_sound) (w := CB2_3_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB2_3_3I0MassTerm_sound : CB2_3_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I0Mass_sound) CB2_3_3I0MassTermLog_sound) (by decide +kernel)
lemma CB2_3_3I0H_sound : CB2_3_3I0H.Encloses (homogeneousEntropy CB2_3_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I0Value CB2_3_3I0MassTerm_sound CB2_3_3I0Entropy_sound) (by decide +kernel)
lemma CB2_3_3I0_sound : CB2_3_3I0H.Encloses (stageBCapacity (shape 2 3 3) 0) := by
  exact CB2_3_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I0
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
lemma CB2_5_1I0Raw_sound (a : Fin 17) :
    (CB2_5_1I0Raw a).Encloses (CB2_5_1I0Value a) := by
  exact marginalBall_sound (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (fun u _ => B2_5_1Law_sound u) ((stageBPriority (shape 2 5 1)) 0) a
lemma CB2_5_1I0Certificates_valid :
    CB2_5_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB2_5_1I0P_check : ∀ a : Fin 17, contains (CB2_5_1I0Raw a) (CB2_5_1I0P a) = true := by
  decide +kernel
lemma CB2_5_1I0P_sound (a : Fin 17) :
    (CB2_5_1I0P a).Encloses (CB2_5_1I0Value a) :=
  contains_sound (CB2_5_1I0Raw_sound a) (CB2_5_1I0P_check a)
lemma CB2_5_1I0Terms_sound (a : Fin 17) :
    (CB2_5_1I0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I0Certificates_valid
    (CB2_5_1I0CertificateIndex a) (CB2_5_1I0P_sound a)
lemma CB2_5_1I0Entropy_sound : CB2_5_1I0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_5_1I0Value CB2_5_1I0Terms CB2_5_1I0Terms_sound) (by decide +kernel)
lemma CB2_5_1I0Mass_sound : CB2_5_1I0Mass.Encloses (∑ a, CB2_5_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_5_1I0P CB2_5_1I0Value CB2_5_1I0P_sound) (by decide +kernel)
lemma CB2_5_1I0MassTermLog_sound : CB2_5_1I0MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_5_1I0Mass_sound) (w := CB2_5_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CB2_5_1I0MassTerm_sound : CB2_5_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I0Mass_sound) CB2_5_1I0MassTermLog_sound) (by decide +kernel)
lemma CB2_5_1I0H_sound : CB2_5_1I0H.Encloses (homogeneousEntropy CB2_5_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I0Value CB2_5_1I0MassTerm_sound CB2_5_1I0Entropy_sound) (by decide +kernel)
lemma CB2_5_1I0_sound : CB2_5_1I0H.Encloses (stageBCapacity (shape 2 5 1) 0) := by
  exact CB2_5_1I0H_sound

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
lemma capacityBBalls_sound_oai (s : Shape) (hs : s ∈ positiveSecond) (i : Fin 3) :
    (capacityBBalls s i).Encloses (stageBCapacity s i) := by
  rw [positiveSecond_list] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · revert i
    exact forall_fin3 CB1_1_6I0_sound CB1_1_6I1_sound CB1_1_6I2_sound
  · revert i
    exact forall_fin3 CB1_2_5I0_sound CB1_2_5I1_sound CB1_2_5I2_sound
  · revert i
    exact forall_fin3 CB1_3_4I0_sound CB1_3_4I1_sound CB1_3_4I2_sound
  · revert i
    exact forall_fin3 CB1_4_3I0_sound CB1_4_3I1_sound CB1_4_3I2_sound
  · revert i
    exact forall_fin3 CB1_5_2I0_sound CB1_5_2I1_sound CB1_5_2I2_sound
  · revert i
    exact forall_fin3 CB1_6_1I0_sound CB1_6_1I1_sound CB1_6_1I2_sound
  · revert i
    exact forall_fin3 CB2_1_5I0_sound CB2_1_5I1_sound CB2_1_5I2_sound
  · revert i
    exact forall_fin3 CB2_2_4I0_sound CB2_2_4I1_sound CB2_2_4I2_sound
  · revert i
    exact forall_fin3 CB2_3_3I0_sound CB2_3_3I1_sound CB2_3_3I2_sound
  · revert i
    exact forall_fin3 CB2_4_2I0_sound CB2_4_2I1_sound CB2_4_2I2_sound
  · revert i
    exact forall_fin3 CB2_5_1I0_sound CB2_5_1I1_sound CB2_5_1I2_sound
  · revert i
    exact forall_fin3 CB3_1_4I0_sound CB3_1_4I1_sound CB3_1_4I2_sound
  · revert i
    exact forall_fin3 CB3_2_3I0_sound CB3_2_3I1_sound CB3_2_3I2_sound
  · revert i
    exact forall_fin3 CB3_3_2I0_sound CB3_3_2I1_sound CB3_3_2I2_sound
  · revert i
    exact forall_fin3 CB3_4_1I0_sound CB3_4_1I1_sound CB3_4_1I2_sound
  · revert i
    exact forall_fin3 CB4_1_3I0_sound CB4_1_3I1_sound CB4_1_3I2_sound
  · revert i
    exact forall_fin3 CB4_2_2I0_sound CB4_2_2I1_sound CB4_2_2I2_sound
  · revert i
    exact forall_fin3 CB4_3_1I0_sound CB4_3_1I1_sound CB4_3_1I2_sound
  · revert i
    exact forall_fin3 CB5_1_2I0_sound CB5_1_2I1_sound CB5_1_2I2_sound
  · revert i
    exact forall_fin3 CB5_2_1I0_sound CB5_2_1I1_sound CB5_2_1I2_sound
  · revert i
    exact forall_fin3 CB6_1_1I0_sound CB6_1_1I1_sound CB6_1_1I2_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityBBalls_sound_oai
