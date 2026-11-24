-- Prove2me | solution 1 for GlobalTheory.T.exists_frobenius_compatible_wittVector_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:43.687876+00:00
-- url     : https://prove2.me/submissions/f72c439e-b895-4a83-b124-d91f4426f948

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFrobeniusCompatibleLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFrobeniusCompatibleLiftStatement
import Theorems.Thm_GlobalTheory_DworkLift_exists_frobenius_compatible_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
end _root_.GlobalTheory.T
