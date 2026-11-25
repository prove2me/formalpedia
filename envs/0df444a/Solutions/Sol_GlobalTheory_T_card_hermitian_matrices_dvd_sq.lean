-- Prove2me | solution 1 for GlobalTheory.T.card_hermitian_matrices_dvd_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:57.37511+00:00
-- url     : https://prove2.me/submissions/67af32f6-64fe-42f4-b1be-bb06cec0ff86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Theorems.Thm_GlobalTheory_GramCount_card_hermitian_dvd_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → ∀ (m : ℕ), Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2 = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  first | exact @GlobalTheory.GramCount.card_hermitian_dvd_sq | exact GlobalTheory.GramCount.card_hermitian_dvd_sq | (intros; apply GlobalTheory.GramCount.card_hermitian_dvd_sq <;> assumption)
end _root_.GlobalTheory.T
