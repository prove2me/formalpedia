-- Prove2me | solution 1 for GlobalTheory.T.witt_free_tuples_split_quadratic_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:27.035839+00:00
-- url     : https://prove2.me/submissions/e2f92ff7-fb87-4f56-ba27-e2376735b3ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtaleStatement
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_witt_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.WittSplit.witt_split | exact GlobalTheory.SgAlg.WittSplit.witt_split | (intros; apply GlobalTheory.SgAlg.WittSplit.witt_split <;> assumption)
end _root_.GlobalTheory.T
