-- Prove2me | solution 1 for GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:45:54.77483+00:00
-- url     : https://prove2.me/submissions/c889688e-330f-4b90-81d2-8380a04fc93a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_zpow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l], ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 → ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  first | exact @GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | exact GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | (intros; apply GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one <;> assumption)
end _root_.GlobalTheory.T
