-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_pow_sub_lin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:00:21.599049+00:00
-- url     : https://prove2.me/submissions/a2cdcb71-a3c4-429a-a389-b027173a1b6f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Theorems.Thm_GlobalTheory_UltrametricPowerBound_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖w ^ k - 1 - k * (w - 1)‖ ≤ ‖w - 1‖ ^ 2 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerBound.main
  | exact _root_.GlobalTheory.UltrametricPowerBound.main
  | (apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerBound.main ..)
end GlobalTheory.Cyc
