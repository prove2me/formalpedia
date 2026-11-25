-- Prove2me | solution 1 for GlobalTheory.CycEigen.chiC_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:06.799612+00:00
-- url     : https://prove2.me/submissions/dfdf8609-2ee1-4bb6-b39a-f50985fd5fb8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g : GQ l) :
    chiC χ (-j) g * chiC χ j g = 1 := by
  rw [chiC, chiC, ← map_mul, ← Units.val_mul, ← zpow_add]
  simp
end GlobalTheory.CycEigen
