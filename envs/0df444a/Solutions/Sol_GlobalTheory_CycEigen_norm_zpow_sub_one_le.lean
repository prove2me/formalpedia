-- Prove2me | solution 1 for GlobalTheory.CycEigen.norm_zpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:44:20.083847+00:00
-- url     : https://prove2.me/submissions/e308e690-ca46-4e50-87cf-f91744c03120

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Theorems.Thm_GlobalTheory_UnitNormPowerSubOne_norm_zpow_sub_one_le


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
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycEigen
theorem _root_.solution (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le ..)
end GlobalTheory.CycEigen
