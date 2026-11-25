-- Prove2me | solution 1 for GlobalTheory.CycPerturb.norm_zpow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:11.643598+00:00
-- url     : https://prove2.me/submissions/ff2d27cc-3655-4e8b-b153-2f40a62b9cc3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_zpow_sub_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CycPerturb
theorem _root_.solution (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le ..)
end GlobalTheory.CycPerturb
