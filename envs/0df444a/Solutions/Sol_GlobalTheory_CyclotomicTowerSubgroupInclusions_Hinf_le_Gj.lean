-- Prove2me | solution 1 for GlobalTheory.CyclotomicTowerSubgroupInclusions.Hinf_le_Gj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:09:21.517951+00:00
-- url     : https://prove2.me/submissions/b8cfe179-8198-441d-88d1-59fc26ff9749

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_le_Kinf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CyclotomicTowerSubgroupInclusions
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CyclotomicTowerSubgroupInclusions
theorem _root_.solution (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩
end GlobalTheory.CyclotomicTowerSubgroupInclusions
