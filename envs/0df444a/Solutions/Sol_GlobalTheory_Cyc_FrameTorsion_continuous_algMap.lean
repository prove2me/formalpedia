-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.continuous_algMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:32:24.547957+00:00
-- url     : https://prove2.me/submissions/a1fdee27-1399-4e1c-bc89-341f478230f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleTwistCoboundaryOnBall
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_norm_algebraMap
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FrameTorsion
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := by
  have hiso : Isometry (algebraMap ℚ_[l] (PadicComplex l)) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (PadicComplex l)) norm_algebraMap
  exact hiso.continuous
end GlobalTheory.Cyc.FrameTorsion
