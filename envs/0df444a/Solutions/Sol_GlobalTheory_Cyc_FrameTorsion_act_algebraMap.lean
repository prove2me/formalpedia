-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.act_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:50.602555+00:00
-- url     : https://prove2.me/submissions/d9778f23-f3fb-49d6-881c-5f62b13f27b6

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_algebraMap_eq

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
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (q : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) q) = algebraMap ℚ_[l] (PadicComplex l) q := by
  rw [algebraMap_eq, ha.1 g, AlgEquiv.commutes]
end GlobalTheory.Cyc.FrameTorsion
