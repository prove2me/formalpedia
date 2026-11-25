-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.ohat_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:21:26.867749+00:00
-- url     : https://prove2.me/submissions/b8b5b3c7-901d-4ae5-999c-cd1ba2eb1846

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
theorem _root_.solution (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have hcl : IsClosed {y : PadicComplex l | ‖y‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  exact closure_minimal (fun z hz => hz.2) hcl hy
end GlobalTheory.Cyc.FrameTorsion
