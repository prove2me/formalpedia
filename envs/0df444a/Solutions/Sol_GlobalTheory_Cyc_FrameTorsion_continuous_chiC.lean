-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.continuous_chiC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:05.282388+00:00
-- url     : https://prove2.me/submissions/f9c46dec-e888-4cd2-b142-762125ad9976

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_continuous_algMap
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
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) : Continuous (chiC χ j) := by
  have h0 : Continuous (fun g : GQ l => ((χ g : ℚ_[l])) ^ j) :=
    (IsCyc.continuous hχ).zpow₀ j (fun g => Or.inl (χ g).ne_zero)
  have h1 : chiC χ j = fun g => algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ j) := by
    funext g
    rw [chiC, Units.val_zpow_eq_zpow_val]
  rw [h1]
  exact continuous_algMap.comp h0
end GlobalTheory.Cyc.FrameTorsion
