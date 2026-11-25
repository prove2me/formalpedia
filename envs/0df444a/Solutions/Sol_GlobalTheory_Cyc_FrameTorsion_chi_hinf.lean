-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.chi_hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:39:50.601913+00:00
-- url     : https://prove2.me/submissions/a0cc1611-ceb3-4dd8-9eaf-53b8e2a62a8d

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
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_hinf_le_gj
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_gj_le
import Theorems.Thm_GlobalTheory_CycEigen_gj_le
import Theorems.Thm_GlobalTheory_CycEigen_hinf_le_gj
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic


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
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K) :
    χ h = 1 := by
  have hK0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  exact ((cyc_basic l χ hχ).2.2 K h hK0).2.1 hh
end GlobalTheory.Cyc.FrameTorsion
