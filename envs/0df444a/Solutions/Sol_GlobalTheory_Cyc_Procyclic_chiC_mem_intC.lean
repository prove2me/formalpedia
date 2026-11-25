-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.chiC_mem_intC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:43:33.382791+00:00
-- url     : https://prove2.me/submissions/abb51e5e-8b78-445d-83ea-1da78d876e41

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_algebraMap_eq_coe
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
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hχ : IsCyc χ) (F : IntermediateField ℚ_[l] (Om l)) (i : ℤ) (σ : GQ l) :
    chiC χ i σ ∈ intC F := by
  refine ⟨⟨_, F.algebraMap_mem _, (algebraMap_eq_coe _).symm⟩, ?_⟩
  rw [chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l χ hχ).1, one_zpow]
end GlobalTheory.Cyc.Procyclic
