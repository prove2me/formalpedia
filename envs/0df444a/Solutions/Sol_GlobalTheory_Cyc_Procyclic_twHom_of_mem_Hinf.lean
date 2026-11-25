-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.twHom_of_mem_Hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:50.741309+00:00
-- url     : https://prove2.me/submissions/a0f7f5c1-7f56-4d77-a8ff-7ddeeb89c33a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_apply
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic
import Theorems.Thm_GlobalTheory_Cyc_cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base


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
variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) (y : Fin r → PadicComplex l) (a : Fin r) :
    twHom act χ i U h y a = act h (y a) := by
  have hh0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (AlmostTrace.Hinf_le_Gj K m hh)
  rw [twHom_apply, chiC, ((cyc_basic l χ hχ).2.2 K h hh0).2.1 hh, hF.2.2.2.2.1 h hh]
  simp [Matrix.one_apply]
end GlobalTheory.Cyc.Procyclic
