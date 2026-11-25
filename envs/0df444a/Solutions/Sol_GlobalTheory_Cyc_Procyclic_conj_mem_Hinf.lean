-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.conj_mem_Hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:14:20.51944+00:00
-- url     : https://prove2.me/submissions/6124c65b-48e9-4537-aa6d-a5e0550349bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
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
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution (hχ : IsCyc χ) (K : FinExt l) {m : ℕ} {σ : GQ l} (hσ : σ ∈ Gj K m)
    {h : GQ l} (hh : h ∈ Hinf K) : σ * h * σ⁻¹ ∈ Hinf K := by
  obtain ⟨-, -, hG⟩ := cyc_basic l χ hχ
  have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m hσ
  have hh0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (AlmostTrace.Hinf_le_Gj K m hh)
  refine (hG K _ (mul_mem (mul_mem hσ0 hh0) (inv_mem hσ0))).2.2 ?_
  rw [map_mul, map_mul, (hG K h hh0).2.1 hh, map_inv, mul_one, mul_inv_cancel]
end GlobalTheory.Cyc.Procyclic
