-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.act_mem_Ohat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:28.531895+00:00
-- url     : https://prove2.me/submissions/3cd042da-1625-4cb8-8c01-315e2ac14b19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_continuous_act
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_conj_mem_Hinf

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
theorem _root_.solution (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {m : ℕ} {σ : GQ l}
    (hσ : σ ∈ Gj K m) {y : PadicComplex l} (hy : y ∈ Ohat K) : act σ y ∈ Ohat K := by
  refine map_mem_closure (continuous_act hact σ) hy ?_
  rintro _ ⟨⟨x, hx, rfl⟩, hx1⟩
  refine ⟨⟨σ x, ?_, (hact.1 σ x).symm⟩, by rwa [hact.2]⟩
  change σ x ∈ Kinf K
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have h1 : (σ⁻¹ * h * σ⁻¹⁻¹) x = x := conj_mem_Hinf hχ K (inv_mem hσ) hh ⟨x, hx⟩
  conv_rhs => rw [← h1]
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
  congr 1
  group
end GlobalTheory.Cyc.Procyclic
