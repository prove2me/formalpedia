-- Prove2me | solution 1 for GlobalTheory.CyclotomicTowerSubgroupInclusions.act_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:09.446517+00:00
-- url     : https://prove2.me/submissions/9c7b5eba-a86e-457e-940a-e395e4a230ec

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
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]
end GlobalTheory.CyclotomicTowerSubgroupInclusions
