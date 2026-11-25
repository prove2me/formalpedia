-- Prove2me | solution 1 for GlobalTheory.CyclotomicTowerSubgroupInclusions.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:51.087192+00:00
-- url     : https://prove2.me/submissions/7a45a39a-3796-4ae0-8efb-128a78196923

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
theorem _root_.solution (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩
end GlobalTheory.CyclotomicTowerSubgroupInclusions
