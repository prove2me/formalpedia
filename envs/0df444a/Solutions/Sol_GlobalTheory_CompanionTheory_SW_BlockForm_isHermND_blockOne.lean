-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockForm.isHermND_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:09.896918+00:00
-- url     : https://prove2.me/submissions/ed1ec218-83fd-41c8-bf28-6bce41c47149

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_det_blockOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.BlockForm
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {t : F} (ht : t ≠ 0) : IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · rw [blockOne_succ_succ, blockOne_succ_succ]
      exact hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2
end GlobalTheory.CompanionTheory.SW.BlockForm
