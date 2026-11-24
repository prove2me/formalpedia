-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockForm.isHermND_hypJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:25.803927+00:00
-- url     : https://prove2.me/submissions/d33681c4-d58b-4596-9eb5-10cb8641b3b3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_one_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_one_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_one_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_succ_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_succ_succ_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_succ_succ_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_det_hypJ

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
    (hJ : IsHermND σ J) : IsHermND σ (hypJ J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [hypJ_zero_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_one]
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
          · rw [hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]
            exact hJ.1 i j
  · rw [det_hypJ]
    exact neg_ne_zero.mpr hJ.2
end GlobalTheory.CompanionTheory.SW.BlockForm
