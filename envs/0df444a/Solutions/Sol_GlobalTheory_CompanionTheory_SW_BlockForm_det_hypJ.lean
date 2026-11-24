-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockForm.det_hypJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:12:11.53648+00:00
-- url     : https://prove2.me/submissions/d34b909d-0757-4598-b767-777897b26087

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_det_blockOne
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_hypJ_zero_succ_succ

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
namespace GlobalTheory.CompanionTheory.SW.BlockForm
theorem _root_.solution {K : Type} [CommRing K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    (hypJ A).det = -A.det := by
  have h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A := by
    rw [← Fin.succ_zero_eq_one]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]
end GlobalTheory.CompanionTheory.SW.BlockForm
