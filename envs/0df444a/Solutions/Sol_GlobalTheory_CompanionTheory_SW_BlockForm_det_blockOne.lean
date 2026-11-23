-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockForm.det_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:10.499948+00:00
-- url     : https://prove2.me/submissions/8fbb21ec-f4ad-446b-bb0f-601bde589465

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockOne_succ_succ

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
theorem _root_.solution {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    exact blockOne_succ_succ t A i j
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blockOne_zero_zero, blockOne_zero_succ, h0]
end GlobalTheory.CompanionTheory.SW.BlockForm
