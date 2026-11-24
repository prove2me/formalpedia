-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockAlg.det_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:55.162839+00:00
-- url     : https://prove2.me/submissions/c3ea1db0-b65c-4023-b9fc-1d7a8c481ab7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
namespace GlobalTheory.CompanionTheory.SW.BlockAlg
theorem _root_.solution {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : (blockOne t A).submatrix Fin.succ (Fin.succAbove (0 : Fin (M + 1))) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [h0, Finset.sum_eq_zero]
  · simp [blockOne_zero_zero]
  · intro j _
    simp [blockOne_zero_succ]
end GlobalTheory.CompanionTheory.SW.BlockAlg
