-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AlgSplit.det_blockOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.505127+00:00
-- url     : https://prove2.me/submissions/0df37ec4-94fa-4f4d-92e2-f1cd8a7d2da6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AlgSplit
namespace GlobalTheory.CompanionTheory.SW.AlgSplit
theorem _root_.solution {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin M, blockOne t A 0 j.succ = 0 := by intro j; simp [blockOne]
  have h00 : blockOne t A 0 0 = t := by simp [blockOne]
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [blockOne]
  simp [hz, h00, h0]
end GlobalTheory.CompanionTheory.SW.AlgSplit
