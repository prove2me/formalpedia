-- Prove2me | solution 1 for GlobalTheory.JR.HeightSquareIntegrable.eq_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:44.531104+00:00
-- url     : https://prove2.me/submissions/ec22d2e0-bebf-4b48-b98d-c3192dd03628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HeightSquareIntegrable
variable {K : Type} [CommRing K] {m : ℕ} {f : Fin m → K}
namespace GlobalTheory.JR.HeightSquareIntegrable
theorem _root_.solution (hsum : ∑ i, f i = 1) {x y : K} (h : ∀ j, f j * x = f j * y) : x = y := by
  have hx : x = ∑ j, f j * x := by rw [← Finset.sum_mul, hsum, one_mul]
  have hy : y = ∑ j, f j * y := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [hx, hy]; exact Finset.sum_congr rfl fun j _ => h j
end GlobalTheory.JR.HeightSquareIntegrable
