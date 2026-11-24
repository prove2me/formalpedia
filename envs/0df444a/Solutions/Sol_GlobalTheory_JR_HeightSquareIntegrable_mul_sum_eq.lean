-- Prove2me | solution 1 for GlobalTheory.JR.HeightSquareIntegrable.mul_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:21.470599+00:00
-- url     : https://prove2.me/submissions/de5e7ced-6439-4059-9d99-76cb0dbadd69

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
theorem _root_.solution (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (a : Fin m → K) (j : Fin m) : f j * ∑ i, f i * a i = f j * a j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [← mul_assoc, hid]
  · intro i _ hij; rw [← mul_assoc, hor j i (Ne.symm hij), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h
end GlobalTheory.JR.HeightSquareIntegrable
