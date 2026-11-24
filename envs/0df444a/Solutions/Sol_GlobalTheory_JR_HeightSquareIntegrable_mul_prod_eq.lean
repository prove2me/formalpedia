-- Prove2me | solution 1 for GlobalTheory.JR.HeightSquareIntegrable.mul_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:58.64507+00:00
-- url     : https://prove2.me/submissions/af673b3d-f53f-4059-a20b-b9925410a59a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop
import Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_mul_eq_iff_mk

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
    (g : Fin m → K) (k : Fin m → ℕ) (j : Fin m) :
    f j * ∏ i, (f i * g i + (1 - f i)) ^ k i = f j * g j ^ k j := by
  rw [mul_eq_iff_mk hid]; simp only [map_prod, map_pow]
  rw [Finset.prod_eq_single j]
  · congr 1
    rw [← mul_eq_iff_mk hid]; linear_combination (g j - 1) * hid j
  · intro i _ hij
    have h1 : Ideal.Quotient.mk (Ideal.span {1 - f j}) (f i * g i + (1 - f i)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - f j})), ← mul_eq_iff_mk hid]
      linear_combination (g i - 1) * hor j i (Ne.symm hij)
    rw [h1, one_pow]
  · intro h; exact absurd (Finset.mem_univ j) h
end GlobalTheory.JR.HeightSquareIntegrable
