-- Prove2me | solution 1 for GlobalTheory.JR.HeightSquareIntegrable.mul_eq_iff_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:45.308621+00:00
-- url     : https://prove2.me/submissions/30c1e894-2ea7-495a-a685-3246ee3fbac6

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
theorem _root_.solution (hid : ∀ i, f i * f i = f i) (j : Fin m) (x y : K) :
    f j * x = f j * y ↔
      Ideal.Quotient.mk (Ideal.span {1 - f j}) x = Ideal.Quotient.mk (Ideal.span {1 - f j}) y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · intro h; exact ⟨x - y, by linear_combination (-1 : K) * h⟩
  · rintro ⟨a, ha⟩; linear_combination (-f j) * ha - a * hid j
end GlobalTheory.JR.HeightSquareIntegrable
