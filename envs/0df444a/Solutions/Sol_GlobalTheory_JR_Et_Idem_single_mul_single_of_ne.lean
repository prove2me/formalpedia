-- Prove2me | solution 1 for GlobalTheory.JR.Et.Idem.single_mul_single_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:28.086572+00:00
-- url     : https://prove2.me/submissions/4aeca34f-ae98-4fde-a381-c02b8c805c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.Idem
namespace GlobalTheory.JR.Et.Idem
theorem _root_.solution {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroClass (R i)] {i j : ι}
    (h : i ≠ j) (a : R i) (b : R j) : (Pi.single i a : ∀ k, R k) * Pi.single j b = 0 := by
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hk, zero_mul]
end GlobalTheory.JR.Et.Idem
