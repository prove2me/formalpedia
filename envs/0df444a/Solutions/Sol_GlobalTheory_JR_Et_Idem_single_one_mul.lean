-- Prove2me | solution 1 for GlobalTheory.JR.Et.Idem.single_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:29.047193+00:00
-- url     : https://prove2.me/submissions/2ae39a79-20c6-4ee8-9ae4-4815aee6a60c

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
theorem _root_.solution {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (x : ∀ j, R j) : (Pi.single i 1 : ∀ j, R j) * x = Pi.single i (x i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]
end GlobalTheory.JR.Et.Idem
