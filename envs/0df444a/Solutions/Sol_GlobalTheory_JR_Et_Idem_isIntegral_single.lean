-- Prove2me | solution 1 for GlobalTheory.JR.Et.Idem.isIntegral_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:31.346281+00:00
-- url     : https://prove2.me/submissions/1b1ca14c-c2dd-4abe-a067-5f2274bfc897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
import Theorems.Thm_GlobalTheory_JR_Et_Idem_isIntegral_of_forall

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
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Finite ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (i : ι) (z : R i) (hz : IsIntegral O z) :
    IsIntegral O (Pi.single i z : ∀ j, R j) := by
  refine isIntegral_of_forall _ fun j => ?_
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
end GlobalTheory.JR.Et.Idem
