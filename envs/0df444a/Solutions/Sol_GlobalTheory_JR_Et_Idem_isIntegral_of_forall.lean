-- Prove2me | solution 1 for GlobalTheory.JR.Et.Idem.isIntegral_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:21.312805+00:00
-- url     : https://prove2.me/submissions/6db8f5cd-fe45-4f2f-a9ec-b20e216cdf6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
import Theorems.Thm_GlobalTheory_IntegralPi_main


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
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)
end GlobalTheory.JR.Et.Idem
