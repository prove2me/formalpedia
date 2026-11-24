-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LinPair.exists_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:02.586955+00:00
-- url     : https://prove2.me/submissions/15ffe538-7660-4fd1-b4b7-f42b61e80912

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ClearDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSnd
import Theorems.Thm_GlobalTheory_ClearDenominatorsIntegral_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LinPair
namespace GlobalTheory.UnitLemma.LinPair
theorem _root_.solution (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)
end GlobalTheory.UnitLemma.LinPair
