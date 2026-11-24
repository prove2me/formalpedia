-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.exists_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:33.886894+00:00
-- url     : https://prove2.me/submissions/42ebd30b-d5ee-42be-8549-164e8b2cbfb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_map_mem_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
variable {S : Type} [AddCommGroup S] [Module Rg S]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution {A : Type} [AddCommGroup A] [Module Rg A] [IsSemisimpleModule Rg A]
    {a : A} (ha : a ≠ 0) (hI : ∀ x ∈ I, x • a = 0) :
    ∃ U : Submodule Rg A, IsSimpleModule Rg U ∧ ∃ u : U, u ≠ 0 ∧ ∀ x ∈ I, x • u = 0 := by
  have hj : a ∉ Module.jacobson Rg A := by
    rw [IsSemisimpleModule.jacobson_eq_bot]
    simpa using ha
  simp only [Module.jacobson, Submodule.mem_sInf, not_forall] at hj
  obtain ⟨P, hP, haP⟩ := hj
  obtain ⟨U, hU⟩ := exists_isCompl P
  have e := Submodule.quotientEquivOfIsCompl P U hU
  haveI : IsSimpleModule Rg (A ⧸ P) := isSimpleModule_iff_isCoatom.2 hP
  refine ⟨U, IsSimpleModule.congr e.symm, e (P.mkQ a), ?_, ?_⟩
  · simpa using haP
  · exact map_mem_killed I (e.toLinearMap.comp P.mkQ) hI
end GlobalTheory.SemisimpleCount
