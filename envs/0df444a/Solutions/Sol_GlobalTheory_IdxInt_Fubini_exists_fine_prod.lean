-- Prove2me | solution 1 for GlobalTheory.IdxInt.Fubini.exists_fine_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:45:57.399445+00:00
-- url     : https://prove2.me/submissions/40beb1bf-13c5-4a2b-8794-cde23a40238b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
import Theorems.Thm_GlobalTheory_IdxInt_Fubini_relIndex_prod
import Theorems.Thm_GlobalTheory_IdxInt_Model_fine_refine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Fubini
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
namespace GlobalTheory.IdxInt.Fubini
theorem _root_.solution {A : AddSubgroup W} {A' : AddSubgroup W'} {φ : W × W' → ℂ}
    (h : Nice (A.prod A') φ) :
    ∃ (B : AddSubgroup W) (B' : AddSubgroup W'), B ≤ A ∧ B' ≤ A' ∧ B.relIndex A ≠ 0 ∧
      B'.relIndex A' ≠ 0 ∧ Fine (A.prod A') φ (B.prod B') := by
  obtain ⟨C, hC⟩ := h
  have i1 : (C.comap (AddMonoidHom.inl W W')).relIndex A ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, A'.zero_mem⟩
  have i2 : (C.comap (AddMonoidHom.inr W W')).relIndex A' ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨A.zero_mem, ha⟩
  refine ⟨C.comap (AddMonoidHom.inl W W'), C.comap (AddMonoidHom.inr W W'),
    fun a ha => (hC.1 ha).1, fun a ha => (hC.1 ha).2, i1, i2, Model.fine_refine hC ?_ ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := C.add_mem ha hb
    simpa using this
  · rw [relIndex_prod]
    exact mul_ne_zero i1 i2
end GlobalTheory.IdxInt.Fubini
