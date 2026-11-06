-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.indexedSlotAssignment_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:47.123202+00:00
-- url     : https://prove2.me/submissions/a224a219-1291-4835-882a-faec5201e6d9

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_empty
attribute [local simp] OAI.SevenEighths.InverseMoment.primeMark_empty



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
omit [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he
end OAI.SevenEighths.InverseMoment
