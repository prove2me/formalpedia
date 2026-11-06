-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeMark_indexed_assignments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:47.261186+00:00
-- url     : https://prove2.me/submissions/93658c88-a4b1-4092-8c6f-d38593dca57e

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_supported_assignments
import Theorems.Thm_OAI_SevenEighths_InverseMoment_indexedSlotAssignment_injective
import Theorems.Thm_OAI_SevenEighths_InverseMoment_primeMark_empty
attribute [local simp] OAI.SevenEighths.InverseMoment.primeMark_empty



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A =
      ∑ r ∈ (I.pi (fun i => L i ∩ A)).image (indexedSlotAssignment I),
        slotAssignmentWeight I a (fun i hi => r (I.equivFin ⟨i,hi⟩)) := by
  rw [Finset.sum_image (fun q _ r _ h => indexedSlotAssignment_injective I h)]
  simpa only [indexedSlotAssignment,Equiv.symm_apply_apply] using
    primeMark_supported_assignments I L a A
end OAI.SevenEighths.InverseMoment
