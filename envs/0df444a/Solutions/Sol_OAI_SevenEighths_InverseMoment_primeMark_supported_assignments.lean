-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeMark_supported_assignments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:45.466231+00:00
-- url     : https://prove2.me/submissions/a07af93d-8594-4ba8-9c76-2232b55c1e90

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
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a
end OAI.SevenEighths.InverseMoment
