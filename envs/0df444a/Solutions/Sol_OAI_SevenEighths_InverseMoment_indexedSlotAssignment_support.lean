-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.indexedSlotAssignment_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:46.693201+00:00
-- url     : https://prove2.me/submissions/bdb98f3d-e1d1-436a-a88c-e04bd887e52b

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SlotAssignments

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _
end OAI.SevenEighths.InverseMoment
