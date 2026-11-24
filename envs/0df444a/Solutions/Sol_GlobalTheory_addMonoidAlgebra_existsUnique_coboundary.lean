-- Prove2me | solution 1 for GlobalTheory.addMonoidAlgebra_existsUnique_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:00.722886+00:00
-- url     : https://prove2.me/submissions/015eadd0-e758-4384-b284-f4ab0d9161c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_addMonoidAlgebra_coboundary_eq_iff
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply


attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv

set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {X : Type*} [Zero X] {A : Type*} [Ring A]
namespace GlobalTheory
theorem _root_.solution (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩
end GlobalTheory
