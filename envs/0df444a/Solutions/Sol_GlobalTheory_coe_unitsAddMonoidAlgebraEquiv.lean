-- Prove2me | solution 1 for GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:41.132877+00:00
-- url     : https://prove2.me/submissions/8b4a1b00-c348-45c4-bf77-8f9391e90fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]
variable [IsDomain A]
variable [Module.Free ℤ X]
namespace GlobalTheory
theorem _root_.solution (p : Aˣ × Multiplicative X) :
    (unitsAddMonoidAlgebraEquiv A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl
end GlobalTheory
