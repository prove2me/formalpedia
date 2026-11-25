-- Prove2me | solution 1 for GlobalTheory.UU.UnitCob.map_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:44:14.477437+00:00
-- url     : https://prove2.me/submissions/58a1d4fc-36db-4c9c-bce6-7d2bbf43e683

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitCob
variable {B C : Type} [CommRing B] [CommRing C] {M N : Type} [AddCommGroup M] [AddCommGroup N]
namespace GlobalTheory.UU.UnitCob
theorem _root_.solution (s : M → N) (F : AddMonoidAlgebra B N →+* C) (G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single (s m) b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F (AddMonoidAlgebra.mapDomain s a) = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [AddMonoidAlgebra.mapDomain_add, map_add, map_add, ha, hb]
  | single m b => rw [AddMonoidAlgebra.mapDomain_single, h]
end GlobalTheory.UU.UnitCob
