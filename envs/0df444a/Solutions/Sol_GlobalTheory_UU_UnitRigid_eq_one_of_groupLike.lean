-- Prove2me | solution 1 for GlobalTheory.UU.UnitRigid.eq_one_of_groupLike
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:04.466925+00:00
-- url     : https://prove2.me/submissions/b0e72a86-44cd-4b5b-87f1-3d81809ba897

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfGroupLike
import Theorems.Thm_GlobalTheory_UU_UnitRigid_coeff_inl_mul_inr
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitRigid
namespace GlobalTheory.UU.UnitRigid
theorem _root_.solution {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))
end GlobalTheory.UU.UnitRigid
