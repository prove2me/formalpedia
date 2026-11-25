-- Prove2me | solution 1 for GlobalTheory.TorusDefect.exists_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:27.671538+00:00
-- url     : https://prove2.me/submissions/43b45a7d-b3e5-46cc-acac-4abddba8a943

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_GlobalTheory_TorusDefect_mem_map_iff
import Theorems.Thm_GlobalTheory_TorusDefect_kerEquiv_pullKer
import Theorems.Thm_GlobalTheory_IsCoaction_injective
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_addMonoidAlgebra_coboundary_eq_iff
import Theorems.Thm_GlobalTheory_addMonoidAlgebra_existsUnique_coboundary
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']
variable {G : Over (Spec (CommRingCat.of A))} [GrpObj G] {J : Ideal A}
  {Z : Type} [AddCommGroup Z]
variable [IsCommMonObj G] [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR A ⟶ G)}
open AddMonoidHom
namespace GlobalTheory.TorusDefect
theorem _root_.solution (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥)
    (δ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))))
    (hδ : pullKer G J (inr X (X × X)) δ / pullKer G J ((AddMonoidHom.fst X X).prod (AddMonoidHom.id _)) δ *
      pullKer G J ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))) δ /
      pullKer G J (prodMap (AddMonoidHom.id X) (inl X X)) δ = 1) :
    ∃ κ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))),
      pullKer G J (inr X X) κ / pullKer G J (inl X X + inr X X) κ * pullKer G J (inl X X) κ = δ := by
  set f : Fin n → AddMonoidAlgebra A (X × X) :=
    fun i => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i : AddMonoidAlgebra A (X × X))) with hf
  have hcoc : ∀ i, AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) (f i) +
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) (f i) = 0 := by
    intro i
    have h := congrArg (fun z => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul z) i :
      AddMonoidAlgebra A (X × (X × X))))) hδ
    simp only [ofMul_div, ofMul_mul, ofMul_one, map_sub, map_add, map_zero, Pi.sub_apply,
      Pi.add_apply, Pi.zero_apply, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      ZeroMemClass.coe_zero] at h
    rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ,
      kerEquiv_pullKer hv hJ] at h
    exact h
  have key : ∀ i, ∃ g : AddMonoidAlgebra A X,
      AddMonoidAlgebra.mapDomain (fun y : X => ((0 : X), y)) g -
        AddMonoidAlgebra.mapDomain (fun y : X => (y, y)) g +
        AddMonoidAlgebra.mapDomain (fun y : X => (y, (0 : X))) g = f i :=
    fun i => (addMonoidAlgebra_existsUnique_coboundary (f i) (hcoc i)).exists
  choose g hg using key
  have hmem : ∀ i, g i ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) := by
    intro i
    rw [mem_map_iff]
    intro x
    rw [(addMonoidAlgebra_coboundary_eq_iff (f i) (hcoc i) (g i)).1 (hg i) x]
    exact (mem_map_iff J (f i)).1 (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i).2 (0, x)
  refine ⟨Additive.toMul ((kerEquiv hv (map_algebraMap_sq hJ)).symm fun i => ⟨g i, hmem i⟩), ?_⟩
  apply Additive.ofMul.injective
  apply (kerEquiv hv (map_algebraMap_sq hJ)).injective
  funext i
  apply Subtype.ext
  have e2 : (⇑(AddMonoidHom.inl X X + AddMonoidHom.inr X X) : X → X × X) = fun y => (y, y) :=
    funext fun y => by simp
  simp only [ofMul_div, ofMul_mul, map_sub, map_add, Pi.sub_apply, Pi.add_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ]
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply, e2]
  exact hg i
end GlobalTheory.TorusDefect
