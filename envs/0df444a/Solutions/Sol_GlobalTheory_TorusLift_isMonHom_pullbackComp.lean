-- Prove2me | solution 1 for GlobalTheory.TorusLift.isMonHom_pullbackComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:22:11.728465+00:00
-- url     : https://prove2.me/submissions/82ab2435-c43c-4df3-a70d-577d36dfdf47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Theorems.Thm_GlobalTheory_TorusLift_hom_ext_fst
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_exists_pullback_comp_iso_monHom
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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


section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorusLift
section General
variable {S S' S'' : Scheme.{0}}
private theorem pullback_pullback_hom_ext {s : S'' ⟶ S'} {p : S' ⟶ S} {G : Over S} {Z : Over S''}
    {a b : Z ⟶ (Over.pullback s).obj ((Over.pullback p).obj G)}
    (h : a.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p = b.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p) :
    a = b := by
  apply hom_ext_fst
  apply pullback.hom_ext
  · simpa using h
  · have ha := Over.w a
    have hb := Over.w b
    simp only [Over.pullback_obj_hom] at ha hb
    simp only [Category.assoc, Over.pullback_obj_left, Over.pullback_obj_hom] at *
    rw [pullback.condition, reassoc_of% ha, reassoc_of% hb]
private theorem pullbackComp_hom_fst_fst (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) :
    ((Over.pullbackComp s p).hom.app G).left ≫ pullback.fst _ s ≫ pullback.fst G.hom p =
      pullback.fst G.hom (s ≫ p) := by
  have h := congrArg (fun x => x.left) (conjugateEquiv_counit (Over.mapPullbackAdj (s ≫ p))
    ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj p)) (Over.mapComp s p).symm.hom G)
  simpa [Over.pullbackComp] using h
end General
end GlobalTheory.TorusLift
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusLift
variable {S S' S'' : Scheme.{0}}
namespace GlobalTheory.TorusLift
theorem _root_.solution (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.exists_pullback_comp_iso_monHom s p (s ≫ p) rfl G
  have : (Over.pullbackComp s p).hom.app G = e.hom := by
    apply pullback_pullback_hom_ext
    rw [hc, pullbackComp_hom_fst_fst]
  rw [this]
  exact he
end GlobalTheory.TorusLift
