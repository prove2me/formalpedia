-- Prove2me | solution 1 for GlobalTheory.appTop_field_point_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:47.890307+00:00
-- url     : https://prove2.me/submissions/e1067756-e0d9-4fcc-b1fe-a1a80738f4d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PullbackSectionFamilyNeZeroIff
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have := Over.w (toUnit (TF (R := R) F))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.comp_id _).symm.trans this
  rw [e]
  have hi : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have hc := hi.comp hb
  intro a b hab
  apply hc
  have na := congrArg (fun q => q.hom a) n
  have nb := congrArg (fun q => q.hom b) n
  exact na.symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hab).trans nb)
end GlobalTheory
