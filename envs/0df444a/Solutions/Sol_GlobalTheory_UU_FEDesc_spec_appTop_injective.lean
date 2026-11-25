-- Prove2me | solution 1 for GlobalTheory.UU.FEDesc.spec_appTop_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:56.766456+00:00
-- url     : https://prove2.me/submissions/e686056e-b53b-487b-997c-fb9e92843b2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFOfExpT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FiniteExponentBaseChangeField
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.FEDesc
namespace GlobalTheory.UU.FEDesc
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  have e : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1.comp hf).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
end GlobalTheory.UU.FEDesc
