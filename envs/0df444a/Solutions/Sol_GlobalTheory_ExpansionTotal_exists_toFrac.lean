-- Prove2me | solution 1 for GlobalTheory.ExpansionTotal.exists_toFrac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:02.752218+00:00
-- url     : https://prove2.me/submissions/2513479e-72f7-48ed-8632-7beea98b911c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
variable (F)
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution : ∃ θ : TF (R := R) F ⟶ TF (R := R) (FractionRing R),
    θ.left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ jFK (R := R) (FractionRing R) =
    jFK (R := R) F := (Spec.map_comp _ _).symm
  exact ⟨Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) h)), h⟩
end GlobalTheory.ExpansionTotal
