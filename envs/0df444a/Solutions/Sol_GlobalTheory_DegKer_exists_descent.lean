-- Prove2me | solution 1 for GlobalTheory.DegKer.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:56.873804+00:00
-- url     : https://prove2.me/submissions/6d964d75-211e-45ec-94c6-87ccfaaa236c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] (Ω : Type) [Field Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ X) (hy : IsClosed {y (IsLocalRing.closedPoint Ω)}) :
    (y ≫ q) ≫ pointOfClosedPoint q _ hy = y := by
  have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X y
  have h2 : (X.fromSpecResidueField _ ≫ q) ≫ pointOfClosedPoint q _ hy =
      X.fromSpecResidueField (y (IsLocalRing.closedPoint Ω)) := by
    rw [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv q _ hy, ← Spec.map_comp_assoc,
      Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  conv_lhs => enter [1, 1]; rw [← h]
  rw [Category.assoc, Category.assoc, ← Category.assoc (X.fromSpecResidueField _), h2, h]
end GlobalTheory.DegKer
