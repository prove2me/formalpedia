-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.fibre_preirr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:00.20358+00:00
-- url     : https://prove2.me/submissions/5f813f60-9287-4671-ad84-f294f5a041a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution {P X Y S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ Y} {g : X ⟶ S} {f : Y ⟶ S}
    (h : IsPullback p q g f) (x : X)
    [hg : GeometricallyIrreducible (f.fiberToSpecResidueField (g x))] :
    IsPreirreducible (p ⁻¹' {x}) := by
  have h1 : IsPullback (p.fiberι x) (p.fiberToSpecResidueField x) p (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (f.fiberι (g x)) (f.fiberToSpecResidueField (g x)) f
      (S.fromSpecResidueField (g x)) := IsPullback.of_hasPullback _ _
  have h3 := h1.paste_horiz h.flip
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h4 := IsPullback.of_right' h3 h2
  have h5 : IrreducibleSpace (p.fiber x) :=
    hg.geometrically_irreducibleSpace _ _ _ h4
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (p.fiberι x).continuous.continuousOn
end GlobalTheory.SS.StrictLaw
