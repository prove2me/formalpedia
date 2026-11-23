-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.geomIrr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:30.839251+00:00
-- url     : https://prove2.me/submissions/11d4ae92-adf8-449e-8e83-af93cd0f2121

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
import Theorems.Thm_GlobalTheory_geometricallyIrreducible_of_isAlgClosed


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
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (M : Model R A)
    (hM : M.Irr) (s : Sp R) (hs : s = IsLocalRing.closedPoint R) :
    GeometricallyIrreducible (M.Y.hom.fiberToSpecResidueField s) := by
  have := M.smooth
  have h0 : s.asIdeal = IsLocalRing.maximalIdeal R := by rw [hs]; rfl
  have h0' : s.asIdeal.IsMaximal := h0 ▸ IsLocalRing.maximalIdeal.isMaximal R
  have h1 : IsAlgClosed s.asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField R) _
      ((Ideal.quotEquivOfEq h0.symm).trans
        (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField _)))
  have h2 : IsAlgClosed ((Sp R).residueField s) :=
    IsAlgClosed.of_ringEquiv s.asIdeal.ResidueField _
      (Scheme.Spec.residueFieldIso (CommRingCat.of R) s).commRingCatIsoToRingEquiv.symm
  have h3 : IrreducibleSpace (M.Y.hom.fiber s) := by
    have : IrreducibleSpace (M.Y.hom ⁻¹' {s} : Set _) :=
      Subtype.irreducibleSpace (hs ▸ hM)
    exact (M.Y.hom.fiberHomeo _).irreducibleSpace_iff.2 this
  have h4 : LocallyOfFiniteType (M.Y.hom.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  exact @geometricallyIrreducible_of_isAlgClosed _ _ h2 _ _ h4 h3
end GlobalTheory.SS.StrictLaw
