-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.free_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:39.625008+00:00
-- url     : https://prove2.me/submissions/8e40c51f-0909-4513-892a-104f28fa8f39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (f : C) (M : Type) [AddCommGroup M] [Module C M] (D : Type) [CommRing D] [Algebra C D]
    [IsLocalization.Away f D] (h : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free D (D ⊗[C] M) := by
  haveI : Module.Free (Localization.Away f) (Localization.Away f ⊗[C] M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) D
  letI : Algebra (Localization.Away f) D := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower C (Localization.Away f) D := IsScalarTower.of_algHom e.toAlgHom
  exact Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange C (Localization.Away f) D D M)
end GlobalTheory.SS.Smoothening
