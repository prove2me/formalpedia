-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.chr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:52.289822+00:00
-- url     : https://prove2.me/submissions/fb184122-d827-4044-88fe-89943f5cd22a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
import Theorems.Thm_GlobalTheory_SS_WtRat_chr_eq

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {k : Type} [Field k] {X : Type} [AddCommGroup X] {R : Type} [CommRing R] {s : Sp R ⟶ Sp k}
namespace GlobalTheory.SS.WtRat
theorem _root_.solution (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ χ' : X) :
    chr t (χ + χ') = chr t χ * chr t χ' := by
  rw [chr_eq, chr_eq, chr_eq, ofAdd_add, map_mul, Units.val_mul]
  exact map_mul _ _ _
end GlobalTheory.SS.WtRat
