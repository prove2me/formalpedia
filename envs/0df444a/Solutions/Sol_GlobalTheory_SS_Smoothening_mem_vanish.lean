-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.mem_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:24.565941+00:00
-- url     : https://prove2.me/submissions/6abf51a5-88e5-4ba9-b412-6cacb0dc48e6

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
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution {π : R} {E : Pts R B} {b : B} : b ∈ vanish π E ↔
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b := Iff.rfl
end GlobalTheory.SS.Smoothening
