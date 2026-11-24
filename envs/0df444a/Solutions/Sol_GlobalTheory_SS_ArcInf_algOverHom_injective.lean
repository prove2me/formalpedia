-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.algOverHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:28.130207+00:00
-- url     : https://prove2.me/submissions/5db73e22-c645-4372-8848-8d261eb963ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution : Function.Injective (algOverHom : (A →ₐ[k] B) → _) := by
  intro a b h
  have h1 : spMap (a : A →+* B) = spMap (b : A →+* B) := congrArg (fun x => x.left) h
  have h2 := Spec.map_injective h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)
end GlobalTheory.SS.ArcInf
