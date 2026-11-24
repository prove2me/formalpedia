-- Prove2me | solution 1 for GlobalTheory.SS.isAffine_splitTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:40.956613+00:00
-- url     : https://prove2.me/submissions/62b6c6da-42fa-49c4-ae53-f123d4bf72f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGSplitTorusPow

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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Sp k) X).left := by
  have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Spec ZU.{0}) := inferInstance
  exact inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))
end GlobalTheory.SS
