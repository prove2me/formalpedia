-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.germ_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:34.316507+00:00
-- url     : https://prove2.me/submissions/b409ce75-3faf-4146-8471-59733d8a6dce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
namespace GlobalTheory.SS.StalkDer
theorem _root_.solution (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (W : P.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hz : z ∈ W) (u : Γ(X.left, V)) :
    (P.presheaf.germ W z hz).hom ((f.appLE V W h).hom u) = gm f z V (h hz) u :=
  TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE h) z hz _
end GlobalTheory.SS.StalkDer
