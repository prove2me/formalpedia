-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.gmDual_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:20:36.803698+00:00
-- url     : https://prove2.me/submissions/217ff829-3a85-4227-aec2-3f0b5f8c1ad4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_gm_res

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
theorem _root_.solution (D : VF X) (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V)
    (hz : z ∈ f ⁻¹ᵁ V') (u : Γ(X.left, V)) :
    gmDual D f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gmDual D f z V (h hz) u :=
  TrivSqZeroExt.ext (gm_res f z V V' h hz u) (by
    show gm f z V' hz (D.D V' _) = gm f z V (h hz) (D.D V u)
    rw [D.res, gm_res])
end GlobalTheory.SS.StalkDer
