-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.gs_sec_pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:47.825879+00:00
-- url     : https://prove2.me/submissions/c8066296-4bce-48d3-b6f9-b0685d39f8ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution {L : LB X} {m : ℤ} (s : LB.Sec (pw L m)) (r : Z ⟶ X) (z : Z) (i j : L.ι) (hi : r z ∈ L.U i)
    (hj : r z ∈ L.U j) :
    gs r z (L.U i) (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j) ^ m).val * gs r z (L.U j) (s.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat i j)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))))
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (map_zpow _ _ _))
end GlobalTheory.BoxDetUnique
