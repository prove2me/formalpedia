-- Prove2me | solution 1 for GlobalTheory.SS.Height.gs_pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:02.376418+00:00
-- url     : https://prove2.me/submissions/9c4fb5f0-df66-4cda-a055-6f2ef74001ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (Pl : Places k K)
namespace GlobalTheory.SS.Height
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {N : ℤ} (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : x y ∈ L.U i) (hj : x y ∈ L.U j) :
    gs x y (L.U i) (s.f i) = (gm x y (L.U i ⊓ L.U j) (L.g i j) ^ N).val * gs x y (L.U j) (s.f j) := by
  have hm : x y ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  refine (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (s.compat i j)).trans
    ((gs_mul x y _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res x y _ hm _))))
  exact (gs_unit x y _ hm (L.g i j ^ N)).trans (congrArg Units.val (map_zpow _ _ _))
end GlobalTheory.SS.Height
