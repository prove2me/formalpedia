-- Prove2me | solution 1 for GlobalTheory.ZJ.eSec_comp_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:34:06.26629+00:00
-- url     : https://prove2.me/submissions/5435dbc5-dfce-4b86-935b-b2f2cb815bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    eSec G' ≫ φ = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]
end GlobalTheory.ZJ
