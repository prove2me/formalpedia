-- Prove2me | solution 1 for GlobalTheory.ZJ.hasWt_zero_appLE_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:38:19.112772+00:00
-- url     : https://prove2.me/submissions/a8af2527-6b44-4dff-8a1a-4c4cd703e5a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Theorems.Thm_GlobalTheory_ZJ_charUnit_zero_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq


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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs
namespace GlobalTheory.ZJ
theorem _root_.solution {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) (a : Γ(S, ⊤)) :
    HasWt i V ((H.hom.appLE ⊤ V le_top).hom a) 0 := by
  intro Y t g h h'
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  refine (appLE_appLE _ H.hom (U := ⊤) le_top h' a).trans (Eq.trans ?_ (appLE_appLE _ H.hom (U := ⊤) le_top h a).symm)
  exact congrArg (fun ψ : Γ(S, ⊤) ⟶ Γ(Y.left, ⊤) => ψ.hom a)
    (appLE_of_eq ((Over.w _).trans (Over.w _).symm) _ _ _ _)
end GlobalTheory.ZJ
