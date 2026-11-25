-- Prove2me | solution 1 for GlobalTheory.ConstFam.gm_comp_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:41.446797+00:00
-- url     : https://prove2.me/submissions/794f5f50-9866-4671-b9f8-20a21e59ebb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_ConstFam_gs_comp_stalkMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.ConstFam
theorem _root_.solution {X Y Z : Scheme.{0}} (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (σ z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (σ ≫ r) z U a = Units.map (σ.stalkMap z).hom.toMonoidHom (gm r (σ z) U a) :=
  Units.ext ((gs_unit (σ ≫ r) z U h a).symm.trans ((gs_comp_stalkMap σ r z U h _).trans
    (congrArg _ (gs_unit r (σ z) U h a))))
end GlobalTheory.ConstFam
