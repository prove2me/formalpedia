-- Prove2me | solution 1 for GlobalTheory.ConstFam.toStk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:39:30.76189+00:00
-- url     : https://prove2.me/submissions/58cc583a-8975-4871-9f53-8763b811f49b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution {F : Type} [Field F] (z : Sp F) (a : F) : toStk z a = constVal (𝟙 _) z a :=
  (gs_eq (𝟙 _) z ⊤ trivial _).symm
end GlobalTheory.ConstFam
