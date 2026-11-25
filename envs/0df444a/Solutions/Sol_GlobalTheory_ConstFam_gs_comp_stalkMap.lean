-- Prove2me | solution 1 for GlobalTheory.ConstFam.gs_comp_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:44.694811+00:00
-- url     : https://prove2.me/submissions/28b204a0-76c5-4c12-8dd9-31d65ae73571

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap


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
    (a : Γ(X, U)) : gs (σ ≫ r) z U a = (σ.stalkMap z).hom (gs r (σ z) U a) := by
  rw [← gs_pull σ r z U h, gs_stalkMap σ z _ h, gs_pull (𝟙 _) r (σ z) U h, Category.id_comp]
end GlobalTheory.ConstFam
