-- Prove2me | solution 1 for GlobalTheory.UnifZero.app_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:03:38.535579+00:00
-- url     : https://prove2.me/submissions/5ae32c2b-5b6a-4783-8615-bb59180c03f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
namespace GlobalTheory.UnifZero
theorem _root_.solution (f : Y' ⟶ Y) {U : Y.Opens} {V W : Y'.Opens} (h : W ≤ V) (h' : W ≤ f ⁻¹ᵁ U)
    {u : Γ(Y', V)ˣ} (hu : u = 1) {x : Γ(Y, U)} {a : Γ(Y, ⊤)} (hx : x = resTop U a) :
    (Y'.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) * (res h u).val =
      resTop W (f.appTop.hom a) := by
  rw [hu, hx, map_one, Units.val_one, _root_.mul_one, app_resTop, DVR.SecOps.resTop_res]
end GlobalTheory.UnifZero
