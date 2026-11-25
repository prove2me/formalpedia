-- Prove2me | solution 1 for GlobalTheory.UnifZero.unit_pow_mul_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:05.484976+00:00
-- url     : https://prove2.me/submissions/650f2061-0a73-403b-ae88-76a742e13649

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
    {u : Γ(Y', V)ˣ} (hu : u = 1) {x : Γ(Y, U)} {a : Γ(Y, ⊤)} (hx : x = resTop U a) (k : ℕ) :
    (res h u).val ^ k * (Y'.presheaf.map (homOfLE h').op).hom ((f.app U).hom x) =
      resTop W (f.appTop.hom a) := by
  rw [hu, hx, map_one, Units.val_one, one_pow, _root_.one_mul, app_resTop, DVR.SecOps.resTop_res]
end GlobalTheory.UnifZero
