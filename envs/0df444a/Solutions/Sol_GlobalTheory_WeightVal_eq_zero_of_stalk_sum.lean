-- Prove2me | solution 1 for GlobalTheory.WeightVal.eq_zero_of_stalk_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:06.733188+00:00
-- url     : https://prove2.me/submissions/c1bad9b1-17e1-4bea-8abb-f1ee4e281980

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.WeightVal
namespace GlobalTheory.WeightVal
theorem _root_.solution {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens}
    (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Y s h (fn_ext fun w hw => ?_)
  have k : ∀ c : Γ(Y.left, V),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  rw [DVR.gs_fsum (𝟙 _) w _ hw, gs_eq (𝟙 _) w _ hw 0, map_zero, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) (hs w hw)
  rw [gs_mul (𝟙 _) w _ hw, k, gs_res (𝟙 _) w _ hw]
end GlobalTheory.WeightVal
