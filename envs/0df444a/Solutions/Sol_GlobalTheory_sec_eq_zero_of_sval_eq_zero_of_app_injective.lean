-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_of_sval_eq_zero_of_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:41.330566+00:00
-- url     : https://prove2.me/submissions/981b1221-b89e-438a-a23c-e523ec00b023

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppWhiskerRightInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (hr : ∀ U : Y.Opens, Function.Injective (r.app U).hom) (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j : K → L.ι) : d.f j = 0 := by
  apply hr (LB.wchart L φ j)
  refine fn_ext fun z hz => ?_
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hz' : r z ∈ LB.wchart L φ j := hz
  have e₁ : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    (sec_trans d r z hz' (Good.mem hI φ r)).trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  have e₂ : gs r z (LB.wchart L φ j) 0 = 0 := by
    rw [gs_eq r z _ hz', map_zero, map_zero]
  refine (gs_pull (𝟙 Z) r z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 Z) r z _ hz' _).symm)
  rw [Category.id_comp]
  exact e₁.trans e₂.symm
end GlobalTheory
