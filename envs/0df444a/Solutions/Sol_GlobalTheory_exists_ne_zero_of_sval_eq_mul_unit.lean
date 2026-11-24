-- Prove2me | solution 1 for GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:54.589076+00:00
-- url     : https://prove2.me/submissions/69db84e6-fe9c-45df-a43d-4adca85f78c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsNeZeroIffSvalGenericPointNeZero
import Theorems.Thm_GlobalTheory_exists_ne_zero_iff_sval_ne_zero
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
theorem _root_.solution : ∀ (Y X : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φ'' : K'' → (Y ⟶ X)) (ε'' : K'' → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (d : LB.Sec (LB.LinComb L φ'' ε'')), (∀ (y : Y) (J), Good L y J → ∃ v : (Y.presheaf.stalk y)ˣ, sval d (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J * v.val) → (∃ j, s.f j ≠ 0) → (∃ j, s'.f j ≠ 0) → ∃ j, d.f j ≠ 0 := by
  intro Y X _ L hL K K' K'' _ _ _ φ ε φ' ε' φ'' ε'' s s' d h hs hs'
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ (genericPoint Y))
  have hG : Good L (genericPoint Y) J := hJ
  obtain ⟨v, hv⟩ := h _ J hG
  rw [exists_ne_zero_iff_sval_ne_zero _ hG] at hs hs' ⊢
  rw [hv]
  exact mul_ne_zero (mul_ne_zero hs hs') v.ne_zero
end GlobalTheory
