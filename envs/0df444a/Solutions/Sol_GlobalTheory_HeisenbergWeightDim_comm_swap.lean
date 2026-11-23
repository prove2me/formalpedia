-- Prove2me | solution 1 for GlobalTheory.HeisenbergWeightDim.comm_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:42.739389+00:00
-- url     : https://prove2.me/submissions/25f74077-b1fc-47b4-8047-11ff084ca1d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_units_eq_of_smul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.HeisenbergWeightDim
variable {F : Type} [Field F] {A : Type} [CommGroup A] {E : Type} [AddCommGroup E] [Module F E]
variable [Nontrivial E] {e : A → A → Fˣ} {Φ : A → (E ≃ₗ[F] E)}
namespace GlobalTheory.HeisenbergWeightDim
theorem _root_.solution (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a b : A) :
    e a b * e b a = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hw : Φ a (Φ b v) ≠ 0 := by simpa using hv
  apply units_eq_of_smul_eq hw
  rw [Units.val_mul, mul_smul, ← hc b a v, ← hc a b v, Units.val_one, one_smul]
end GlobalTheory.HeisenbergWeightDim
