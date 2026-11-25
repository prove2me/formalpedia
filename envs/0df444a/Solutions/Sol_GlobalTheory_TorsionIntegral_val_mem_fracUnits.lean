-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.val_mem_fracUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:00:02.203432+00:00
-- url     : https://prove2.me/submissions/d8f268fd-eb1a-4951-b03f-dbbb5a08470d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_GlobalTheory_TorsionIntegral_val_trans
import Theorems.Thm_GlobalTheory_TorsionIntegral_gm_mem_fracUnits
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution [IsAffine Y] (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {ψ' : K → (Z ⟶ X)}
    (hψ : ∀ k, ψ' k = φ ≫ ψ k) {J J' : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hJ' : Good L z J')
    (t : LB.Gen (LB.LinComb L ψ' ε)) (ht : t.IsGen) (hv : val t (𝟙 Z) z J' ∈ fracUnits (germTop φ z)) :
    val t (𝟙 Z) z J ∈ fracUnits (germTop φ z) := by
  obtain rfl : ψ' = fun k => φ ≫ ψ k := funext hψ
  rw [val_trans φ z ψ ε hJ hJ' t ht]
  refine mul_mem (prod_mem fun k _ => zpow_mem ?_ _) hv
  have hm : ψ k (φ z) ∈ L.U (J (φ ≫ ψ k)) ⊓ L.U (J' (φ ≫ ψ k)) := ⟨hJ (φ ≫ ψ k), hJ' (φ ≫ ψ k)⟩
  dsimp only
  rw [← gm_pull φ (ψ k) z _ hm]
  exact gm_mem_fracUnits φ z _ hm _
end GlobalTheory.TorsionIntegral
