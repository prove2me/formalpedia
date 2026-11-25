-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.val_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:08.926576+00:00
-- url     : https://prove2.me/submissions/0c3c668a-092b-45f8-a9f7-ebe641f1795a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution (φ : Z ⟶ Y) (z : Z) {J₀ : (Z ⟶ X) → L.ι} (hJ₀ : Good L z J₀)
    (h₀ : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q))) {ψ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L ψ ε)) (r : Y ⟶ Y') : val t (φ ≫ r) z J₀ ∈ (gm φ z ⊤).range := by
  rw [← val_pull hJ₀]
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (fun k => r ≫ ψ k) (fun k => J₀ (φ ≫ r ≫ ψ k)) :=
    fun y _ => Set.mem_iInter.2 fun k => h₀ (r ≫ ψ k) y
  exact ⟨res le _, gm_res φ z le trivial _⟩
end GlobalTheory.TorsionIntegral
