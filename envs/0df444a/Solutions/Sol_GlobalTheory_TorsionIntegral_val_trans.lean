-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.val_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:39:03.519333+00:00
-- url     : https://prove2.me/submissions/6eb76dfe-0251-4945-8c9b-6802075c2ddd

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
theorem _root_.solution (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {J J' : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (hJ' : Good L z J') (t : LB.Gen (LB.LinComb L (fun k => φ ≫ ψ k) ε)) (ht : t.IsGen) :
    val t (𝟙 Z) z J = trF ψ ε φ z (fun k => J (φ ≫ ψ k)) (fun k => J' (φ ≫ ψ k)) * val t (𝟙 Z) z J' := by
  rw [val_of t _ z J (fun k => J (φ ≫ ψ k)) (fun k => by rw [Category.id_comp]),
    val_of t _ z J' (fun k => J' (φ ≫ ψ k)) (fun k => by rw [Category.id_comp])]
  refine (gen_trans ht (𝟙 Z) z (j' := fun k => J' (φ ≫ ψ k)) (Set.mem_iInter.2 fun k => hJ (φ ≫ ψ k))
    (Set.mem_iInter.2 fun k => hJ' (φ ≫ ψ k))).trans ?_
  simp only [trF, Category.id_comp]
end GlobalTheory.TorsionIntegral
