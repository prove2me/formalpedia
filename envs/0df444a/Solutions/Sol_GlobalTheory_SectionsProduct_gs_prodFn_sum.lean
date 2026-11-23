-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.gs_prodFn_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:35.26082+00:00
-- url     : https://prove2.me/submissions/dc311497-5ce0-4c92-b710-423ebaf3168f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_tmul

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
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
variable {U U' : X₁.Opens} {V V' : X₂.Opens} (r : T ⟶ W) (z : T) (hz : r z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V)
include hz
namespace GlobalTheory.SectionsProduct
theorem _root_.solution {n : ℕ} (a : Fin n → Fn i₁ U) (b : Fin n → Fn i₂ V) :
    gs r z _ (prodFn H U V (∑ i, a i ⊗ₜ b i)) = ∑ i, gs (r ≫ p) z U (a i) * gs (r ≫ q) z V (b i) :=
  (congrArg (gs r z _) (map_sum (mm H U V _ inf_le_left inf_le_right) _ _)).trans ((gs_sum' r z _ hz _).trans
    (Finset.sum_congr rfl fun i _ => gs_prodFn_tmul H r z hz (a i) (b i)))
end GlobalTheory.SectionsProduct
