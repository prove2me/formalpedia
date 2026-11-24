-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.gs_prodFn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:52.970138+00:00
-- url     : https://prove2.me/submissions/1e8621a4-d5ae-41aa-91ba-412688df9310

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


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
theorem _root_.solution (s t) :
    gs r z _ (prodFn H U V (s + t)) = gs r z _ (prodFn H U V s) + gs r z _ (prodFn H U V t) :=
  (congrArg (gs r z _) (map_add (mm H U V _ inf_le_left inf_le_right) s t)).trans (gs_add r z _ hz _ _)
end GlobalTheory.SectionsProduct
