-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.exists_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:02.333229+00:00
-- url     : https://prove2.me/submissions/ffd9243b-7467-416b-a9b7-27850a420950

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_wchart
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_affine_le

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
namespace GlobalTheory.SectionsProduct
theorem _root_.solution (hL : L.IsLB) [CompactSpace Y] (φ : K → (Y ⟶ B)) :
    ∃ (P : Type) (_ : Finite P) (U : P → Y.Opens) (j : P → K → L.ι), (∀ p, IsAffineOpen (U p)) ∧
      (∀ p, U p ≤ LB.wchart L φ (j p)) ∧ ∀ y, ∃ p, y ∈ U p := by
  choose j hj using exists_wchart hL φ
  choose U h₁ h₂ h₃ using fun y => exists_affine_le (hj y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, h₂ y⟩)
  refine ⟨s, inferInstance, fun p => U p, fun p => j p, fun p => h₁ p, fun p => h₃ p, fun y => ?_⟩
  obtain ⟨p, hp, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact ⟨⟨p, hp⟩, h⟩
end GlobalTheory.SectionsProduct
