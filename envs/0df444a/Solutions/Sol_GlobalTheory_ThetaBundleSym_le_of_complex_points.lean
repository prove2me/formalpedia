-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.le_of_complex_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:32.344199+00:00
-- url     : https://prove2.me/submissions/7ca65255-5485-45f5-8aaa-8fb691122c22

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSym
variable {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {Z : Type} {ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
namespace GlobalTheory.ThetaBundleSym
theorem _root_.solution (hex : Function.Surjective ex) {U V : X.left.Opens}
    (h : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → ⊤ ≤ (ex z).left ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := (U : Set X.left) ∩ (V : Set X.left)ᶜ) ⟨y, hy, hyV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ X := Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
  obtain ⟨z, hz⟩ := hex p
  have hp : ∀ W : X.left.Opens, ⊤ ≤ (ex z).left ⁻¹ᵁ W ↔ x ∈ W := by
    intro W
    rw [hz]
    refine (top_le_preimage_iff_mem (pointOfClosedPoint X.hom x hx) W).trans ?_
    exact (pointOfClosedPoint_apply X.hom x hx _).symm ▸ Iff.rfl
  exact hxV ((hp V).1 (h z ((hp U).2 hxU)))
end GlobalTheory.ThetaBundleSym
