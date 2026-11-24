-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.isUnit_of_complex_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:35.265528+00:00
-- url     : https://prove2.me/submissions/1af20f14-c7fd-4815-8c58-5cebeb9edbfb

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
import Theorems.Thm_GlobalTheory_ThetaBundleSym_le_of_complex_points
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff


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
theorem _root_.solution (hex : Function.Surjective ex) {U : X.left.Opens} (f : Γ(X.left, U))
    (h : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → valAt' (ex z).left U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.left.basicOpen f := le_of_complex_points hex fun z hz =>
    (top_le_preimage_basicOpen_iff _ U f).2 (h z hz)
  exact X.left.toRingedSpace.isUnit_of_isUnit_germ U f fun p hp =>
    (X.left.mem_basicOpen f p hp).1 (hle hp)
end GlobalTheory.ThetaBundleSym
