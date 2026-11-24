-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.hom_ext_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:14.67716+00:00
-- url     : https://prove2.me/submissions/a53ae321-061f-424c-90e7-c056c5367480

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_chart
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


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
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
theorem _root_.solution (H : PointCriterion) (h1 : IsReduced Y.left) (h2 : LocallyOfFiniteType Y.hom)
    {κ : Type} {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (ha : ∀ c, IsAffineOpen (D c)) (f g : Y ⟶ X)
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y ≫ f = y ≫ g) : f = g := by
  refine (H X Y h1 h2 (fun y => y ≫ f) fun y => ?_).unique (fun _ => rfl) (fun y => (h y).symm)
  obtain ⟨c, hc⟩ := exists_chart hD (y ≫ f)
  exact ⟨f.left ⁻¹ᵁ D c, D c, (top_le_preimage_comp _ _ _).1 hc, ha c,
    fun y' hy' => (top_le_preimage_comp _ _ _).2 hy',
    fun φ => ⟨(f.left.app (D c)).hom φ, fun y' _ => valAt'_comp _ _ _ _⟩⟩
end GlobalTheory.ThetaModelGroup
