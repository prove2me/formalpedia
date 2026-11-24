-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.top_le_wchart_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:45.011491+00:00
-- url     : https://prove2.me/submissions/f33eb9f9-0c59-4fcb-a7e6-ccbd8c8d1775

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (j : Fin 2 → L.ι)
    (x : Z ⟶ Y) (y₀ y₁ : Z ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j ↔ ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1) := by
  rw [top_le_wchart_iff, Fin.forall_fin_two]
  simp [h₀, h₁]
end GlobalTheory.ThetaGroupFrame
