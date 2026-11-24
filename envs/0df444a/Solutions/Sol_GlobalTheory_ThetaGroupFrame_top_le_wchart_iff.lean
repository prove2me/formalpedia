-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.top_le_wchart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:14.988601+00:00
-- url     : https://prove2.me/submissions/c1b90022-d0d1-4c4c-9652-b6149341996b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover

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
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Z ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  unfold LB.wchart
  constructor
  · intro h k z _
    have hz : x z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(L.U (j k)) := h (show z ∈ (⊤ : Z.Opens) from trivial)
    exact Set.mem_iInter.mp hz k
  · intro h z _
    show x z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(L.U (j k))
    exact Set.mem_iInter.mpr fun k => h k (show z ∈ (⊤ : Z.Opens) from trivial)
end GlobalTheory.ThetaGroupFrame
