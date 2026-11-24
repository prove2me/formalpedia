-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.RegAt.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:09.853279+00:00
-- url     : https://prove2.me/submissions/28a95fcb-3b33-4ac8-a0b5-bb93ac338e0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_regOn_family
import Theorems.Thm_P2M_GlobalTheory_valAt__sum_98f4f63a0a11


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
namespace RegAt
theorem _root_.solution {κ : Type} [Fintype κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) : RegAt y (fun y' => ∑ c, s c y') := by
  obtain ⟨U, hU, hR⟩ := exists_regOn_family h
  choose ρ hρ using hR
  exact ⟨U, hU, ∑ c, ρ c, fun y' hy' => by
    rw [valAt'_sum]; exact Finset.sum_congr rfl fun c _ => hρ c y' hy'⟩
end RegAt
end GlobalTheory.ThetaModelGroup
