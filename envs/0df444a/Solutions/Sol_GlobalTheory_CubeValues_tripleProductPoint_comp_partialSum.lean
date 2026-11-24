-- Prove2me | solution 1 for GlobalTheory.CubeValues.tripleProductPoint_comp_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:38:36.687806+00:00
-- url     : https://prove2.me/submissions/bcc268be-4e3e-46ec-85ca-de7c408fe472

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Theorems.Thm_GlobalTheory_CubeValues_comp_psum

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
noncomputable section
open GlobalTheory GlobalTheory.CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)
namespace GlobalTheory.CubeValues
theorem _root_.solution (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    (pt3 u x).left ≫ (psum A (x3 A) I).left = (u.ex (∑ a ∈ I, x a)).left := by
  rw [← Over.comp_left, comp_psum u (pt3 u x) (x3 A) x _ I]
  intro k
  fin_cases k <;> simp [pt3, x3]
end GlobalTheory.CubeValues
