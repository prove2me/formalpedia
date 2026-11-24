-- Prove2me | solution 1 for GlobalTheory.CubeValues.comp_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:51.25104+00:00
-- url     : https://prove2.me/submissions/c898e576-6110-4e43-9eda-ae6b68c4bcb2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Theorems.Thm_GlobalTheory_CubeValues_comp_foldr
import Theorems.Thm_GlobalTheory_CubeValues_ex_list_sum

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
theorem _root_.solution {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (w : Fin n → Fin g → ℂ) (h : ∀ k, p ≫ y k = u.ex (w k)) (I : Finset (Fin n)) :
    p ≫ psum A y I = u.ex (∑ a ∈ I, w a) := by
  have hs : ∑ a ∈ I, w a = (((List.finRange n).filter (fun a => decide (a ∈ I))).map w).sum := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext a
    simp
  rw [psum, comp_foldr, hs, ex_list_sum]
  exact congrArg List.prod (List.map_congr_left (fun k _ => h k))
end GlobalTheory.CubeValues
