-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.tangent_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:38.04784+00:00
-- url     : https://prove2.me/submissions/50516eda-a745-4e01-8848-d60afe943f84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_comp

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
open GlobalTheory GlobalTheory.TangentOrigin
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {v : epsR ℂ ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    ⊤ ≤ v.left ⁻¹ᵁ W ↔ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := by
  rw [← tangent_comp (u := u) hv]
  exact top_le_preimage_iff v.left W
end GlobalTheory.TangentOrigin
