-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.jet_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:39.76983+00:00
-- url     : https://prove2.me/submissions/75f50add-c97c-4049-9360-0788292bdd34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_TangentOrigin_fderiv_val_res
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd

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
namespace GlobalTheory.TangentOrigin
theorem _root_.solution (w : Fin g → ℂ) {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    jet u w V hV (resG A.left e f) = jet u w W hW f := by
  refine TrivSqZeroExt.ext (evalPt_res _ e hW hV f) ?_
  rw [jet_snd, jet_snd, fderiv_val_res u e hW hV]
end GlobalTheory.TangentOrigin
