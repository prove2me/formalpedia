-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.fderiv_val_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:36.745067+00:00
-- url     : https://prove2.me/submissions/5075b79b-fd25-460c-bd8d-511b273d8116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res

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
theorem _root_.solution {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left V (resG A.left e f)) 0 =
      fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [eventually_mem u hW, eventually_mem u hV] with z hz hz'
  rw [valAt'_eq_evalPt _ _ hz, valAt'_eq_evalPt _ _ hz', evalPt_res]
end GlobalTheory.TangentOrigin
