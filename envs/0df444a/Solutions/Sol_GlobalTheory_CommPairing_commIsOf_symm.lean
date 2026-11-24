-- Prove2me | solution 1 for GlobalTheory.CommPairing.commIsOf_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:03.226566+00:00
-- url     : https://prove2.me/submissions/13ccf25d-409e-437b-8d84-5aaab5ca4556

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommPairing
theorem _root_.solution (hL : L.IsLB) {T : Over S} {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θy θx c⁻¹ := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  rw [H Z r z J hJ, map_inv, mul_inv_cancel_right]
end GlobalTheory.CommPairing
