-- Prove2me | solution 1 for GlobalTheory.CommPairing.weilIs_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:38.055615+00:00
-- url     : https://prove2.me/submissions/f9a3c289-e8d2-42bd-a99f-9ac8e3cdc50d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_symm

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
theorem _root_.solution (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k y x c⁻¹ := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H p
  refine ⟨V, hp, ⟨θy, θx, hy, hx⟩, fun θy θx hy hx => ?_⟩
  have e : unitRes V c⁻¹ = (unitRes V c)⁻¹ := map_inv _ _
  rw [e]
  exact commIsOf_symm hL (hc θx θy hx hy)
end GlobalTheory.CommPairing
