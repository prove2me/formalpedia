-- Prove2me | solution 1 for GlobalTheory.GlobalLift.weilIs_iff_commIsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:24.743656+00:00
-- url     : https://prove2.me/submissions/29d5c285-d053-447c-9424-0bfa54addb3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Theorems.Thm_GlobalTheory_GlobalLift_weilIs_of_commIsOf
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_commIsOf
import Theorems.Thm_GlobalTheory_CommutatorPairing_weilIs_unique


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.GlobalLift
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k θx.pt θy.pt c ↔ CommIsOf A L k θx θy c := by
  refine ⟨fun H => ?_, weilIs_of_commIsOf hG hA hL⟩
  obtain ⟨c₀, h₀⟩ := CommutatorPairing.exists_commIsOf hG hA hL θx θy
  rw [CommutatorPairing.weilIs_unique hG hA hL H (weilIs_of_commIsOf hG hA hL h₀)]
  exact h₀
end GlobalTheory.GlobalLift
