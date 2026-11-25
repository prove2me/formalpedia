-- Prove2me | solution 1 for GlobalTheory.GlobalLift.weilIs_of_commIsOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:07:51.359113+00:00
-- url     : https://prove2.me/submissions/eb4f6aa7-f1f8-4bc9-b262-ce0377c2e67b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_change
import Theorems.Thm_GlobalTheory_CommPairing_exists_commIsOf_pull


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
    {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) : WeilIs A L k θx.pt θy.pt c := by
  intro p
  obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
  exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
    commIsOf_change hG hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩
end GlobalTheory.GlobalLift
