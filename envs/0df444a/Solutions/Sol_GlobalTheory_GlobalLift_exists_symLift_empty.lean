-- Prove2me | solution 1 for GlobalTheory.GlobalLift.exists_symLift_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:01.073548+00:00
-- url     : https://prove2.me/submissions/577584a3-fd5f-4649-b058-cd442d4eb3a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution (hL : L.IsLB) (n : ℕ) {T : Over S} [IsEmpty T.left] (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n x θ := by
  have he : ∀ {Q : Prop} (_ : (T ⊗ A).left), Q := fun y => isEmptyElim ((fst T A).left y)
  exact ⟨⟨x, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y⟩, rfl, corr_of_val hL fun y _ _ => he y,
    ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y, corr_of_val hL fun y _ _ => he y⟩
end GlobalTheory.GlobalLift
