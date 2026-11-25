-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.weilIs_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:41.305166+00:00
-- url     : https://prove2.me/submissions/fdb91c54-0377-4ddb-b06a-9d5eb464baf6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommutatorPairing_commVal_indep
import Theorems.Thm_GlobalTheory_CommutatorPairing_gm_unitRes
import Theorems.Thm_P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') : c = c' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', ⟨θx', θy', hx', hy'⟩, H'⟩ := h' p
  let z : (V ⊓ V').toScheme := ⟨p, hV, hV'⟩
  let t := overLE (inf_le_left : V ⊓ V' ≤ V)
  let t' := overLE (inf_le_right : V ⊓ V' ≤ V')
  choose J hJ using fun χ : (overRes (V ⊓ V')).left ⟶ A.left => exists_chart hL (χ z)
  have e₁ := (commIsOf_iff hL _ _ _).1 (H θx θy hx hy) _ t 1 z J hJ
  have e₂ := (commIsOf_iff hL _ _ _).1 (H' θx' θy' hx' hy') _ t' 1 z J hJ
  have e₃ := commVal_indep hG hA hL θx θy θx' θy' t t'
    (by rw [hx, hx', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι])
    (by rw [hy, hy', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι]) 1 z J hJ
  have f₁ := gm_unitRes V c (T.left.homOfLE (inf_le_left : V ⊓ V' ≤ V)) z
  have f₂ := gm_unitRes V' c' (T.left.homOfLE (inf_le_right : V ⊓ V' ≤ V')) z
  rw [Scheme.homOfLE_ι] at f₁ f₂
  exact gm_inj (V ⊓ V').ι z (U := ⊤) (U' := ⊤) trivial trivial (f₁.symm.trans (e₁.symm.trans (e₃.trans (e₂.trans f₂))))
end GlobalTheory.CommutatorPairing
