-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.gs_isoUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:19.065877+00:00
-- url     : https://prove2.me/submissions/dccc365f-d203-4952-aece-4987baae45b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (n : ℤ) (i₂ : L₂.ι) (i₁ : L₁.ι)
    {O : Y'.Opens} (hO : O ≤ m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)))
    (r : Z ⟶ Y') (z : Z) (hz : r z ∈ O) :
    gs r z O (res hO (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ n).val = (isoVal w (r ≫ m) z i₂ i₁ ^ n).val :=
  (gs_unit r z O hz _).trans (congrArg Units.val ((map_zpow _ _ _).trans (congrArg (· ^ n)
    ((gm_res r z hO hz _).trans (gm_pull r m z _ (hO hz) _)))))
end GlobalTheory.FieldBaseChange
