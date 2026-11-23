-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isoVal_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:31.457587+00:00
-- url     : https://prove2.me/submissions/32edfc7c-e72f-481c-820c-48618adacac0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
theorem _root_.solution {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z)
    {i₂ j₂ : L₂.ι} {i₁ j₁ : L₁.ι} (a₂ : f₂ (r z) ∈ L₂.U i₂) (b₂ : f₂ (r z) ∈ L₂.U j₂)
    (a₁ : f₁ (r z) ∈ L₁.U i₁) (b₁ : f₁ (r z) ∈ L₁.U j₁) :
    isoVal w r z i₂ i₁ = gm (r ≫ f₂) z _ (L₂.g i₂ j₂) * (gm (r ≫ f₁) z _ (L₁.g i₁ j₁))⁻¹ * isoVal w r z j₂ j₁ := by
  have := (isGen_iff w).1 hw _ r z i₂ j₂ (fun _ => i₁) (fun _ => j₁) a₂ b₂ (mem_pull.2 a₁) (mem_pull.2 b₁)
  exact this.trans (congrArg (fun u => _ * u⁻¹ * _)
    (gm_pull_g L₁ f₁ r z (fun _ => i₁) (fun _ => j₁) (mem_pull.2 a₁) (mem_pull.2 b₁)))
end GlobalTheory.FieldBaseChange
