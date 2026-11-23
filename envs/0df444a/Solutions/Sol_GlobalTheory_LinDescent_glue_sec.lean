-- Prove2me | solution 1 for GlobalTheory.LinDescent.glue_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:02.519599+00:00
-- url     : https://prove2.me/submissions/161795ce-b595-458d-85a9-7db8e5eb74be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_glue_fn
import Theorems.Thm_GlobalTheory_LinDescent_gs_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.LinDescent
theorem _root_.solution {L : LB X} (hL : L.IsLB) {κ : Type} (W : X.Opens) (O : κ → X.Opens)
    (a : κ → L.ι) (hO : ∀ k, O k ≤ W) (ha : ∀ k, O k ≤ L.U (a k))
    (hc : ∀ x ∈ W, ∃ k, x ∈ O k) (b : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l →
      gs (𝟙 X) x (O k) (b k) = (gg L (𝟙 X) x (a k) (a l)).val * gs (𝟙 X) x (O l) (b l)) :
    ∃ m : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ L.U i → r z ∈ O k →
        gs r z _ (m i) = (gg L r z i (a k)).val * gs r z (O k) (b k) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ O k ⊓ L.U i →
      gs r z (O k ⊓ L.U i) (rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val *
        rs inf_le_left (b k)) = (gg L r z i (a k)).val * gs r z (O k) (b k) := fun Z r z i k hz => by
    rw [gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_g L r z hz.2 (ha k hz.1)]
  have : ∀ i, ∃ m : Γ(X, W ⊓ L.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k,
      r z ∈ L.U i → r z ∈ O k →
        gs r z _ m = (gg L r z i (a k)).val * gs r z (O k) (b k) := fun i => by
    obtain ⟨m, hm⟩ := glue_fn (W ⊓ L.U i) (fun k => O k ⊓ L.U i)
      (fun k => inf_le_inf_right _ (hO k))
      (fun x hx => (hc x hx.1).imp fun k hk => ⟨hk, hx.2⟩)
      (fun k => rs (le_inf inf_le_right (inf_le_left.trans (ha k))) (L.g i (a k)).val *
        rs inf_le_left (b k)) (fun k l x hk hl => by
        rw [v _ _ x i k hk, v _ _ x i l hl, h k l x hk.1 hl.1, ← mul_assoc, ← Units.val_mul,
          gm_cocycle hL (𝟙 X) x hk.2 (ha k hk.1) (ha l hl.1)])
    exact ⟨m, fun Z r z k hi hk => (hm Z r z k ⟨hk, hi⟩).trans (v Z r z i k ⟨hk, hi⟩)⟩
  choose m hm using this
  refine ⟨m, fun Z r z i j hW hi hj => ?_, fun Z r z i k => hm i Z r z k⟩
  obtain ⟨k, hk⟩ := hc _ hW
  rw [hm i Z r z k hi hk, hm j Z r z k hj hk, ← mul_assoc, ← Units.val_mul,
    gm_cocycle hL r z hi hj (ha k hk)]
end GlobalTheory.LinDescent
