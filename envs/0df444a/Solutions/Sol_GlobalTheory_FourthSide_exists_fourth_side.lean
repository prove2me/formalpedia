-- Prove2me | solution 1 for GlobalTheory.FourthSide.exists_fourth_side
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.741126+00:00
-- url     : https://prove2.me/submissions/a9eb3c13-184a-4def-8499-43ee375160d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
import Theorems.Thm_GlobalTheory_FourthSide_gm_pull_g
import Theorems.Thm_GlobalTheory_FourthSide_germ_change
import Theorems.Thm_GlobalTheory_FourthSide_exists_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FourthSide
variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}
namespace GlobalTheory.FourthSide
theorem _root_.solution (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by
  rw [isGen_iff] at hw hwL hwe
  choose s hs using exists_unit hM hM' hL hL' e₁ e₂ hw hwL hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₂ b₂ a₄ b₄
    obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' (r z)))
    obtain ⟨l, hl⟩ := exists_chart hL (Ψ (fG' (r z)))
    have a₄' := mem_pull.1 a₄
    have b₄' := mem_pull.1 b₄
    have c := germ_change e₁ e₂ hw hwL hwe r z i i j j' l l _ _ hi a₂ hl a₄' hi b₂ hl b₄'
    rw [← hs j _ Z r z i l hi a₂ hl a₄', ← hs j' _ Z r z i l hi b₂ hl b₄',
      ← gm_pull_g L' fG' r z _ _ a₄' b₄'] at c
    exact c
  · exact (congrArg (gw w (r ≫ pG') z jM jM' * ·) (hs jM' jL' Z r z jM jL a₁ a₂ a₃ a₄)).trans
      (mul_inv_cancel_left _ _)
end GlobalTheory.FourthSide
