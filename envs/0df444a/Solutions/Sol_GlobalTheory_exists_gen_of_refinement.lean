-- Prove2me | solution 1 for GlobalTheory.exists_gen_of_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:56.788052+00:00
-- url     : https://prove2.me/submissions/b086bb95-fafc-4a37-b984-b30838c8656e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution (L : LB Y) (hL : L.IsLB) {A : Type} (W : A → Y.Opens)
    (hW : ∀ y : Y, ∃ a, y ∈ W a) (e : A → L.ι) (he : ∀ a, W a ≤ L.U (e a)) (u : ∀ a, Γ(Y, W a)ˣ)
    (hu : ∀ a b (y : Y), y ∈ W a → y ∈ W b →
      gm (𝟙 Y) y (W a) (u a) = gm (𝟙 Y) y _ (L.g (e a) (e b)) * gm (𝟙 Y) y (W b) (u b)) :
    ∃ t : L.Gen, t.IsGen := by
  have le₁ : ∀ i a, L.U i ⊓ W a ≤ L.U i ⊓ L.U (e a) := fun i a => inf_le_inf_left _ (he a)
  let v : ∀ i a, Γ(Y, L.U i ⊓ W a)ˣ := fun i a =>
    res (le₁ i a) (L.g i (e a)) * res inf_le_right (u a)
  have hv : ∀ i a (y : Y), y ∈ L.U i ⊓ W a → gm (𝟙 Y) y (L.U i ⊓ W a) (v i a) =
      gm (𝟙 Y) y _ (L.g i (e a)) * gm (𝟙 Y) y (W a) (u a) := fun i a y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))
  have glue : ∀ i, ∃ s : Γ(Y, L.U i)ˣ, ∀ a, res (inf_le_left : L.U i ⊓ W a ≤ L.U i) s = v i a := by
    intro i
    refine glue_unit (L.U i) (fun a => L.U i ⊓ W a) (fun a => inf_le_left) (fun y hy => ?_) (v i) ?_
    · obtain ⟨a, ha⟩ := hW y
      exact Opens.mem_iSup.2 ⟨a, hy, ha⟩
    · intro a b y hy
      rw [hv i a y hy.1, hv i b y hy.2, hu a b y hy.1.2 hy.2.2, ← mul_assoc,
        gm_cocycle hL (𝟙 Y) y hy.1.1 (he a hy.1.2) (he b hy.2.2)]
  choose s hs using glue
  have hs' : ∀ i a (y : Y), y ∈ L.U i ⊓ W a → gm (𝟙 Y) y (L.U i) (s i) =
      gm (𝟙 Y) y _ (L.g i (e a)) * gm (𝟙 Y) y (W a) (u a) := fun i a y hy => by
    rw [← hv i a y hy, ← hs i a]
    exact (gm_res _ y _ hy _).symm
  refine ⟨⟨s⟩, fun i j => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hW y
  rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, hs' i a y ⟨hy.1, ha⟩, hs' j a y ⟨hy.2, ha⟩,
    ← mul_assoc, gm_cocycle hL (𝟙 Y) y hy.1 hy.2 (he a ha)]
end GlobalTheory
