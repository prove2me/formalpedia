-- Prove2me | solution 1 for GlobalTheory.KerPow.gen_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:54.556586+00:00
-- url     : https://prove2.me/submissions/89d251ce-f13b-4536-98da-140b26578195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
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
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
namespace GlobalTheory.KerPow
theorem _root_.solution {M M' : LB Y} (e : M'.ι → M.ι) (hU : ∀ j, M'.U j ≤ M.U (e j))
    (hg : ∀ i j (y : Y), y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y (M'.U i ⊓ M'.U j) (M'.g i j) = gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j)) (M.g (e i) (e j)))
    (h : ∃ t : LB.Gen M, t.IsGen) : ∃ t' : LB.Gen M', t'.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => res (hU j) (t.s (e j))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (e i) ⊓ M.U (e j) := ⟨hU i hy.1, hU j hy.2⟩
  have h1 := congrArg (gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j))) (ht (e i) (e j))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at h1
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy, hg i j y hy.1 hy.2]
  exact (gm_res (𝟙 Y) y (hU i) (show y ∈ M'.U i from hy.1) _).trans
    (h1.trans (congrArg _ (gm_res (𝟙 Y) y (hU j) (show y ∈ M'.U j from hy.2) _).symm))
end GlobalTheory.KerPow
