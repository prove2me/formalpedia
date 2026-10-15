-- Prove2me | solution 1 for OAI.CompactBanach.ambient_iterated_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:28:45.452602+00:00
-- url     : https://prove2.me/submissions/795f35c2-3391-4518-953d-28ac7b14c20d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean:L40-L71
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.ambient_iterated_cover. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers

-- ---- from OAI.Geometry.DoublingHilbert.IntrinsicCovers ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

                                                                                    
theorem ambient_iterated_cover {B : Type*} [MetricSpace B] {K : Set B} {L : ℕ}
    (h : AmbientDoubling K L) (n : ℕ) {x : B} (hx : x ∈ K) {r : ℝ} (hr : 0 < r) :
    ∃ centers : Finset B, (∀ c ∈ centers, c ∈ K) ∧ centers.card ≤ L ^ n ∧
      ∀ y ∈ K, dist y x < r → ∃ c ∈ centers, dist y c < r / (2 : ℝ) ^ n := by
  classical
  induction n generalizing x r with
  | zero =>
    refine ⟨{x}, ?_, ?_, ?_⟩
    · simpa only [Finset.mem_singleton, forall_eq] using hx
    · simp
    · intro y _ hy
      exact ⟨x, by simp, by simpa using hy⟩
  | succ n ih =>
    obtain ⟨c, hc, hcard, hcov⟩ := h x hx r hr
    have H (z : c) := ih (hc z z.property) (half_pos hr)
    choose d hdK hdcard hdcov using H
    let cs : Finset B := c.attach.biUnion d
    refine ⟨cs, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, _, hzw⟩ := Finset.mem_biUnion.mp hz
      exact hdK w z hzw
    · calc
        cs.card ≤ ∑ z ∈ c.attach, (d z).card := Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ c.attach, L ^ n := Finset.sum_le_sum fun z _ => hdcard z
        _ = c.card * L ^ n := by simp
        _ ≤ L * L ^ n := Nat.mul_le_mul_right _ hcard
        _ = L ^ (n + 1) := (pow_succ' _ _).symm
    · intro y hy hxy
      obtain ⟨z, hz, hyz⟩ := hcov y hy hxy
      obtain ⟨w, hw, hyw⟩ := hdcov ⟨z, hz⟩ y hy hyz
      refine ⟨w, Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, hw⟩, ?_⟩
      simpa only [div_div, pow_succ'] using hyw

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CompactBanach.ambient_iterated_cover := @_root_.OAI.CompactBanach.ambient_iterated_cover
