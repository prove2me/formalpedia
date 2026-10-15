-- Prove2me | solution 1 for OAI.CompactBanach.five_scales
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:33:12.433124+00:00
-- url     : https://prove2.me/submissions/f0d1e6c9-8322-49e3-b1f0-c81f995c67e0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/ClusterScales.lean:L70-L93
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.five_scales. The node keeps its source
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
import Definitions.Def_OAI_Geometry_DoublingHilbert_ClusterScales

-- ---- from OAI.Geometry.DoublingHilbert.ClusterScales ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem clusterScale_add (j n : ℕ) :
    clusterScale (j + n) = clusterScale j * (1 / 2 : ℝ) ^ n := by
  unfold clusterScale
  rw [show j + n + 1 = (j + 1) + n by omega, pow_add]

theorem clusterScale_antitone : Antitone clusterScale := by
  intro i j hij
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.add_le_add_right hij 1)
  exact h

                                            
                                                                               
                                                                           
                                                                             
theorem five_scales {r : ℝ} (hr : 0 < r) (s : Finset ℕ)
    (hlo : ∀ j ∈ s, r / 4 < clusterScale j)
    (hhi : ∀ j ∈ s, clusterScale j ≤ (400 / 97 : ℝ) * r) : s.card ≤ 5 := by
  classical
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    have hi : i ∈ s := s.min'_mem hs
    have hsub : s ⊆ Finset.Icc i (i + 4) := by
      intro j hj
      have hij : i ≤ j := s.min'_le j hj
      have hji : j ≤ i + 4 := by
        by_contra! hj'
        have hd : clusterScale j ≤ clusterScale i / 32 := by
          calc
            clusterScale j ≤ clusterScale (i + 5) := clusterScale_antitone (by omega)
            _ = clusterScale i / 32 := by rw [clusterScale_add]; norm_num; ring
        have h1 := hlo j hj
        have h2 := hhi i hi
        linarith
      exact Finset.mem_Icc.mpr ⟨hij, hji⟩
    calc
      s.card ≤ (Finset.Icc i (i + 4)).card := Finset.card_le_card hsub
      _ = 5 := by simp; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.CompactBanach.five_scales := @_root_.OAI.CompactBanach.five_scales
