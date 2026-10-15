-- Prove2me | solution 1 for OAI.CompactBanach.ambient_doubling_clusters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:34:52.76327+00:00
-- url     : https://prove2.me/submissions/cfc72fef-4d58-4191-87c7-58df273fe20c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/ClusterCover.lean:L15-L107
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.ambient_doubling_clusters. The node keeps its source
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
import Theorems.Thm_OAI_CompactBanach_ambient_iterated_cover
import Theorems.Thm_OAI_CompactBanach_five_scales

-- ---- from OAI.Geometry.DoublingHilbert.ClusterScales ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem clusterScale_pos (j : ℕ) : 0 < clusterScale j := by
  unfold clusterScale
  positivity

theorem clusterScale_add (j n : ℕ) :
    clusterScale (j + n) = clusterScale j * (1 / 2 : ℝ) ^ n := by
  unfold clusterScale
  rw [show j + n + 1 = (j + 1) + n by omega, pow_add]

theorem clusterScale_antitone : Antitone clusterScale := by
  intro i j hij
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.add_le_add_right hij 1)
  exact h

theorem clusterScale_half {i j : ℕ} (hij : i < j) :
    clusterScale j ≤ clusterScale i / 2 := by
  calc
    clusterScale j ≤ clusterScale (i + 1) := clusterScale_antitone (by omega)
    _ = clusterScale i / 2 := by rw [clusterScale_add]; norm_num; ring

theorem clusterScale_tendsto : Tendsto clusterScale atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact h.comp (tendsto_add_atTop_nat 1)

                                            
theorem cluster_norm_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {v z : B} (hv : ‖v‖ = 1) {j : ℕ}
    (hz : dist z (clusterScale j • v) ≤ clusterScale j / 100) :
    ‖z‖ ≤ (101 / 100 : ℝ) * clusterScale j := by
  have hcent : dist (clusterScale j • v) 0 = clusterScale j := by
    simp [dist_zero_right, norm_smul, hv, Real.norm_eq_abs, abs_of_pos (clusterScale_pos j)]
  have ht := dist_triangle z (clusterScale j • v) 0
  rw [dist_zero_right, hcent] at ht
  linarith

                                                                               
theorem cluster_separation {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {v p q : B} (hv : ‖v‖ = 1) {i j : ℕ} (hij : i < j)
    (hp : dist p (clusterScale i • v) ≤ clusterScale i / 100)
    (hq : dist q (clusterScale j • v) ≤ clusterScale j / 100) :
    (97 / 200 : ℝ) * clusterScale i ≤ dist p q := by
  have ha := clusterScale_half hij
  have hi := clusterScale_pos i
  have hj := clusterScale_pos j
  have hcent : dist (clusterScale i • v) (clusterScale j • v) =
      clusterScale i - clusterScale j := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have ht := dist_triangle4 (clusterScale i • v) p q (clusterScale j • v)
  rw [hcent, dist_comm (clusterScale i • v) p] at ht
  linarith

                                                                           
                                                                             
end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.ClusterCover ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem ambient_doubling_clusters
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (C : ℕ → Finset B) {v : B} (hv : ‖v‖ = 1)
    (hloc : ∀ j z, z ∈ C j → dist z (clusterScale j • v) ≤ clusterScale j / 100)
    {L : ℕ} (hC : ∀ j, AmbientDoubling (C j : Set B) L) :
    AmbientDoubling ({0} ∪ ⋃ j : ℕ, (C j : Set B)) (1 + 5 * L ^ 2) := by
  classical
  intro x _ r hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (clusterScale_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < r / 4 by positivity)))
  let I : Finset ℕ := (Finset.range N).filter fun j =>
    r / 4 < clusterScale j ∧ ∃ z ∈ C j, dist z x < r
  have hImem {j : ℕ} (hj : j ∈ I) :
      r / 4 < clusterScale j ∧ ∃ z ∈ C j, dist z x < r :=
    (Finset.mem_filter.mp hj).2
  have hIcard : I.card ≤ 5 := by
    by_cases hsmall : I.card ≤ 1
    · omega
    · have hbig : 1 < I.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
      have hne : I.Nonempty := ⟨a, ha⟩
      let i := I.min' hne
      have hi : i ∈ I := I.min'_mem hne
      have hex : ∃ j ∈ I, i < j := by
        by_cases hai : a = i
        · refine ⟨b, hb, ?_⟩
          have hle : i ≤ b := I.min'_le b hb
          omega
        · refine ⟨a, ha, ?_⟩
          have hle : i ≤ a := I.min'_le a ha
          omega
      obtain ⟨j, hj, hij⟩ := hex
      obtain ⟨p, hp, hpx⟩ := (hImem hi).2
      obtain ⟨q, hq, hqx⟩ := (hImem hj).2
      have hs := cluster_separation hv hij (hloc i p hp) (hloc j q hq)
      have ht := dist_triangle p x q
      rw [dist_comm x q] at ht
      have hi_bound : clusterScale i ≤ (400 / 97 : ℝ) * r := by linarith
      apply five_scales hr I (fun k hk => (hImem hk).1)
      intro k hk
      exact (clusterScale_antitone (I.min'_le k hk)).trans hi_bound
  have hcover (j : I) : ∃ d : Finset B,
      (∀ z ∈ d, z ∈ C j.val) ∧ d.card ≤ L ^ 2 ∧
        ∀ z ∈ C j.val, dist z x < r → ∃ w ∈ d, dist z w < r / 2 := by
    obtain ⟨y, hy, hyx⟩ := (hImem j.property).2
    obtain ⟨d, hd, hcard, hcov⟩ :=
      ambient_iterated_cover (hC j.val) 2 hy (show 0 < 2 * r by positivity)
    refine ⟨d, hd, hcard, ?_⟩
    intro z hz hzx
    have hzy : dist z y < 2 * r := by
      have h := dist_triangle z x y
      rw [dist_comm x y] at h
      linarith
    obtain ⟨w, hw, hzw⟩ := hcov z hz hzy
    norm_num at hzw
    exact ⟨w, hw, by linarith⟩
  choose d hdK hdcard hdcov using hcover
  let centers : Finset B := insert 0 (I.attach.biUnion d)
  have hzero : (0 : B) ∈ centers := Finset.mem_insert_self _ _
  refine ⟨centers, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Or.inl (by simp)
    · obtain ⟨j, _, hzj⟩ := Finset.mem_biUnion.mp hz
      exact Or.inr (mem_iUnion.mpr ⟨j.val, hdK j z hzj⟩)
  · calc
      centers.card ≤ (I.attach.biUnion d).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ j ∈ I.attach, (d j).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ (∑ _j ∈ I.attach, L ^ 2) + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum fun j _ => hdcard j) _
      _ = I.card * L ^ 2 + 1 := by simp
      _ ≤ 5 * L ^ 2 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hIcard) _
      _ = 1 + 5 * L ^ 2 := by omega
  · intro z hz hzx
    rcases hz with hz | hz
    · have hz0 := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨0, hzero, by simpa using half_pos hr⟩
    · obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
      by_cases hj : clusterScale j ≤ r / 4
      · refine ⟨0, hzero, ?_⟩
        rw [dist_zero_right]
        have hn := cluster_norm_bound hv (hloc j z hzj)
        linarith
      · have hjN : j < N := by
          by_contra! hn
          have h := hN j hn
          linarith
        have hjI : j ∈ I := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hjN, lt_of_not_ge hj, z, hzj, hzx⟩
        obtain ⟨w, hw, hzw⟩ := hdcov ⟨j, hjI⟩ z hzj hzx
        exact ⟨w, Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨⟨j, hjI⟩, Finset.mem_attach _ _, hw⟩), hzw⟩

                                                                            
                                                                          
                                                                                
end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.CompactBanach.ambient_doubling_clusters := @_root_.OAI.CompactBanach.ambient_doubling_clusters
