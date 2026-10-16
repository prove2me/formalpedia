-- Prove2me | solution 1 for OAI.BoxTransport.Routing.exists_rational_padding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:28:04.511076+00:00
-- url     : https://prove2.me/submissions/dc5492b0-259a-4fa8-8ab0-21aaaaef1ad0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Geometry.lean:L260-L300
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.exists_rational_padding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Theorems.Thm_OAI_BoxTransport_Routing_realBox_disjoint_iff

-- ---- from OAI.Analysis.BoxTransport.Geometry ----
namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem realBox_disjoint_of_gap {c d h k : Space}
    (hgap : ∃ j, h j + k j < |c j - d j|) :
    Disjoint (realBox c h) (realBox d k) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, hj⟩ := hgap
  have hle : |c j - d j| ≤ h j + k j := calc
    |c j - d j| = |(c j - x j) + (x j - d j)| := by congr 1; ring
    _ ≤ |c j - x j| + |x j - d j| := abs_add_le _ _
    _ = |x j - c j| + |x j - d j| := by rw [abs_sub_comm (c j) (x j)]
    _ ≤ h j + k j := add_le_add (hx j) (hy j)
  exact (not_lt_of_ge hle) hj

theorem solidBox_disjoint_iff {a b h k : RationalSpace}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (solidBox a h) (solidBox b k) ↔
      ∃ j, h j + k j < |a j - b j| := by
  have hh' : ∀ j, 0 ≤ realPoint h j := by
    intro j
    change (0 : ℝ) ≤ (h j : ℝ)
    exact_mod_cast hh j
  have hk' : ∀ j, 0 ≤ realPoint k j := by
    intro j
    change (0 : ℝ) ≤ (k j : ℝ)
    exact_mod_cast hk j
  rw [solidBox, solidBox, realBox_disjoint_iff hh' hk']
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (h j : ℝ) + (k j : ℝ) < |(a j : ℝ) - (b j : ℝ)| at hj
    exact_mod_cast hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (h j : ℝ) + (k j : ℝ) < |(a j : ℝ) - (b j : ℝ)|
    exact_mod_cast hj

theorem coordinateGap_pos_iff (a b h k : RationalSpace) :
    0 < coordinateGap a b h k ↔ ∃ j, h j + k j < |a j - b j| := by
  simp only [coordinateGap, Finset.lt_sup'_iff, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨j, hj⟩ <;> exact ⟨j, by linarith⟩

theorem positive_finset_lower_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) :
    (∀ i ∈ s, 0 < f i) → ∃ g : ℚ, 0 < g ∧ ∀ i ∈ s, g ≤ f i := by
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨g, hg, hgf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      refine ⟨min g (f i), lt_min hg (hf i (Finset.mem_insert_self _ _)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hgf j hj)

theorem uniform_rational_gap {n : ℕ} (a h : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j)
    (hdis : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j))) :
    ∃ g : ℚ, 0 < g ∧ ∀ i j, i ≠ j →
      ∃ l, h i l + h j l + g ≤ |a i l - a j l| := by
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)
  have hpos : ∀ p ∈ pairs, 0 < coordinateGap (a p.1) (a p.2) (h p.1) (h p.2) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    apply (coordinateGap_pos_iff _ _ _ _).mpr
    exact (solidBox_disjoint_iff (hh _) (hh _)).mp (hdis hne)
  obtain ⟨g, hg, hbound⟩ := positive_finset_lower_bound pairs
    (fun p => coordinateGap (a p.1) (a p.2) (h p.1) (h p.2)) hpos
  refine ⟨g, hg, ?_⟩
  intro i j hij
  have hb := hbound (i, j) (by simp [pairs, hij])
  obtain ⟨l, hlmem, hl⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp hb
  exact ⟨l, by dsimp at hl; linarith⟩

theorem exists_rational_padding {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j) (hk : ∀ i j, 0 ≤ k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (R : ℚ) (hR : 0 < R) :
    ∃ η : ℚ, 0 < η ∧ η < R / 8 ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
          (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η))) ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
          (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) := by
  obtain ⟨ga, hga, haga⟩ := uniform_rational_gap a h hh ha
  obtain ⟨gb, hgb, hbgb⟩ := uniform_rational_gap b k hk hb
  let m := min R (min ga gb)
  have hm : 0 < m := lt_min hR (lt_min hga hgb)
  let η := m / 16
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hmR : m ≤ R := min_le_left _ _
  have hmga : m ≤ ga := (min_le_right _ _).trans (min_le_left _ _)
  have hmgb : m ≤ gb := (min_le_right _ _).trans (min_le_right _ _)
  have hηR : η < R / 8 := by dsimp [η]; linarith
  have hηa : 4 * η < ga := by dsimp [η]; linarith
  have hηb : 4 * η < gb := by dsimp [η]; linarith
  refine ⟨η, hη0, hηR, ?_, ?_⟩
  · intro i j hij
    obtain ⟨l, hl⟩ := haga i j hij
    apply realBox_disjoint_of_gap
    refine ⟨l, ?_⟩
    have hlt : (h i l + 2 * η) + (h j l + 2 * η) < |a i l - a j l| := by linarith
    change ((h i l : ℝ) + 2 * (η : ℝ)) + ((h j l : ℝ) + 2 * (η : ℝ)) <
      |(a i l : ℝ) - (a j l : ℝ)|
    exact_mod_cast hlt
  · intro i j hij
    obtain ⟨l, hl⟩ := hbgb i j hij
    apply realBox_disjoint_of_gap
    refine ⟨l, ?_⟩
    have hlt : (k i l + 2 * η) + (k j l + 2 * η) < |b i l - b j l| := by linarith
    change ((k i l : ℝ) + 2 * (η : ℝ)) + ((k j l : ℝ) + 2 * (η : ℝ)) <
      |(b i l : ℝ) - (b j l : ℝ)|
    exact_mod_cast hlt

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.exists_rational_padding := @_root_.OAI.BoxTransport.Routing.exists_rational_padding
