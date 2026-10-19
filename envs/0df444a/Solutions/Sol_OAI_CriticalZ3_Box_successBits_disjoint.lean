-- Prove2me | solution 1 for OAI.CriticalZ3.Box.successBits_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:54:16.769506+00:00
-- url     : https://prove2.me/submissions/827bbe4f-b6b0-4882-89ea-125dd49c05d6

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
theorem cz_nn_close {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) : |x i - y i| ≤ 1 := by
  obtain ⟨j, h | h⟩ := h <;> subst h <;> simp only [step] <;> split_ifs <;> simp

theorem cz_entry (C : Box) {y : Vertex} (hy : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  unfold Box.entry; rw [dif_pos hy]; exact hy.2.choose_spec

theorem cz_seed_close (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex}
    (hy : C.Exterior y) {v : Vertex} (hv : (C.seedBox r y).Contains v) (i : Fin 3) :
    |v i - y i| ≤ 2*r+1 := by
  obtain ⟨hc, hnn⟩ := cz_entry C hy
  have h1 := cz_nn_close hnn i
  have h2 := hc i
  have h3 := hw i
  unfold Box.seedBox at hv
  rw [contains_cube] at hv
  have h4 := hv i
  unfold Box.relayCenter Box.seedCenter at h4
  rw [abs_le] at h1 h4 ⊢
  rcases le_total (C.upper i - r) (C.entry y i) with h5 | h5
  · rw [min_eq_left h5] at h4
    rcases le_total (C.lower i + r) (C.upper i - r) with h6 | h6
    · rw [max_eq_right h6] at h4; constructor <;> linarith [h4.1, h4.2, h1.1, h1.2]
    · rw [max_eq_left h6] at h4; constructor <;> linarith [h4.1, h4.2, h1.1, h1.2]
  · rw [min_eq_right h5] at h4
    rcases le_total (C.lower i + r) (C.entry y i) with h6 | h6
    · rw [max_eq_right h6] at h4; constructor <;> linarith [h4.1, h4.2, h1.1, h1.2]
    · rw [max_eq_left h6] at h4; constructor <;> linarith [h4.1, h4.2, h1.1, h1.2, h2.1, h2.2]

def czAnchor : (m : Model) → m.Bit → Vertex
  | .bond, e => e.1
  | .site, e => e

theorem cz_bit_close (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (m : Model)
    {y : Vertex} (hy : C.Exterior y) (e : m.Bit) (he : e ∈ C.successBits r m y) (i : Fin 3) :
    |czAnchor m e i - y i| ≤ 2*r+1 := by
  cases m
  · simp only [Box.successBits, Finset.mem_insert] at he
    simp only [czAnchor]
    rcases he with he | he
    · obtain ⟨hc, hnn⟩ := cz_entry C hy
      have hinc : Incidence (neighborBond y (C.entry y)) y (C.entry y) := by
        unfold neighborBond; rw [dif_pos hnn]; exact (LatticeGraph.neighbor_incidence hnn).choose_spec
      simp only [Box.entryBit] at he
      rw [he]
      have := cz_nn_close hnn i
      rw [abs_sub_comm] at this
      rcases hinc with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [← h1]; simp; positivity
      · rw [← h1]; linarith
    · rw [Box.mem_bonds] at he
      exact cz_seed_close C r hw hy he.1 i
  · simp only [Box.successBits, Box.mem_vertices] at he
    exact cz_seed_close C r hw hy he i

theorem solution (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y z : Vertex}
    (hy : C.Exterior y) (hz : C.Exterior z) (hsep : ∃ i, (4*r+2 : ℤ) < |y i-z i|) :
    Disjoint (C.successBits r m y) (C.successBits r m z) := by
  obtain ⟨i, hi⟩ := hsep
  rw [Finset.disjoint_left]
  intro e hey hez
  have h1 := cz_bit_close C r hw m hy e hey i
  have h2 := cz_bit_close C r hw m hz e hez i
  have : |y i - z i| ≤ |czAnchor m e i - y i| + |czAnchor m e i - z i| := by
    rw [abs_sub_comm (czAnchor m e i) (y i)]
    exact abs_sub_le _ _ _
  linarith

