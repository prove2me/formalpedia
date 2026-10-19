-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.internal_pair_not_exposed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:12:15.453969+00:00
-- url     : https://prove2.me/submissions/cf5d5d90-4232-4c62-a6a9-d4e80edf5591

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
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
theorem cz_coord_unique (r : ℕ) {a b x : ℤ} (ha : |x - (20*(r:ℤ)+1)*a| ≤ 10*r)
    (hb : |x - (20*(r:ℤ)+1)*b| ≤ 10*r) : a = b := by
  by_contra hne
  have h1 : 1 ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hne)
  have h2 : |(20*(r:ℤ)+1)*(a - b)| ≤ 20*r := by
    have : (20*(r:ℤ)+1)*(a - b) = (x - (20*(r:ℤ)+1)*b) - (x - (20*(r:ℤ)+1)*a) := by ring
    rw [this]
    have := abs_sub (x - (20*(r:ℤ)+1)*b) (x - (20*(r:ℤ)+1)*a)
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0:ℤ) < 20*r+1)] at h2
  nlinarith

theorem cz_cube_unique (r : ℕ) {v w : Point} {x : Vertex}
    (hv : (Q r v).Contains x) (hw : (Q r w).Contains x) : v = w := by
  rw [Q, Box.contains_cube] at hv hw
  have h0v := hv 0
  have h0w := hw 0
  have h1v := hv 1
  have h1w := hw 1
  simp only [center, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0v h0w h1v h1w
  push_cast at h0v h0w h1v h1w
  have e1 := cz_coord_unique r (by linarith [h0v] : |x 0 - (20*(r:ℤ)+1)*v.1| ≤ 10*r) (by linarith [h0w])
  have e2 := cz_coord_unique r (by linarith [h1v] : |x 1 - (20*(r:ℤ)+1)*v.2| ≤ 10*r) (by linarith [h1w])
  exact Prod.ext e1 e2

theorem solution (m : Model) (r : ℕ) {D : Finset Point}
    (h0 : 0 ∈ D) {v w : Point} (hv : v ∉ D) (hw : w ∉ D) {e : m.Bit}
    (he : m.Internal (PairRegion r v w) e) : e ∉ exposed m r D := by
  intro hex
  have key : ∀ u ∈ D, ∀ y : Vertex, (Q r u).Contains y → y ∈ PairRegion r v w → False := by
    intro u hu y hy hyP
    rcases hyP with h | h
    · exact hv (cz_cube_unique r hy h ▸ hu)
    · exact hw (cz_cube_unique r hy h ▸ hu)
  simp only [exposed, rootBits, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_product] at hex
  cases m
  · obtain ⟨h1, h2⟩ := he
    rcases hex with ((hq | ⟨d, hd⟩) | ⟨u, hu, hq⟩) | ⟨⟨a, b⟩, ⟨ha, hb⟩, hl⟩
    · simp only [Box.bits, Box.mem_bonds] at hq; exact key 0 h0 _ hq.1 h1
    · simp only [linkBits, mem_interface] at hd
      rcases hd with ⟨hd1, _⟩ | ⟨_, hd2⟩
      · exact key 0 h0 _ hd1 h1
      · exact key 0 h0 _ hd2 h2
    · simp only [Box.bits, Box.mem_bonds] at hq; exact key u hu _ hq.1 h1
    · simp only [linkBits, mem_interface] at hl
      rcases hl with ⟨hl1, _⟩ | ⟨_, hl2⟩
      · exact key a ha _ hl1 h1
      · exact key a ha _ hl2 h2
  · rcases hex with ((hq | ⟨d, hd⟩) | ⟨u, hu, hq⟩) | ⟨⟨a, b⟩, ⟨ha, hb⟩, hl⟩
    · simp only [Box.bits, Box.mem_vertices] at hq; exact key 0 h0 _ hq he
    · simp [linkBits] at hd
    · simp only [Box.bits, Box.mem_vertices] at hq; exact key u hu _ hq he
    · simp [linkBits] at hl

