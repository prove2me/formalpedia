-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.block_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:13:50.906672+00:00
-- url     : https://prove2.me/submissions/aab7c3af-1719-42f2-8d7b-1c2d56b0aafd

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

theorem cz_block_cover (m : Model) (r : ℕ) (v a : Point) (e : m.Bit) (he : e ∈ block m r v a) :
    match m, e with
    | .bond, e => ((Q r v).Contains e.1 ∨ (Q r a).Contains e.1) ∧
        ((Q r v).Contains (step e.1 e.2) ∨ (Q r a).Contains (step e.1 e.2)) ∧
        ((Q r v).Contains e.1 ∨ (Q r v).Contains (step e.1 e.2))
    | .site, e => (Q r v).Contains e := by
  cases m
  · simp only [block, Finset.mem_union, Box.bits, linkBits, Box.mem_bonds, mem_interface] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1, Or.inl h2, Or.inl h1⟩
    · exact ⟨Or.inl h1, Or.inr h2, Or.inl h1⟩
    · exact ⟨Or.inr h1, Or.inl h2, Or.inr h2⟩
  · simp only [block, Finset.mem_union, Box.bits, linkBits, Box.mem_vertices,
      Finset.notMem_empty, or_false] at he
    exact he

theorem solution (m : Model) (r : ℕ) {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (hw : w ∉ D) (ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block m r v a) (block m r w b) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  have c1 := cz_block_cover m r v a e he1
  have c2 := cz_block_cover m r w b e he2
  cases m
  · obtain ⟨p1, q1, s1⟩ := c1
    obtain ⟨p2, q2, s2⟩ := c2
    have key : ∀ y : Vertex, (Q r v).Contains y → ((Q r w).Contains y ∨ (Q r b).Contains y) → False := by
      intro y hy h
      rcases h with h | h
      · exact hvw (cz_cube_unique r hy h)
      · exact hv (cz_cube_unique r hy h ▸ hb)
    rcases s1 with s | s
    · exact key _ s p2
    · exact key _ s q2
  · exact hvw (cz_cube_unique r c1 c2)

