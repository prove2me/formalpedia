-- Prove2me | solution 2 for OAI.PlanarBoundary.coordinate_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:22:28.642104+00:00
-- url     : https://prove2.me/submissions/8737d88f-2e29-4311-a1c3-90e9efd660c7

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean:L235-L260
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.coordinate_diameter. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
end PlanarBoundary

namespace PlanarBoundary
open Classical

theorem neighbor_coord {a b : Point} (h : Neighbor a b) : |b.1-a.1| ≤ 1 := by
  obtain ⟨d,rfl⟩ := h
  fin_cases d <;> simp [outward]

/-- A coarse diameter bound adequate for the same Peierls argument. -/
theorem coordinate_diameter {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by
  let a : ℕ → ℤ := fun k => (v ⟨k%n,Nat.mod_lt _ hn⟩).1
  have hs (k : ℕ) : |a (k+1)-a k| ≤ 1 := by
    have he : FiniteTrails.next hn ⟨k%n,Nat.mod_lt _ hn⟩ =
        (⟨(k+1)%n,Nat.mod_lt _ hn⟩ : Fin n) := by
      ext
      exact Nat.mod_add_mod k n 1
    simpa only [he] using neighbor_coord (hedge ⟨k%n,Nat.mod_lt _ hn⟩)
  have hb (k : ℕ) : |a k-a 0| ≤ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        |a (k+1)-a 0| ≤ |a (k+1)-a k|+|a k-a 0| := abs_sub_le _ _ _
        _ ≤ 1+(k : ℤ) := add_le_add (hs k) ih
        _ = (k+1 : ℕ) := by omega
  have hi := (abs_le.mp (hb i.val)).2
  have hj := (abs_le.mp (hb j.val)).1
  dsimp [a] at hi hj
  simp only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt,Fin.eta] at hi hj
  have hin : (i.val : ℤ) < n := by exact_mod_cast i.isLt
  have hjn : (j.val : ℤ) < n := by exact_mod_cast j.isLt
  omega

end PlanarBoundary

namespace PlanarBoundary
open Classical

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical


theorem solution : type_of% @_root_.OAI.PlanarBoundary.coordinate_diameter := @_root_.OAI.PlanarBoundary.coordinate_diameter
