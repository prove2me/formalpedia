-- Prove2me | solution 1 for OAI.PlanarBoundary.coordinate_diameter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:18:46.841924+00:00
-- url     : https://prove2.me/submissions/667814ba-a48e-4066-bac8-cfa672a55a02

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

open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical
theorem pl_outward_fst_le (d : Direction) : (outward d).1 ≤ 1 := by
  fin_cases d <;> simp [outward]

theorem solution {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by
  have key : ∀ k : ℕ, (v ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩).1 - (v j).1 ≤ k := by
    intro k
    induction k with
    | zero => simp [Nat.mod_eq_of_lt j.isLt]
    | succ k ih =>
      obtain ⟨d, hd⟩ := hedge ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩
      have hnx : FiniteTrails.next hn ⟨(j.val + k) % n, Nat.mod_lt _ hn⟩ = ⟨(j.val + (k+1)) % n, Nat.mod_lt _ hn⟩ := by
        apply Fin.ext
        simp only [FiniteTrails.next]
        rw [Nat.mod_add_mod, ← add_assoc]
      rw [hnx] at hd
      rw [hd, Prod.fst_add]
      have := pl_outward_fst_le d
      push_cast
      linarith
  have hk := key (i.val + n - j.val)
  have hi : (⟨(j.val + (i.val + n - j.val)) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
    apply Fin.ext
    simp only
    have : j.val + (i.val + n - j.val) = i.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  rw [hi] at hk
  have h1 : ((i.val + n - j.val : ℕ) : ℤ) < 2 * (n : ℤ) := by
    have := i.isLt; have := j.isLt
    omega
  linarith

