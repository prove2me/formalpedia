-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.cube_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:13:16.534407+00:00
-- url     : https://prove2.me/submissions/393c685f-6391-4a1a-b52a-2a0741f5ce4a

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

theorem solution (r : ℕ) {v w : Point} {x : Vertex}
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

