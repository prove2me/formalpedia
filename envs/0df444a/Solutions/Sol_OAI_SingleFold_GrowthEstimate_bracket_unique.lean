-- Prove2me | solution 1 for OAI.SingleFold.GrowthEstimate.bracket_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:09:07.901766+00:00
-- url     : https://prove2.me/submissions/553fdd9a-1a3b-496e-8bec-8d3e4b1e073a

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

open OAI OAI.SingleFold
open Filter
open scoped Topology
variable {W : ℕ → ℕ} {a c : ℝ}


theorem solution (hW : StrictMono W) (hunb : ∀ U, ∃ j, U<W j) (u : ℕ) :
    ∃! k : ℕ, 1≤k ∧ W k≤u+W 1 ∧ u+W 1<W (k+1) := by
  classical
  have hex : ∃ j, u + W 1 < W j := hunb _
  let j := Nat.find hex
  have hj : u + W 1 < W j := Nat.find_spec hex
  have hmin : ∀ i < j, ¬ u + W 1 < W i := fun i hi => Nat.find_min hex hi
  have hj2 : 2 ≤ j := by
    by_contra hc
    push_neg at hc
    interval_cases hjj : j
    · have := hW (show 0 < 1 by norm_num); omega
    · omega
  refine ⟨j - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · have := hmin (j-1) (by omega); omega
  · rwa [show j - 1 + 1 = j by omega]
  · rintro k ⟨hk1, hk2, hk3⟩
    have a1 : k + 1 ≥ j := by
      by_contra hc; push_neg at hc
      exact hmin (k+1) hc hk3
    have a2 : k < j := by
      by_contra hc; push_neg at hc
      have := hW.monotone hc; omega
    omega

