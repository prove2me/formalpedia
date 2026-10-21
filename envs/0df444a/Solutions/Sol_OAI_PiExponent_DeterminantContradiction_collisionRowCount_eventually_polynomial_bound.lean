-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collisionRowCount_eventually_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:21:39.815967+00:00
-- url     : https://prove2.me/submissions/30979968-b37b-4123-aed1-5a2e2ddbed3f

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_eventually_at_least_one
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_eventually_polynomial_upper

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open scoped Topology

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ H : ℝ in atTop, 1 ≤ (actualRowCount d H : ℝ)) ∧
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by
  obtain ⟨C, hC, hUpper⟩ :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper d
  exact ⟨C, hC,
    OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_at_least_one d,
    hUpper⟩