-- Prove2me | solution 1 for OAI.SingleFold.PowerEstimate.growth_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:15:21.868316+00:00
-- url     : https://prove2.me/submissions/cc9cccad-5e88-49cf-a798-d5d542e317f3

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
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power

open OAI OAI.SingleFold OAI.SingleFold.PowerEstimate


theorem solution {g : ℕ → ℕ} {δ : ℝ} {u : ℕ} (hδ : 0 < δ) (hu : 4≤u)
    (hg : δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    0<g u ∧ g u<u^u := by
  obtain ⟨h1, h2⟩ := hg
  have hpos : 0 < g u := by
    rcases Nat.eq_zero_or_pos (g u) with h | h
    · exfalso; rw [h] at h1; simp at h1; nlinarith [sq_nonneg (Real.log u)]
    · exact h
  refine ⟨hpos, ?_⟩
  have hu' : (0:ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have : Real.log (g u : ℝ) < Real.log ((u:ℝ)^u) := by rw [Real.log_pow]; exact h2
  have := (Real.log_lt_log_iff (by exact_mod_cast hpos) (by positivity)).1 this
  exact_mod_cast this

