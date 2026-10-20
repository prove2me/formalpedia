-- Prove2me | solution 1 for OAI.SingleFold.GrowthEstimate.sequence_strict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:14:09.004549+00:00
-- url     : https://prove2.me/submissions/9edbb17d-11a7-4bcc-8bd0-a698923c9a8c

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


theorem solution (hW : ∀ j, 0<W j) (hzero : W 0=1) (hc : 0≤c) (ha : 2*c<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) : StrictMono W := by
  have ha0 : 0 < a := by linarith
  have key : ∀ j : ℕ, Real.log (W j : ℝ) < Real.log (W (j+1) : ℝ) := by
    intro j
    have h2 := abs_le.mp (happrox (j+1) (by omega))
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [hzero]; simp only [Nat.cast_one, Real.log_one]
      push_cast at h2; nlinarith [h2.1]
    · have h1 := abs_le.mp (happrox j hj)
      have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
      push_cast at h2
      nlinarith [h1.2, h2.1]
  apply strictMono_nat_of_lt_succ
  intro j
  have hp := hW j
  have hp' := hW (j+1)
  have := (Real.log_lt_log_iff (by exact_mod_cast hp) (by exact_mod_cast hp')).mp (key j)
  exact_mod_cast this

