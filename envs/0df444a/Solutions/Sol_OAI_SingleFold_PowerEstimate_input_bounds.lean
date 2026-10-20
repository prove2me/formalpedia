-- Prove2me | solution 1 for OAI.SingleFold.PowerEstimate.input_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:15:36.350695+00:00
-- url     : https://prove2.me/submissions/11e54831-a459-4f43-b9af-22ee57fff7f4

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


theorem solution {ell u₀ b n c : ℕ} (hell : 1≤ell) (h₀ : 4≤u₀) :
    u₀ ≤ input ell u₀ b n c ∧ (c+1)*(n+1)+4 ≤ input ell u₀ b n c ∧
    b < input ell u₀ b n c ∧ n+1 < input ell u₀ b n c-1 := by
  unfold input
  have hP : c + 1 ≤ (c+1)^ell := Nat.le_self_pow (by omega) _
  have hA : (c+1)*(n+1) ≤ (c+1)^ell*(n+1)*(b+1) := by
    calc (c+1)*(n+1) = (c+1)*(n+1)*1 := by ring
      _ ≤ (c+1)^ell*(n+1)*(b+1) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hP) (by omega)
  have hB : (b+1) ≤ (c+1)^ell*(n+1)*(b+1) := by
    have : 1 ≤ (c+1)^ell*(n+1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc b+1 = 1*(b+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hC : n+1 ≤ (c+1)*(n+1) := by nlinarith
  refine ⟨by omega, by omega, by omega, by omega⟩

