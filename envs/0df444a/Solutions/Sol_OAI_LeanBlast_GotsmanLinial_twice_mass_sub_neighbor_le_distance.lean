-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:25.847247+00:00
-- url     : https://prove2.me/submissions/3e614612-3a01-4d70-8bf2-f85d40715b7d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean:L37-L59
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery

-- ---- from OAI.Combinatorics.GotsmanLinial.EdgeRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Pointwise distance counting: distance-zero entries are the only possible
source of a deficit between total mass and distance-weighted mass. -/
theorem twice_mass_sub_neighbor_le_distance (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    2 * (∑ a, w a) - (∑ a ∈ distanceShell d 1, w a) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) + ∑ a, (d a : ℝ) * w a := by
  have hpoint : ∀ a,
      2 * w a - (if d a = 1 then w a else 0) ≤
        2 * (if d a = 0 then w a else 0) + (d a : ℝ) * w a := by
    intro a
    by_cases h0 : d a = 0
    · simp [h0]
    by_cases h1 : d a = 1
    · rw [ite_eq_left h1, ite_eq_right h0, h1]
      norm_num
      linarith
    have h2 : 2 ≤ d a := by omega
    have h2R : (2 : ℝ) ≤ (d a : ℝ) := by exact_mod_cast h2
    simpa only [ite_eq_right h0, ite_eq_right h1, sub_zero, mul_zero, zero_add] using
      mul_le_mul_of_nonneg_right h2R (hw a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ => hpoint a
  simpa only [distanceShell, Finset.sum_filter, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum] using hsum

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance := @_root_.OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance
