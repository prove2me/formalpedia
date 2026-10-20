-- Prove2me | solution 1 for OAI.TalagrandThreshold.finite_tuple_sum_le_inverse_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:06:32.283017+00:00
-- url     : https://prove2.me/submissions/ba89bd63-4cca-4684-968e-d0eb0a40f4fb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/TupleGeometric.lean:L43-L70
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.finite_tuple_sum_le_inverse_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients

-- ---- from OAI.Combinatorics.ExpectationThreshold.TupleGeometric ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

/-!
# A finite geometric bound for nonzero tuples

Every finite family of tuples lies in a finite coordinate box. Factoring
the sum over this box reduces the estimate to ordinary finite geometric
sums. Adding the zero tuple contributes exactly one, so removing it gives
the selector's budget of strictly less than `1 / 20`.
-/

namespace TalagrandThreshold

open scoped BigOperators

private theorem finite_geom_sum_mul_one_sub (c : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, c ^ k) * (1 - c) = 1 - c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

private theorem finite_geom_sum_le_inverse {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, c ^ k) ≤ (1 - c)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hc1)).mpr
  rw [finite_geom_sum_mul_one_sub]
  exact sub_le_self 1 (pow_nonneg hc0 n)

/-- A finite tuple family is bounded by the product of geometric bounds. -/
theorem finite_tuple_sum_le_inverse_product {ι : Type*} [Fintype ι]
    (T : Finset (ι → ℕ)) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ ∏ i, (1 - c i)⁻¹ := by
  classical
  let m : ι → ℕ := fun i => T.sup (fun t => t i) + 1
  let B : Finset (ι → ℕ) := Fintype.piFinset (fun i => Finset.range (m i))
  have hTB : T ⊆ B := by
    intro t ht
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun u => u i) ht)
  calc
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤
        ∑ t ∈ B, ∏ i, (c i) ^ (t i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTB
        (fun t _ _ => Finset.prod_nonneg fun i _ => pow_nonneg (hc0 i) (t i))
    _ = ∏ i, ∑ k ∈ Finset.range (m i), (c i) ^ k :=
      (Finset.prod_univ_sum (fun i => Finset.range (m i))
        (fun i k => (c i) ^ k)).symm
    _ ≤ ∏ i, (1 - c i)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun k _ => pow_nonneg (hc0 i) k
      · intro i _
        exact finite_geom_sum_le_inverse (hc0 i) (hc1 i) (m i)

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.finite_tuple_sum_le_inverse_product := @_root_.OAI.TalagrandThreshold.finite_tuple_sum_le_inverse_product
