-- Prove2me | solution 1 for OAI.TalagrandThreshold.tuple_geometric_sum_lt_one_twentieth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:07:17.110929+00:00
-- url     : https://prove2.me/submissions/f8e7f5bd-f967-400d-b6bb-7fba6caf3c88

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/TupleGeometric.lean:L86-L109
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.tuple_geometric_sum_lt_one_twentieth. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_finite_tuple_sum_le_inverse_product
import Theorems.Thm_OAI_TalagrandThreshold_one_sub_sum_le_prod_one_sub

-- ---- from OAI.Combinatorics.ExpectationThreshold.TupleCoefficients ----
namespace OAI

/-!
# Coefficients for the finite tuple estimate

Replacing `e` by `3` gives the coefficients `3 / 64^(i+1)`. Their finite
sum has an explicit positive remainder below `1 / 21`. A finite product
inequality then bounds the product of their complements from below.
-/

namespace TalagrandThreshold

open scoped BigOperators

theorem tupleCoefficient_eq (i : ℕ) :
    tupleCoefficient i = (3 / 64 : ℝ) * (1 / 64 : ℝ) ^ i := by
  simp only [tupleCoefficient, pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul,
    inv_pow]
  ring

theorem tupleCoefficient_pos (i : ℕ) : 0 < tupleCoefficient i := by
  unfold tupleCoefficient
  positivity

theorem tupleCoefficient_nonneg (i : ℕ) : 0 ≤ tupleCoefficient i :=
  (tupleCoefficient_pos i).le

theorem tupleCoefficient_le_first (i : ℕ) : tupleCoefficient i ≤ 3 / 64 := by
  rw [tupleCoefficient_eq]
  have hpow : (1 / 64 : ℝ) ^ i ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem tupleCoefficient_lt_one (i : ℕ) : tupleCoefficient i < 1 :=
  lt_of_le_of_lt (tupleCoefficient_le_first i) (by norm_num)

/-- The exact finite geometric identity, including the empty sum. -/
theorem sum_tupleCoefficient_add_remainder (s : ℕ) :
    (∑ i : Fin s, tupleCoefficient i.val) +
      (1 / 21 : ℝ) * (1 / 64 : ℝ) ^ s = 1 / 21 := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [tupleCoefficient_eq s, pow_succ]
    nlinarith [ih]

theorem sum_tupleCoefficient_lt (s : ℕ) :
    (∑ i : Fin s, tupleCoefficient i.val) < 1 / 21 := by
  have hrem : 0 < (1 / 21 : ℝ) * (1 / 64 : ℝ) ^ s := by positivity
  linarith [sum_tupleCoefficient_add_remainder s]

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.TupleGeometric ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
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

/-- The sum of coefficients controls every finite tuple family. -/
theorem finite_tuple_sum_le_inverse_one_sub_sum {ι : Type*} [Fintype ι]
    (T : Finset (ι → ℕ)) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1)
    (hsum : (∑ i, c i) < 1) :
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ (1 - ∑ i, c i)⁻¹ := by
  calc
    (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ ∏ i, (1 - c i)⁻¹ :=
      finite_tuple_sum_le_inverse_product T c hc0 hc1
    _ = (∏ i, (1 - c i))⁻¹ := Finset.prod_inv_distrib _
    _ ≤ (1 - ∑ i, c i)⁻¹ :=
      inv_anti₀ (sub_pos.mpr hsum)
        (one_sub_sum_le_prod_one_sub c hc0 (fun i => (hc1 i).le))

/-- The actual selector coefficients give a strict budget for every finite
family of nonzero tuples, without an infinite-series argument. -/
theorem tuple_geometric_sum_lt_one_twentieth {s : ℕ}
    (T : Finset (Fin s → ℕ)) (hT : ∀ t ∈ T, t ≠ 0) :
    (∑ t ∈ T, ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)) < 1 / 20 := by
  classical
  let c : Fin s → ℝ := fun i => tupleCoefficient i.val
  have hc0 : ∀ i, 0 ≤ c i := fun i => tupleCoefficient_nonneg i.val
  have hc1 : ∀ i, c i < 1 := fun i => tupleCoefficient_lt_one i.val
  have hrho : (∑ i, c i) < (1 / 21 : ℝ) := sum_tupleCoefficient_lt s
  have hsum : (∑ i, c i) < 1 := hrho.trans (by norm_num)
  have hz : (0 : Fin s → ℕ) ∉ T := fun hz => hT 0 hz rfl
  have hall := finite_tuple_sum_le_inverse_one_sub_sum (insert 0 T) c hc0 hc1 hsum
  have htotal : 1 + (∑ t ∈ T, ∏ i, (c i) ^ (t i)) ≤ (1 - ∑ i, c i)⁻¹ := by
    simpa only [Finset.sum_insert hz, Pi.zero_apply, pow_zero, Finset.prod_const_one]
      using hall
  have hden : (20 / 21 : ℝ) < 1 - ∑ i, c i := by linarith
  have hinv : (1 - ∑ i, c i)⁻¹ < (21 / 20 : ℝ) := by
    have h := (inv_lt_inv₀ (sub_pos.mpr hsum)
      (by norm_num : (0 : ℝ) < 20 / 21)).mpr hden
    norm_num at h
    exact h
  change (∑ t ∈ T, ∏ i, (c i) ^ (t i)) < 1 / 20
  linarith

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.tuple_geometric_sum_lt_one_twentieth := @_root_.OAI.TalagrandThreshold.tuple_geometric_sum_lt_one_twentieth
