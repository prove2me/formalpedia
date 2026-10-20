-- Prove2me | solution 1 for OAI.TalagrandThreshold.productScore_lower_of_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:27:16.874772+00:00
-- url     : https://prove2.me/submissions/928fe037-4229-42a6-851e-567f1c0ac8f8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingLowerBound.lean:L72-L117
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.productScore_lower_of_mean. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_half_mass_of_weighted_average_le

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingMasses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Concrete rounding masses

Each nonempty subset's fractional weight is split equally among its members.
Normalizing by the total nonempty-subset weight gives the probability mass used
by the common selector. Both normalization and the mean identity are finite
double-sum calculations.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- Averaging one set's distributed weight gives its subset average. -/
theorem sum_weighted_uniform_subset_weight (g : Finset α → ℝ)
    (S : Finset α) (a : α → ℝ) :
    (∑ x : α, a x * (if x ∈ S then g S / (S.card : ℝ) else 0)) =
      g S * subsetAverage a S := by
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem_eq, ← Finset.sum_mul]
  unfold subsetAverage
  ring

theorem roundingMass_mean (g : Finset α → ℝ) (H : Finset α) (a : α → ℝ) :
    (∑ x : α, a x * roundingMass g H x) =
      (∑ S ∈ nonemptySubsets H, g S * subsetAverage a S) / memberMass g H := by
  unfold roundingMass
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact sum_weighted_uniform_subset_weight g S a

end
end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingColorProducts ----
namespace OAI

/-!
# Products controlled by the total color level

The numerical color variable is a quotient of powers. This retains its correct
value when a color level exceeds four, without truncated natural subtraction.
Only the total level over the selected finite set enters the product bound.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*}

/-- Separate the fixed numerator from the sum of all color exponents. -/
theorem colorProduct_eq_pow_div_pow (S : Finset α) (a : α → ℕ) :
    (∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) =
      (512 : ℝ) ^ (4 * S.card) / (512 : ℝ) ^ (∑ x ∈ S, a x) := by
  rw [Finset.prod_div_distrib (s := S)
    (fun _ : α => (512 : ℝ) ^ 4) (fun x : α => (512 : ℝ) ^ a x)]
  rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum S a (512 : ℝ), ← pow_mul]

/-- Average color at most four forces the numerical product to be at least one. -/
theorem one_le_colorProduct_of_sum_le (S : Finset α) (a : α → ℕ)
    (hsum : (∑ x ∈ S, a x) ≤ 4 * S.card) :
    1 ≤ ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
  rw [colorProduct_eq_pow_div_pow S a]
  apply (one_le_div (pow_pos (by norm_num : (0 : ℝ) < 512) _)).mpr
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 512) hsum

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingLowerBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The deterministic lower bound for rounding

A weighted average at most two places at least half the mass on subsets with
average at most four. On those subsets the quotient-of-powers product is at
least one, yielding the lower bound one quarter for the full product score.
This statement is pointwise in the coloring and needs no independence premise.
-/

open scoped BigOperators

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem subsetAverage_nat_nonneg (a : α → ℕ) (S : Finset α) :
    0 ≤ subsetAverage (fun x => (a x : ℝ)) S := by
  unfold subsetAverage
  exact div_nonneg (Finset.sum_nonneg (fun x _ => Nat.cast_nonneg (a x)))
    (Nat.cast_nonneg S.card)

omit [Fintype α] [DecidableEq α] in
theorem sum_le_four_card_of_subsetAverage_le (a : α → ℕ) {S : Finset α}
    (hS : S.Nonempty) (haverage : subsetAverage (fun x => (a x : ℝ)) S ≤ 4) :
    (∑ x ∈ S, a x) ≤ 4 * S.card := by
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hreal : (∑ x ∈ S, (a x : ℝ)) ≤ 4 * (S.card : ℝ) :=
    (div_le_iff₀ hcard).mp haverage
  exact_mod_cast hreal

/-- The fractional member mass and its mean color force a product-score lower
bound. Natural colors can include zero; the actual selector uses `val + 1`. -/
theorem productScore_lower_of_mean (g : Finset α → ℝ) (H : Finset α)
    (a : α → ℕ) (hg : ∀ S, 0 ≤ g S) (hMH : (1 / 2 : ℝ) ≤ memberMass g H)
    (hmean : (∑ x : α, (a x : ℝ) * roundingMass g H x) ≤ 2) :
    (1 / 4 : ℝ) ≤ productScore g (fun x => (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) := by
  classical
  have hMpos : 0 < memberMass g H := by linarith
  have hweighted :
      (∑ S ∈ nonemptySubsets H, g S * subsetAverage (fun x => (a x : ℝ)) S) ≤
        2 * memberMass g H := by
    apply (div_le_iff₀ hMpos).mp
    rw [← roundingMass_mean g H (fun x => (a x : ℝ))]
    exact hmean
  let G := (nonemptySubsets H).filter
    (fun S => subsetAverage (fun x => (a x : ℝ)) S ≤ 4)
  have hgood : memberMass g H / 2 ≤ ∑ S ∈ G, g S := by
    simpa only [G, memberMass] using
      half_mass_of_weighted_average_le (nonemptySubsets H) g
        (fun S => subsetAverage (fun x => (a x : ℝ)) S)
        (fun S _ => hg S) (fun S _ => subsetAverage_nat_nonneg a S) hweighted
  have hsub : G ⊆ (Finset.univ.erase ∅ : Finset (Finset α)) := by
    intro S hS
    have hS' : S ∈ nonemptySubsets H := (Finset.mem_filter.mp hS).1
    have hSne : S ≠ ∅ := (mem_nonemptySubsets.mp hS').1
    exact Finset.mem_erase.mpr ⟨hSne, Finset.mem_univ S⟩
  have hproduct (S : Finset α) (hS : S ∈ G) :
      1 ≤ ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
    have hS' := Finset.mem_filter.mp hS
    have hSne : S ≠ ∅ := (mem_nonemptySubsets.mp hS'.1).1
    exact one_le_colorProduct_of_sum_le S a
      (sum_le_four_card_of_subsetAverage_le a
        (Finset.nonempty_iff_ne_empty.mpr hSne) hS'.2)
  have hY (x : α) : 0 ≤ (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x :=
    div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  calc
    (1 / 4 : ℝ) ≤ memberMass g H / 2 := by linarith
    _ ≤ ∑ S ∈ G, g S := hgood
    _ ≤ ∑ S ∈ G, g S * ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
      apply Finset.sum_le_sum
      intro S hS
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hproduct S hS) (hg S)
    _ ≤ productScore g (fun x => (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) := by
      unfold productScore
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun S _ _ => mul_nonneg (hg S) (Finset.prod_nonneg (fun x _ => hY x)))

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.productScore_lower_of_mean := @_root_.OAI.TalagrandThreshold.productScore_lower_of_mean
