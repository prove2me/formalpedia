-- Prove2me | solution 1 for OAI.TalagrandThreshold.expectation_productScore_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:25:37.344595+00:00
-- url     : https://prove2.me/submissions/61185bd6-9be5-4765-acd2-76597848fa3b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean:L67-L99
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.expectation_productScore_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_expectation_productScore

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityFinite ----
namespace OAI

/-!
# Finite probability laws

Probabilities and expectations are finite real sums. Independent samples,
product laws, and uniform laws satisfy the usual elementary inequalities.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expectation f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

end FiniteLaw

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingExpectation ----
namespace OAI

/-!
# The upper expectation bound for rounding

The score sums over nonempty subsets of the original ground set. Its moments
come from the actual coordinate product law. Nonemptiness saves a factor of
one fifth in the fractional-cover cost.
-/

open scoped BigOperators

namespace TalagrandThreshold

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {Ω : Type*} [Fintype Ω]

/-- A nonempty product gains at least one factor of one fifth. -/
theorem one_fifth_pow_le {r : ℝ} (hr : 0 ≤ r) {k : ℕ} (hk : 0 < k) :
    (r / 5) ^ k ≤ (1 / 5) * r ^ k := by
  have hsmall : (1 / 5 : ℝ) ^ k ≤ 1 / 5 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (Nat.ne_of_gt hk)
  calc
    (r / 5) ^ k = (1 / 5 : ℝ) ^ k * r ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (1 / 5) * r ^ k := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hr k)

/-- The product score costs at most one fifth of the fractional-cover cost. -/
theorem expectation_productScore_le (ν : FiniteLaw Ω) (g : Finset α → ℝ)
    (Y : Ω → ℝ) {r : ℝ} (hg : ∀ S, 0 ≤ g S) (hY : ∀ ω, 0 ≤ Y ω)
    (hr : 0 ≤ r) (hmean : ν.expectation Y ≤ r / 5) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) ≤
      (1 / 5) * fracCost r g := by
  classical
  have hmean0 := ν.expectation_nonneg hY
  rw [expectation_productScore]
  calc
    (∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * (ν.expectation Y) ^ S.card) ≤
        ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
          (1 / 5) * (g S * r ^ S.card) := by
      apply Finset.sum_le_sum
      intro S hS
      have hne : S.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      have hpower : (ν.expectation Y) ^ S.card ≤ (1 / 5) * r ^ S.card :=
        (pow_le_pow_left₀ hmean0 hmean S.card).trans
          (one_fifth_pow_le hr (Finset.card_pos.mpr hne))
      calc
        g S * (ν.expectation Y) ^ S.card ≤ g S * ((1 / 5) * r ^ S.card) :=
          mul_le_mul_of_nonneg_left hpower (hg S)
        _ = (1 / 5) * (g S * r ^ S.card) := by ring
    _ = (1 / 5) * ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * r ^ S.card := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 5) * fracCost r g := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 5)
      unfold fracCost
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun S _ _ => mul_nonneg (hg S) (pow_nonneg hr S.card))

end
end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.expectation_productScore_le := @_root_.OAI.TalagrandThreshold.expectation_productScore_le
