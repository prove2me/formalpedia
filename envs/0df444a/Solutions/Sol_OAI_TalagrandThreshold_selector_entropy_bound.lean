-- Prove2me | solution 1 for OAI.TalagrandThreshold.selector_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:58:13.650993+00:00
-- url     : https://prove2.me/submissions/7dd2752e-e630-41d3-811c-effb36a20810

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorEntropy.lean:L46-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.selector_entropy_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorEntropyDyadic ----
namespace OAI

/-!
# Finite dyadic mass for the selector entropy estimate

The positive dyadic levels have total mass at most one, including when there
are no levels.
-/

open scoped BigOperators

namespace TalagrandThreshold

private lemma selector_dyadic_range_sum (s : ℕ) :
    (∑ i ∈ Finset.range s, (1 / 2 : ℝ) ^ (i + 1)) = 1 - (1 / 2 : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    ring

/-- The dyadic weights of all positive selector levels sum to at most one. -/
theorem selector_dyadic_sum_le_one (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) ≤ 1 := by
  calc
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) =
        ∑ i ∈ Finset.range s, (1 / 2 : ℝ) ^ (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) s
    _ = 1 - (1 / 2 : ℝ) ^ s := selector_dyadic_range_sum s
    _ ≤ 1 := sub_le_self _ (pow_nonneg (by norm_num) s)

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorEntropy ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

/-!
# The selector's finite entropy estimate

After scaling row `i` by `4^(i+1)`, its binomial coefficient is bounded by
one term of the exponential series at `T * 2^(-(i+1))`. The sum of these
arguments is at most `T`, so their product is at most `exp T ≤ 3^T`.
This proves the row-count estimate directly, including rows of count zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- A finite series and its explicit remainder already give the needed slack. -/
private theorem selector_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (n := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact h.trans (by norm_num [Finset.sum_range_succ])

/-- A scaled binomial coefficient is bounded by an exponential-series term. -/
theorem selector_choose_le_scaled_exp (m t : ℕ) (d y : ℝ)
    (hd : 0 ≤ d) (hy : 0 ≤ y) (hm : (m : ℝ) ≤ d * y) :
    (m.choose t : ℝ) ≤ d ^ t * Real.exp y := by
  calc
    (m.choose t : ℝ) ≤ (m : ℝ) ^ t / (t.factorial : ℝ) :=
      Nat.choose_le_pow_div t m
    _ ≤ (d * y) ^ t / (t.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg m) hm t) (Nat.cast_nonneg _)
    _ = d ^ t * (y ^ t / (t.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ d ^ t * Real.exp y :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp y hy t)
        (pow_nonneg hd t)

/-- The actual finite entropy bound for the selector's row sizes and counts.
The statement also permits total count zero. -/
theorem selector_entropy_bound (s : ℕ) (m t : Fin s → ℕ)
    (hm : ∀ i, m i ≤ 2 ^ (i.val + 1) * (∑ j, t j)) :
    (∏ i, ((m i).choose (t i) : ℝ)) ≤
      ∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i) := by
  let T : ℕ := ∑ i, t i
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hrow (i : Fin s) :
      ((m i).choose (t i) : ℝ) ≤
        ((4 : ℝ) ^ (i.val + 1)) ^ (t i) *
          Real.exp ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) := by
    have hbound : (m i : ℝ) ≤ (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by
      have hnat : m i ≤ 2 ^ (i.val + 1) * T := hm i
      exact_mod_cast hnat
    have hscale : (4 : ℝ) ^ (i.val + 1) *
        ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) =
        (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by
      calc
        (4 : ℝ) ^ (i.val + 1) *
            ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) =
            ((4 : ℝ) * (1 / 2 : ℝ)) ^ (i.val + 1) * (T : ℝ) := by
          rw [mul_pow]
          ring
        _ = (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by norm_num
    apply selector_choose_le_scaled_exp
      (m i) (t i) ((4 : ℝ) ^ (i.val + 1))
      ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1))
    · exact pow_nonneg (by norm_num) _
    · exact mul_nonneg hT (pow_nonneg (by norm_num) _)
    · rw [hscale]
      exact hbound
  have hsum : (∑ i : Fin s, (T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) ≤
      (T : ℝ) := by
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right hT (selector_dyadic_sum_le_one s)
  have hexp : Real.exp (T : ℝ) ≤ (3 : ℝ) ^ T := by
    calc
      Real.exp (T : ℝ) = Real.exp 1 ^ T := by
        simpa only [mul_one] using Real.exp_nat_mul 1 T
      _ ≤ (3 : ℝ) ^ T :=
        pow_le_pow_left₀ (Real.exp_pos 1).le selector_exp_one_le_three T
  have hprod : (0 : ℝ) ≤ ∏ i : Fin s, ((4 : ℝ) ^ (i.val + 1)) ^ (t i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (pow_nonneg (by norm_num) _) _)
  have hfactor : (∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i)) =
      (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * (3 : ℝ) ^ T := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact mul_comm _ _
  calc
    (∏ i, ((m i).choose (t i) : ℝ)) ≤
        ∏ i, (((4 : ℝ) ^ (i.val + 1)) ^ (t i) *
          Real.exp ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1))) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hrow i)
    _ = (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) *
        Real.exp (∑ i : Fin s, (T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    _ ≤ (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * Real.exp (T : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hsum) hprod
    _ ≤ (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * (3 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_left hexp hprod
    _ = ∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i) := hfactor.symm

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.selector_entropy_bound := @_root_.OAI.TalagrandThreshold.selector_entropy_bound
