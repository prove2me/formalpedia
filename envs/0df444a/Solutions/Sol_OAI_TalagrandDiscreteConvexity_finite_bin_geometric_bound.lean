-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:21:31.610994+00:00
-- url     : https://prove2.me/submissions/3a76877d-bf00-4027-999f-cadf7c266936

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean:L68-L98
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers

-- ---- from OAI.Combinatorics.DiscreteConvexity.BinNumerics ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

private theorem half_range_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) + 2 * (1 / 2 : ℝ) ^ n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

private theorem finite_half_sum_le_two (s : Finset ℕ) :
    (∑ i ∈ s, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hle : (∑ i ∈ s, (1 / 2 : ℝ) ^ i) ≤
      ∑ i ∈ Finset.range (s.sup id + 1), (1 / 2 : ℝ) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hnot
      positivity)
  have hgeom := half_range_sum (s.sup id + 1)
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (s.sup id + 1) := by positivity
  linarith

private theorem finite_small_base_sum_le_two (s : Finset ℕ) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) : (∑ i ∈ s, a ^ i) ≤ 2 := by
  calc
    (∑ i ∈ s, a ^ i) ≤ ∑ i ∈ s, (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ ha ha' i)
    _ ≤ 2 := finite_half_sum_le_two s

private theorem finite_quadrant_sum_le_four (T : Finset (ℕ × ℕ)) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∑ c ∈ T, a ^ c.1 * a ^ c.2) ≤ 4 := by
  have hsub : T ⊆ (T.image Prod.fst) ×ˢ (T.image Prod.snd) := by
    intro c hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩
  calc
    (∑ c ∈ T, a ^ c.1 * a ^ c.2) ≤
        ∑ c ∈ (T.image Prod.fst) ×ˢ (T.image Prod.snd), a ^ c.1 * a ^ c.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro c hc hnot
        exact mul_nonneg (pow_nonneg ha _) (pow_nonneg ha _))
    _ = (∑ i ∈ T.image Prod.fst, a ^ i) * (∑ j ∈ T.image Prod.snd, a ^ j) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ 2 * 2 :=
      mul_le_mul (finite_small_base_sum_le_two _ ha ha')
        (finite_small_base_sum_le_two _ ha ha')
        (Finset.sum_nonneg fun _ _ => pow_nonneg ha _) (by norm_num)
    _ = 4 := by norm_num

/-- A finite occupied-bin estimate, with no infinite-series premise. -/
theorem finite_bin_geometric_bound (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∑ b ∈ B, a ^ b.2) ≤ 4 * a ^ 64 := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun b => (b.1 - 1, b.2 - b.1 - 63)
  have hinj : Set.InjOn shift B := by
    intro b hb c hc heq
    have hb' := hB b hb
    have hc' := hB c hc
    have heq₁ : b.1 - 1 = c.1 - 1 := congrArg Prod.fst heq
    have heq₂ : b.2 - b.1 - 63 = c.2 - c.1 - 63 := congrArg Prod.snd heq
    apply Prod.ext <;> omega
  have heq : (∑ b ∈ B, a ^ b.2) =
      a ^ 64 * ∑ c ∈ B.image shift, a ^ c.1 * a ^ c.2 := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' := hB b hb
    have hexp : b.2 = 64 + (b.1 - 1) + (b.2 - b.1 - 63) := by omega
    change a ^ b.2 = a ^ 64 * (a ^ (b.1 - 1) * a ^ (b.2 - b.1 - 63))
    calc
      a ^ b.2 = a ^ (64 + (b.1 - 1) + (b.2 - b.1 - 63)) := congrArg (a ^ ·) hexp
      _ = a ^ 64 * (a ^ (b.1 - 1) * a ^ (b.2 - b.1 - 63)) := by
        simp only [pow_add, mul_assoc]
  rw [heq]
  calc
    a ^ 64 * (∑ c ∈ B.image shift, a ^ c.1 * a ^ c.2) ≤ a ^ 64 * 4 :=
      mul_le_mul_of_nonneg_left (finite_quadrant_sum_le_four _ ha ha')
        (pow_nonneg ha _)
    _ = 4 * a ^ 64 := mul_comm _ _

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound := @_root_.OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound
