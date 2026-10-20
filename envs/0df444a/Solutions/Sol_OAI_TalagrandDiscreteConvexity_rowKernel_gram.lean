-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.rowKernel_gram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:50:35.174837+00:00
-- url     : https://prove2.me/submissions/0da76541-517a-41e6-acd0-4851b98b0efe

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FourierProductKernel.lean:L53-L87
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.rowKernel_gram. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights

-- ---- from OAI.Combinatorics.DiscreteConvexity.FourierProductKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Orthogonality of the biased product kernel

The two possible choices at one coordinate give its Bernoulli diagonal
matrix. Summing over all subsets tensors this identity, with no square roots
or choice of a normalized Fourier basis.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

/-- The one-coordinate Gram identity for the mass and alternating factors. -/
theorem bitWeight_correction_gram (q : ℝ) (hq1 : q < 1) (x y : Bool) :
    bitWeight q x * bitWeight q y +
        (q / (1 - q)) * correction q x * correction q y =
      if x = y then bitWeight q x else 0 := by
  have hden : (1 : ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  cases x <;> cases y <;>
    simp [bitWeight, correction] <;> field_simp [hden] <;> ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Move the subset weight into the coordinate product. -/
theorem rowKernel_weighted_product (q : ℝ) (U : Finset V) (x y : V → Bool) :
    (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y =
      ∏ i, if i ∈ U then
        (q / (1 - q)) * correction q (x i) * correction q (y i)
      else bitWeight q (x i) * bitWeight q (y i) := by
  have hp : (q / (1 - q)) ^ U.card =
      ∏ i : V, if i ∈ U then q / (1 - q) else 1 := by
    symm
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  rw [hp]
  simp only [rowKernel]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U <;> simp [hi]

/-- Summing the weighted kernel products over all subsets gives the original
Bernoulli mass on the diagonal and zero away from the diagonal. -/
theorem rowKernel_gram (q : ℝ) (_hq0 : 0 < q) (hq1 : q < 1) (x y : V → Bool) :
    (∑ U : Finset V,
      (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y) =
      if x = y then cubeWeight q x else 0 := by
  classical
  calc
    (∑ U : Finset V,
        (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y) =
        ∑ U : Finset V, ∏ i, if i ∈ U then
          (q / (1 - q)) * correction q (x i) * correction q (y i)
        else bitWeight q (x i) * bitWeight q (y i) := by
      apply Finset.sum_congr rfl
      intro U _
      exact rowKernel_weighted_product q U x y
    _ = ∏ i,
        ((q / (1 - q)) * correction q (x i) * correction q (y i) +
          bitWeight q (x i) * bitWeight q (y i)) := by
      simpa using (sum_finset_product (fun (i : V) (flag : Bool) =>
        if flag then
          (q / (1 - q)) * correction q (x i) * correction q (y i)
        else bitWeight q (x i) * bitWeight q (y i)))
    _ = ∏ i, if x i = y i then bitWeight q (x i) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [add_comm]
      exact bitWeight_correction_gram q hq1 (x i) (y i)
    _ = if x = y then cubeWeight q x else 0 := by
      rw [Fintype.prod_ite_zero]
      by_cases hxy : x = y
      · have hpoint : ∀ i, x i = y i := fun i => congrFun hxy i
        simp only [ite_eq_left hpoint, ite_eq_left hxy, cubeWeight]
      · have hpoint : ¬ ∀ i, x i = y i := fun h => hxy (funext h)
        simp only [ite_eq_right hpoint, ite_eq_right hxy]

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.rowKernel_gram := @_root_.OAI.TalagrandDiscreteConvexity.rowKernel_gram
