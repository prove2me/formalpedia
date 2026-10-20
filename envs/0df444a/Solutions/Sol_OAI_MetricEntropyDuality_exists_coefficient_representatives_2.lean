-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_coefficient_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:44:28.929926+00:00
-- url     : https://prove2.me/submissions/5fa1ec5f-67ca-4a32-931b-cfbfc746f5f3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/PolarCover.lean:L71-L101
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_coefficient_representatives. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover

-- ---- from OAI.Analysis.MetricEntropy.Basic ----
namespace OAI

universe uι uX uY

/-!
# Literal finite-dimensional convex bodies and covering numbers

The coordinate space carries its ordinary finite product topology and sup norm.
Polar membership uses the actual real coordinate pairing. Covering centers are
unrestricted ambient vectors. `coveringNumber` is the least finite cover size;
the natural-number empty-infimum convention is zero when no finite cover exists.
The geometric applications prove `Coverable` before using attainment, positivity,
or a lower bound, so that convention never substitutes for a genuine minimum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

section Elementary

variable {ι : Type uι} {X : Type uX} {Y : Type uY} [Fintype ι]

theorem l1Norm_sub_le (x y : RealSpace ι) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y := by
  calc
    l1Norm (x - y) ≤ ∑ i, (|x i| + |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.sub_apply, sub_eq_add_neg, abs_neg] using abs_add_le (x i) (-y i)
    _ = l1Norm x + l1Norm y := by rw [Finset.sum_add_distrib]; rfl

theorem UniformClose.symm {ε : ℝ} {f h : RealSpace X}
    (hfh : UniformClose ε f h) : UniformClose ε h f := by
  intro x
  simpa only [abs_sub_comm] using hfh x

end Elementary

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PolarCover ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe uX uY

/-!
# Polar covers from arbitrary uniform approximation lists

The functions on the approximation list need not be column combinations.
For every nonempty coefficient fiber we choose an actual vector in the
coefficient ball; empty fibers receive zero. The resulting list has exactly
the original number of slots, with no factor depending on the dimension.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype Y]

theorem coefficientRepresentative_mem (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X) :
    coefficientRepresentative g ε f ∈ l1Ball Y := by
  classical
  by_cases h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f
  · simpa only [coefficientRepresentative, dite_eq_left h] using (Classical.choose_spec h).1
  · simpa only [coefficientRepresentative, dite_eq_right h] using
      (zero_mem_l1Ball : (0 : RealSpace Y) ∈ l1Ball Y)

theorem coefficientRepresentative_close (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X)
    (h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f) :
    UniformClose ε (columnCombination g (coefficientRepresentative g ε f)) f := by
  classical
  simpa only [coefficientRepresentative, dite_eq_left h] using (Classical.choose_spec h).2

/-- Two functions within the same error of one arbitrary center are within
twice that error of each other. -/
theorem UniformClose.of_same_center {ε : ℝ} {f h r : RealSpace X}
    (hf : UniformClose ε f h) (hr : UniformClose ε r h) :
    UniformClose (2 * ε) f r := by
  intro x
  have htriangle := abs_sub_le (f x) (h x) (r x)
  have hfx := hf x
  have hrx := hr.symm x
  linarith

/-- Choose one actual coefficient-ball representative for each original
list slot. Every coefficient vector is close to one such representative
both after the column map and in the coefficient ℓ¹ norm. -/
theorem exists_coefficient_representatives (g : Y → X → ℝ) (ε : ℝ)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      ∀ lam ∈ l1Ball Y, ∃ j,
        UniformClose (2 * ε) (columnCombination g lam) (columnCombination g (centers j)) ∧
        l1Norm (lam - centers j) ≤ 2 := by
  classical
  let centers : Fin A.card → RealSpace Y := fun j =>
    coefficientRepresentative g ε ((A.equivFin).symm j).val
  refine ⟨centers, ?_, ?_⟩
  · intro j
    exact coefficientRepresentative_mem g ε _
  · intro lam hLam
    obtain ⟨f, hf, hclose⟩ := hA lam hLam
    let j : Fin A.card := A.equivFin ⟨f, hf⟩
    have hj : centers j = coefficientRepresentative g ε f := by
      simp [centers, j]
    have hrep := coefficientRepresentative_close g ε f ⟨lam, hLam, hclose⟩
    have hrepMem := coefficientRepresentative_mem g ε f
    refine ⟨j, ?_, ?_⟩
    · rw [hj]
      exact hclose.of_same_center hrep
    · rw [hj]
      have hLamNorm : l1Norm lam ≤ 1 := hLam
      have hrepNorm : l1Norm (coefficientRepresentative g ε f) ≤ 1 := hrepMem
      have hsub := l1Norm_sub_le lam (coefficientRepresentative g ε f)
      linarith

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Pointwise


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.exists_coefficient_representatives.{uX,uY} := @_root_.OAI.MetricEntropyDuality.exists_coefficient_representatives.{uX,uY}
