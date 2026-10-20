-- Prove2me | solution 2 for OAI.MetricEntropyDuality.mem_smul_polar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:42:47.717465+00:00
-- url     : https://prove2.me/submissions/c98feaaa-6487-4bca-bdbc-ce0e04f4707c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SupportPolar.lean:L71-L86
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.mem_smul_polar_iff. The node keeps its source
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

theorem pairing_comm (x y : RealSpace ι) : pairing x y = pairing y x := by
  simp only [pairing, mul_comm]

theorem pairing_smul_left (a : ℝ) (x y : RealSpace ι) :
    pairing (a • x) y = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

theorem pairing_smul_right (a : ℝ) (x y : RealSpace ι) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_comm, pairing_smul_left, pairing_comm y x]

end Elementary

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.SupportPolar ----
namespace OAI

universe uι uX uY

/-!
# Exact support and polar calculations

Both summands of the matrix body have explicit maximizing points. Consequently
the support equalities below are equalities to attained finite suprema, not
uses of the convention for an empty or unbounded real supremum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {X : Type uX} {Y : Type uY}

/-- This formulation does not require boundedness, symmetry, or attainment. -/
theorem mem_smul_polar_iff [Fintype ι] (K : Set (RealSpace ι)) (δ : RealSpace ι)
    {c : ℝ} (hc : 0 < c) :
    δ ∈ c • polar K ↔ ∀ z ∈ K, pairing z δ ≤ c := by
  constructor
  · intro h z hz
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp h
    rw [pairing_smul_right]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hv z hz) hc.le
  · intro h
    refine Set.mem_smul_set.mpr ⟨c⁻¹ • δ, ?_, ?_⟩
    · intro z hz
      rw [pairing_smul_right]
      have h' := mul_le_mul_of_nonneg_left (h z hz) (inv_nonneg.mpr hc.le)
      simpa only [inv_mul_cancel₀ hc.ne'] using h'
    · rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Pointwise


theorem solution.{uι} : type_of% @_root_.OAI.MetricEntropyDuality.mem_smul_polar_iff.{uι} := @_root_.OAI.MetricEntropyDuality.mem_smul_polar_iff.{uι}
