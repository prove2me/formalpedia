-- Prove2me | solution 1 for MIPRE.QLD.exists_projective_of_nearProjective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:16.470289+00:00
-- url     : https://prove2.me/submissions/eda193d9-582d-4f9d-b684-397f28da7919

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Assembly.lean
-/
/-
# Assembly of the orthogonalized PVM (step **F3**)

This file carries out the last step of the proof of Theorem 1.2 in the finite
case (M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 3, lines 247–271 of `manuscript/arXiv2103.14126v2.tex`;
`PLAN.md` §1, step **F3**).

The input is the isometry data of `Orthogonalization/IsometryData.lean`: reading
the partial isometry `u ∈ M_n(M)` of Lemma 3.2 block by block gives operators
`w_i = (e_{1i} ⊗ 1) u` on `H` satisfying

* (W1) `∑ i, w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ j, q_j a_j`.

The paper's PVM is `p_i = u* t_i u` with `t_i = e_{ii} ⊗ q_i`, which in this
block notation is exactly `p_i = w_i* w_i` (`assembledPVM`). We prove:

* `IsometryData.q_mul_w`: `q_i w_i = w_i`;
* `assembledPVM_isStarProjection`, `sum_assembledPVM`: `(p_i)` is a PVM;
* `sqrt_mul_assembledPVM_mul_sqrt`: the paper's `|x| p_i |x| = q_i a_i`;
* `assembled_bound`: the three-term estimate
  `φ (∑ i, |a_i − p_i|²) < 9 ε`, from `φ (∑ a_i²) > 1 − ε` and
  `φ (∑ q_i a_i) ≥ 1 − ε`.

The estimate is proved through `assembled_bound_core`, which abstracts the
square root `|x|` into a plain operator `s` subject to the three properties the
argument actually uses (`0 ≤ s ≤ 1`, `s² = y`, `s p_i s = q_i a_i`); this keeps
the (long) inequality bookkeeping free of `CFC.sqrt`.

Nothing in this file is a statement of the paper; it is proof-side machinery for
`Orthogonalization/Basic.lean`.
-/
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Main.lean
-/
/-
# Tier T1a: Theorem 1.2 for `B(H)`, `H` finite-dimensional

Assembly of the three finite-dimensional steps (`PLAN.md` §1, §3):

* **F1** `FinDim.exists_commuting_projections` (Lemma 3.1): projections `q i`
  commuting with `a i`, total trace `dim H`, `φ(∑ q i a i) ≥ φ(∑ a i a i)`;
* **F2** `FinDim.exists_isometryData` (Lemma 3.2 in `M_n(B(H))`): the block
  partial isometry `w` with `w i* w i` summing to `1`, `w i w j* = δ q i`,
  `w i √y = q i √(a i)`;
* **F3** `assembled_bound`: the PVM `p i = w i* w i` and the three-term estimate
  `φ(∑ |a i − p i|²) < 9ε`.

`povm_orthogonalization_finDim` is the engine, stated for an arbitrary state
`φ` on `B(H)` (a positive normalized linear functional: normality is automatic
in finite dimension and is not used); `povm_orthogonalization_of_mem_all` and
`povm_orthogonalization_fullAlgebra` are the literal instances of the signed
statement `povm_orthogonalization` (Theorem 1.2) for a von Neumann algebra
containing every operator, resp. for `fullAlgebra H = B(H)` (encoding decision
E6 of `PLAN.md`; FIDELITY.md, "Instances").
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Ortho.lean (solution of MIPRE.QLD.exists_projective_of_nearProjective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Theorems.Thm_MIPRE_quadForm_eq
import Theorems.Thm_Orthogonalization_FinDim_exists_commuting_projections
import Theorems.Thm_Orthogonalization_FinDim_exists_isometryData
import Theorems.Thm_Orthogonalization_assembledPVM_isStarProjection
import Theorems.Thm_Orthogonalization_assembled_bound

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a q w : ι → H →L[ℂ] H}
/-- The assembled projections sum to `1`: this is (W1). -/
theorem sum_assembledPVM (hw : IsometryData a q w) : ∑ i, assembledPVM w i = 1 :=
  hw.sum_star_mul
end
end Orthogonalization

namespace Orthogonalization
section
open scoped BigOperators ComplexOrder
open Module
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]
/-- **Theorem 1.2 for `B(H)`, `H` finite-dimensional, any state.** A POVM `(a i)`
on a finite-dimensional Hilbert space and a positive normalized linear functional
`φ` on `B(H)` with `φ(∑ a i²) > 1 − ε` admit a PVM `(p i)` on `H` with
`φ(∑ |a i − p i|²) < 9ε`. -/
theorem povm_orthogonalization_finDim (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, (∀ i, IsStarProjection (p i)) ∧ ∑ i, p i = 1 ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  classical
  obtain ⟨q, hq, hqa, htr, hqa'⟩ := FinDim.exists_commuting_projections φ a ha0 ha1
  obtain ⟨w, hw⟩ := FinDim.exists_isometryData a q ha0 hq hqa htr
  exact ⟨assembledPVM w, assembledPVM_isStarProjection hw, sum_assembledPVM hw,
    assembled_bound φ hφ hφ1 a q w ha0 ha1 hq hqa hw ε hε (le_trans hε.le hqa')⟩
end
end Orthogonalization

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_sub (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x - y) = ofCLM x - ofCLM y := map_sub _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_mul (x y : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (x * y) = ofCLM x * ofCLM y := map_mul _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_one : ofCLM (1 : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) = 1 := map_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_star (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (star x) = (ofCLM x)ᴴ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.map_star' x
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem ofCLM_sum {ι : Type*} (s : Finset ι)
    (f : ι → EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    ofCLM (∑ i ∈ s, f i) = ∑ i ∈ s, ofCLM (f i) := map_sum _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem toCLM_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    toCLM (∑ i ∈ s, f i) = ∑ i ∈ s, toCLM (f i) := map_sum _ _ _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem toCLM_one : toCLM (1 : Matrix dA dA ℂ) = 1 := map_one _
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- A positive semidefinite matrix is a positive operator: `toEuclideanCLM` is a star-algebra
equivalence of C*-algebras, so it preserves the order. -/
theorem toCLM_nonneg {M : Matrix dA dA ℂ} (hM : (0 : Matrix dA dA ℂ) ≤ M) :
    0 ≤ toCLM M :=
  map_nonneg _ hM
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The reduced state is normalized exactly when `ψ` is a unit vector. -/
theorem redState_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    redState ψ 1 = 1 := by
  rw [redState_apply, ofCLM_one, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ]
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The reduced state on a square is the state-dependent squared norm.** -/
theorem redState_star_mul_self (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    redState ψ (star x * x) = (stateSqNorm ψ (ofCLM x) : ℂ) := by
  rw [redState_apply, ofCLM_mul, ofCLM_star, quadForm_eq]
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Hence the reduced state is positive. -/
theorem redState_nonneg (ψ : dA × dB → ℂ)
    (x : EuclideanSpace ℂ dA →L[ℂ] EuclideanSpace ℂ dA) :
    0 ≤ redState ψ (star x * x) := by
  rw [redState_star_mul_self]
  exact Complex.zero_le_real.mpr (stateSqNorm_nonneg ψ _)
end
end MIPRE.QLD

namespace MIPRE.QLD
section
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **The reduced state on the square of a self-adjoint operator**, which is the form the
vendored theorem's near-projectivity hypothesis takes. -/
theorem redState_mul_self (ψ : dA × dB → ℂ) {M : Matrix dA dA ℂ} (hM : Mᴴ = M) :
    redState ψ (toCLM M * toCLM M) = (stateSqNorm ψ M : ℂ) := by
  have hMM : M * M = Mᴴ * M := by rw [hM]
  rw [redState_apply, ofCLM_mul, ofCLM_toCLM, hMM]
  exact quadForm_eq ψ M
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq A] in
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (ε : ℝ) (hε : 1 - ε < ∑ a, stateSqNorm ψ ((Q.mats a).val)) :
    ∃ P : A → Matrix dA dA ℂ,
      (∀ a, (P a)ᴴ = P a) ∧ (∀ a, P a * P a = P a) ∧ (∑ a, P a = 1) ∧
        ∑ a, stateSqNorm ψ ((Q.mats a).val - P a) < 9 * ε := by
  classical
  -- the POVM, as positive operators summing to one
  have hQnn : ∀ a, (0 : Matrix dA dA ℂ) ≤ (Q.mats a).val := fun a =>
    Subtype.coe_le_coe.mpr (Q.nonneg a)
  have ha0 : ∀ a, 0 ≤ toCLM ((Q.mats a).val) := fun a => toCLM_nonneg (hQnn a)
  have ha1 : ∑ a, toCLM ((Q.mats a).val) = 1 := by
    have hone : ∑ a, ((Q.mats a).val) = (1 : Matrix dA dA ℂ) := by
      rw [← AddSubmonoidClass.coe_finsetSum, Q.normalized]
      rfl
    rw [← toCLM_sum, hone, toCLM_one]
  -- each element is self-adjoint, so its square is what the hypothesis measures
  have hsq : ∀ a, redState ψ (toCLM ((Q.mats a).val) * toCLM ((Q.mats a).val))
      = (stateSqNorm ψ ((Q.mats a).val) : ℂ) := fun a =>
    redState_mul_self ψ ((Q.mats a).2 : star ((Q.mats a).val) = (Q.mats a).val)
  -- the hypothesis, in the vendored theorem's form
  have hε' : 1 - ε
      < (redState ψ (∑ a, toCLM ((Q.mats a).val) * toCLM ((Q.mats a).val))).re := by
    rw [map_sum (redState ψ), Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hsq a,
      ← Complex.ofReal_sum, Complex.ofReal_re]
    exact hε
  obtain ⟨p, hp, hpsum, hbound⟩ := Orthogonalization.povm_orthogonalization_finDim
    (redState ψ) (redState_nonneg ψ) (redState_one hψ)
    (fun a => toCLM ((Q.mats a).val)) ha0 ha1 ε hε'
  refine ⟨fun a => ofCLM (p a), fun a => ?_, fun a => ?_, ?_, ?_⟩
  · have h : ofCLM (star (p a)) = (ofCLM (p a))ᴴ := ofCLM_star (p a)
    rw [show star (p a) = p a from (hp a).isSelfAdjoint] at h
    exact h.symm
  · have h : ofCLM (p a * p a) = ofCLM (p a) * ofCLM (p a) := ofCLM_mul _ _
    rw [show p a * p a = p a from (hp a).isIdempotentElem] at h
    exact h.symm
  · rw [← ofCLM_sum, hpsum, ofCLM_one]
  · refine lt_of_le_of_lt (le_of_eq ?_) hbound
    rw [map_sum (redState ψ), Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [redState_star_mul_self, Complex.ofReal_re, ofCLM_sub, ofCLM_toCLM]
end MIPRE.QLD
