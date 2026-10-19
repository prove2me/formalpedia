-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:30.629415+00:00
-- url     : https://prove2.me/submissions/a7c0c1fc-e6ea-426e-a7e0-737c7231ff78

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean
-/
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean (solution of MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_avgOver_abs_le_sqrt_of_pointwise
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_projSubMeas_total_proj
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_abs_mul_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_add
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_qSDD_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_nonneg
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Any `OpBounded01` operator is Hermitian. -/
lemma opBounded01_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    Bᴴ = B :=
  (Matrix.nonneg_iff_posSemidef.mp hB.nonnegative).isHermitian.eq
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
lemma opBounded01_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B * B ≤ 1 := by
  have hB_le_one : B ≤ 1 := sub_nonneg.mp hB.boundedByIdentity
  exact le_trans
    (MIPStarRE.Quantum.sq_le_self hB.nonnegative hB_le_one)
    hB_le_one
end
end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.Preliminaries
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
/-- Left tensoring preserves the `0 ≤ B ≤ 1` bounds. -/
lemma leftTensor_opBounded01
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B : MIPStarRE.Quantum.Op ι₁} (hB : OpBounded01 B) :
    OpBounded01 (leftTensor (ι₂ := ι₂) B) := by
  constructor
  · exact leftTensor_nonneg (ι₂ := ι₂) hB.nonnegative
  · exact sub_nonneg.mpr
      (leftTensor_le_one (ι₂ := ι₂) (sub_nonneg.mp hB.boundedByIdentity))
end
end MIPStarRE.LDT.Preliminaries

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Preliminaries
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  intro happrox
  have hδ :
      avgOver 𝒟
        (fun q =>
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [BipartiteSDDRel, sddError, IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight, SubMeas.liftLeft, SubMeas.liftRight] using
      happrox.leftRightSquaredDistanceBound
  have hpointwise :
      ∀ q,
        |(∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))| ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
    intro q
    classical
    let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
    let LT : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) ((A q).total)
    let RT : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) ((A q).total)
    have hLB : OpBounded01 LB := by
      dsimp [LB]
      exact leftTensor_opBounded01 (ι₂ := ι) hB
    have hLB_nonneg : 0 ≤ LB := by
      exact hLB.nonnegative
    have hLB_herm : LBᴴ = LB := by
      exact opBounded01_hermitian hLB
    have hLB_sq_le_one : LB * LB ≤ 1 := by
      exact opBounded01_sq_le_one hLB
    have hLT_nonneg : 0 ≤ LT := by
      dsimp [LT]
      exact leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hRT_nonneg : 0 ≤ RT := by
      dsimp [RT]
      exact rightTensor_nonneg (ι₁ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hLT_herm : LTᴴ = LT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hLT_nonneg).isHermitian.eq
    have hRT_herm : RTᴴ = RT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hRT_nonneg).isHermitian.eq
    have hLT_proj : LT * LT = LT := by
      calc
        LT * LT
          = leftTensor (ι₂ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [LT]
              simpa [leftTensor] using
                (Matrix.mul_kronecker_mul
                  ((A q).total) ((A q).total)
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
        _ = LT := by
              rw [projSubMeas_total_proj (A q)]
    have hRT_proj : RT * RT = RT := by
      calc
        RT * RT
          = rightTensor (ι₁ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [RT]
              simpa [rightTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                  ((A q).total) ((A q).total)).symm
        _ = RT := by
              rw [projSubMeas_total_proj (A q)]
    have hLTRT_comm : LT * RT = RT * LT := by
      calc
        LT * RT
          = opTensor ((A q).total) ((A q).total) := by
              dsimp [LT, RT]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = RT * LT := by
              dsimp [RT, LT]
              simpa [rightTensor, leftTensor, opTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) ((A q).total)
                  ((A q).total) (1 : MIPStarRE.Quantum.Op ι))
    have hLB_diag_le_one : ev ψ (LBᴴ * LB) ≤ 1 := by
      have hmono : ev ψ (LB * LB) ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
        exact ev_mono ψ _ _ hLB_sq_le_one
      simpa [hLB_herm, ev_one_of_isNormalized ψ hψ] using hmono
    have hsqrt_LB : Real.sqrt (ev ψ (LBᴴ * LB)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hLB_diag_le_one
    have hLT_ev :
        ev ψ LT =
          ∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) := by
      dsimp [LT]
      rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
      simp [leftTensor_finset_sum, (A q).sum_eq_total]
    have hRT_ev :
        ev ψ RT =
          ∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) := by
      dsimp [RT]
      rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ι) ((A q).outcome a))]
      simp [rightTensor_finset_sum, (A q).sum_eq_total]
    have hdiag_le_cross :
        ∑ a,
          ev ψ
            (leftTensor (ι₂ := ι) ((A q).outcome a) *
              rightTensor (ι₁ := ι) ((A q).outcome a)) ≤
          ev ψ (LT * RT) := by
      calc
        ∑ a,
            ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                rightTensor (ι₁ := ι) ((A q).outcome a))
          ≤
            ∑ a,
              ∑ b,
                ev ψ
                  (leftTensor (ι₂ := ι) ((A q).outcome a) *
                    rightTensor (ι₁ := ι) ((A q).outcome b)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact Finset.single_le_sum
                (fun b _ =>
                  ev_leftTensor_mul_rightTensor_nonneg ψ
                    ((A q).outcome_pos a) ((A q).outcome_pos b))
                (by simp)
        _ =
            ev ψ (LT * RT) := by
              calc
                ∑ a,
                    ∑ b,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((A q).outcome b))
                  =
                    ∑ a,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [← ev_sum ψ
                        (fun b : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            rightTensor (ι₁ := ι) ((A q).outcome b))]
                      rw [Matrix.mul_sum]
                _ =
                    ev ψ
                      (∑ a,
                        leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [← ev_sum ψ
                        (fun a : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            ∑ b,
                              rightTensor (ι₁ := ι) ((A q).outcome b))]
                _ =
                    ev ψ
                      ((∑ a,
                          leftTensor (ι₂ := ι) ((A q).outcome a)) *
                        ∑ b,
                          rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [Finset.sum_mul]
                _ = ev ψ (LT * RT) := by
                      simp [LT, RT, leftTensor_finset_sum, rightTensor_finset_sum,
                        (A q).sum_eq_total]
    have htotal_sq_le :
        ev ψ ((RT - LT)ᴴ * (RT - LT)) ≤
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
      have hDherm : (RT - LT)ᴴ = RT - LT := by
        simp [hRT_herm, hLT_herm]
      have hD_expand :
          (RT - LT)ᴴ * (RT - LT) = RT + LT - (2 : Error) • (LT * RT) := by
        have hmul :
            (RT - LT) * (RT - LT) = RT * RT - RT * LT - LT * RT + LT * LT := by
          noncomm_ring
        calc
          (RT - LT)ᴴ * (RT - LT)
            = (RT - LT) * (RT - LT) := by simp [hDherm]
          _ = RT * RT - RT * LT - LT * RT + LT * LT := hmul
          _ = RT + LT - (2 : Error) • (LT * RT) := by
                rw [hRT_proj, hLT_proj, hLTRT_comm]
                simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hq_expand :
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) =
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
        unfold qSDD qSDDCore
        calc
          ∑ a,
              ev ψ
                ((((leftTensor (ι₂ := ι) ((A q).outcome a) -
                        rightTensor (ι₁ := ι) ((A q).outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) ((A q).outcome a) -
                      rightTensor (ι₁ := ι) ((A q).outcome a))))
            =
              ∑ a,
                (ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) +
                  ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                  2 *
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                let LA : MIPStarRE.Quantum.Op (ι × ι) :=
                  leftTensor (ι₂ := ι) ((A q).outcome a)
                let RA : MIPStarRE.Quantum.Op (ι × ι) :=
                  rightTensor (ι₁ := ι) ((A q).outcome a)
                have hLA_nonneg : 0 ≤ LA := by
                  dsimp [LA]
                  exact leftTensor_nonneg (ι₂ := ι) ((A q).outcome_pos a)
                have hRA_nonneg : 0 ≤ RA := by
                  dsimp [RA]
                  exact rightTensor_nonneg (ι₁ := ι) ((A q).outcome_pos a)
                have hLA_herm : LAᴴ = LA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hLA_nonneg).isHermitian.eq
                have hRA_herm : RAᴴ = RA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hRA_nonneg).isHermitian.eq
                have hLA_proj : LA * LA = LA := by
                  calc
                    LA * LA
                      = leftTensor (ι₂ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [LA]
                          simpa [leftTensor] using
                            (Matrix.mul_kronecker_mul
                              ((A q).outcome a) ((A q).outcome a)
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
                    _ = LA := by
                          rw [(A q).proj a]
                have hRA_proj : RA * RA = RA := by
                  calc
                    RA * RA
                      = rightTensor (ι₁ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [RA]
                          simpa [rightTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                              ((A q).outcome a) ((A q).outcome a)).symm
                    _ = RA := by
                          rw [(A q).proj a]
                have hcomm : LA * RA = RA * LA := by
                  calc
                    LA * RA
                      = opTensor ((A q).outcome a) ((A q).outcome a) := by
                          dsimp [LA, RA]
                          rw [leftTensor_mul_rightTensor_eq_opTensor]
                    _ = RA * LA := by
                          dsimp [RA, LA]
                          simpa [rightTensor, leftTensor, opTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) ((A q).outcome a)
                              ((A q).outcome a) (1 : MIPStarRE.Quantum.Op ι))
                have hmul :
                    (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
                  noncomm_ring
                calc
                  ev ψ (((LA - RA)ᴴ) * (LA - RA))
                    = ev ψ (RA + LA - (2 : Error) • (LA * RA)) := by
                        rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                        rw [hmul, hLA_proj, hRA_proj, hcomm]
                        simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  _ = ev ψ RA + ev ψ LA - 2 * ev ψ (LA * RA) := by
                        rw [ev_sub]
                        rw [ev_add]
                        have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                          exact ev_scale ψ (2 : Error) (LA * RA)
                        rw [hscale]
          _ =
              (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
                (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
                2 *
                  (∑ a,
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      calc
        ev ψ ((RT - LT)ᴴ * (RT - LT))
          = ev ψ (RT + LT - (2 : Error) • (LT * RT)) := by
              rw [hD_expand]
        _ = ev ψ RT + ev ψ LT - 2 * ev ψ (LT * RT) := by
              rw [ev_sub, ev_add]
              have hscale : ev ψ ((2 : Error) • (LT * RT)) = 2 * ev ψ (LT * RT) := by
                exact ev_scale ψ (2 : Error) (LT * RT)
              rw [hscale]
        _ ≤
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
              rw [hRT_ev, hLT_ev]
              linarith
        _ = qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
              rw [hq_expand]
    have hrewrite :
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
          ev ψ (LB * (RT - LT)) := by
      have hmiddle :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)) =
            ev ψ (LB * RT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))]
        calc
          ev ψ (∑ a,
              leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a))
            = ev ψ
                (LB *
                  ∑ a, rightTensor (ι₁ := ι) ((A q).outcome a)) := by
                    refine congrArg (ev ψ) ?_
                    dsimp [LB]
                    symm
                    exact Finset.mul_sum Finset.univ
                      (fun a : Outcome =>
                        rightTensor (ι₁ := ι) ((A q).outcome a))
                      (leftTensor (ι₂ := ι) B)
          _ = ev ψ (LB * RT) := by
                simp [RT, rightTensor_finset_sum, (A q).sum_eq_total]
      have hright :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
            ev ψ (LB * LT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) (B * (A q).outcome a))]
        calc
          ev ψ (∑ a, leftTensor (ι₂ := ι) (B * (A q).outcome a))
            = ev ψ (∑ a, LB * leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                refine congrArg (ev ψ) ?_
                refine Finset.sum_congr rfl ?_
                intro a _
                dsimp [LB]
                simpa [leftTensor] using
                  (Matrix.mul_kronecker_mul
                    B ((A q).outcome a)
                    (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι))
          _ = ev ψ (LB * ∑ a, leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                rw [Finset.mul_sum]
          _ = ev ψ (LB * LT) := by
                simp [LT, leftTensor_finset_sum, (A q).sum_eq_total]
      calc
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))
          = ev ψ (LB * RT) - ev ψ (LB * LT) := by rw [hmiddle, hright]
        _ = ev ψ (LB * (RT - LT)) := by
              rw [(ev_sub ψ (LB * RT) (LB * LT)).symm]
              simp [mul_sub]
    have hsqrt_LB' : Real.sqrt (ev ψ (LB * LBᴴ)) ≤ 1 := by
      simpa [hLB_herm] using hsqrt_LB
    calc
      |(∑ a, ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) ((A q).outcome a))) -
        ∑ a, ev ψ
          (leftTensor (ι₂ := ι) (B * (A q).outcome a))|
        = |ev ψ (LB * (RT - LT))| := by rw [hrewrite]
      _ ≤
          Real.sqrt (ev ψ (LB * LBᴴ)) *
            Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
              simpa using ev_abs_mul_le_sqrt ψ LB (RT - LT)
      _ ≤ 1 * Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_LB' (Real.sqrt_nonneg _)
      _ = Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by ring
      _ ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
            exact Real.sqrt_le_sqrt htotal_sq_le
  calc
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      = |avgOver 𝒟 (fun q =>
          (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)))| := by
            simp [middleSandwichExpectation, rightSandwichExpectation, avgOver,
              Finset.sum_sub_distrib, mul_sub]
    _ ≤
        Real.sqrt
          (avgOver 𝒟
            (fun q =>
              qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
          exact
            avgOver_abs_le_sqrt_of_pointwise 𝒟
              (fun q =>
                (∑ a, ev ψ
                  (leftTensor (ι₂ := ι) B *
                    rightTensor (ι₁ := ι) ((A q).outcome a))) -
                ∑ a, ev ψ
                  (leftTensor (ι₂ := ι) (B * (A q).outcome a)))
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              hpointwise
              (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              h𝒟
    _ ≤ Real.sqrt δ := by
          exact Real.sqrt_le_sqrt hδ
end MIPStarRE.LDT.Preliminaries
