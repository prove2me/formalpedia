-- Prove2me | solution 1 for MIPStarRE.LDT.sandwichTensor_residual_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:19.48101+00:00
-- url     : https://prove2.me/submissions/44f016a6-a654-493c-829c-5b19d14b077b

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/TensorPlacement.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/TensorPlacement.lean (solution of MIPStarRE.LDT.sandwichTensor_residual_sum_le_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
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
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {α β γ ιA ιB : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Outer : SubMeas β ιA) (Inner : SubMeas α ιA) (Right : SubMeas γ ιB) :
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2))) ≤ 1 := by
  let sandwichTotal : MIPStarRE.Quantum.Op ιA :=
    ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o
  have hsandwichTotal_nonneg : 0 ≤ sandwichTotal := by
    exact Finset.sum_nonneg fun o _ =>
      IsSelfAdjoint.conjugate_nonneg
        (SubMeas.total_nonneg Inner) (Outer.outcome_hermitian o)
  have hsandwichTotal_le_one : sandwichTotal ≤ 1 := by
    calc
      sandwichTotal
        ≤ ∑ o : β, Outer.outcome o := by
            refine Finset.sum_le_sum ?_
            intro o _
            exact le_trans
              (IsSelfAdjoint.conjugate_le_conjugate
                Inner.total_le_one (Outer.outcome_hermitian o))
              (by
                simpa using
                  MIPStarRE.Quantum.sq_le_self
                    (Outer.outcome_pos o) (SubMeas.outcome_le_one Outer o))
      _ = Outer.total := Outer.sum_eq_total
      _ ≤ 1 := Outer.total_le_one
  have hop_sum :
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)) =
        leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total := by
    calc
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2))
        = ∑ i : α, ∑ r : γ, ∑ o : β,
            leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome r) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ιA) Right.total := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (∑ r : γ, ∑ o : β,
                  leftTensor (ι₂ := ιB)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                    rightTensor (ι₁ := ιA) (Right.outcome r))
                = ∑ o : β, ∑ r : γ,
                    leftTensor (ι₂ := ιB)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ιA) (Right.outcome r) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ιB)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ιA) Right.total := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [← Matrix.mul_sum]
                    rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ Right.outcome]
                    rw [Right.sum_eq_total]
      _ = (∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome i * Outer.outcome o)) *
            rightTensor (ι₁ := ιA) Right.total := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_mul]
      _ = leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total := by
            congr 1
            calc
              ∑ i : α, ∑ o : β,
                  leftTensor (ι₂ := ιB)
                    (Outer.outcome o * Inner.outcome i * Outer.outcome o)
                = ∑ o : β, ∑ i : α,
                    leftTensor (ι₂ := ιB)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ιB)
                      (∑ i : α,
                        Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ]
              _ = leftTensor (ι₂ := ιB)
                    (∑ o : β, ∑ i : α,
                      Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ]
              _ = leftTensor (ι₂ := ιB) sandwichTotal := by
                    congr 1
                    calc
                      ∑ o : β, ∑ i : α,
                          Outer.outcome o * Inner.outcome i * Outer.outcome o
                        = ∑ o : β,
                            Outer.outcome o * Inner.total * Outer.outcome o := by
                            refine Finset.sum_congr rfl ?_
                            intro o _
                            rw [← Matrix.sum_mul, ← Matrix.mul_sum, Inner.sum_eq_total]
                      _ = sandwichTotal := rfl
  calc
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)))
      = ev ψ (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro ir _
          rw [ev_sum]
    _ = ev ψ (leftTensor (ι₂ := ιB) sandwichTotal *
        rightTensor (ι₁ := ιA) Right.total) := by
          rw [hop_sum]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
          apply ev_mono ψ _ _
          calc
            leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total
              = opTensor sandwichTotal Right.total := by
                rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ιB) sandwichTotal :=
                opTensor_le_leftTensor hsandwichTotal_nonneg Right.total_le_one
            _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) hsandwichTotal_le_one
    _ = 1 := ev_one_of_isNormalized ψ hnorm
end MIPStarRE.LDT
