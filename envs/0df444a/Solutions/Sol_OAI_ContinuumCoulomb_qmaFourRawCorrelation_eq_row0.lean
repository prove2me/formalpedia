-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:59:35.033935+00:00
-- url     : https://prove2.me/submissions/aaebb662-1d93-4201-9694-296a6d67c6e5

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ092A007
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_table

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCorrelationCertificate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational spin correlations in the two-column singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourRawCorrelation_000 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 0 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_001 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 0 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_002 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 0 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_010 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 1 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_011 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 1 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_012 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 1 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_020 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 2 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_021 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 2 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_022 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 2 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_030 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 3 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_031 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 3 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_032 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 3 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32] <;> norm_num

theorem qmaFourRawCorrelation_eq_row0_oai (j : Fin 4) (μ ν : Fin 3) :
    (qmaFourSpinRawAction 0 μ).transpose*qmaFourSpinRawAction j ν =
      if μ = ν then qmaFourRawCorrelation 0 j else 0 := by
  fin_cases j
  · fin_cases μ
    · exact qmaFourRawCorrelation_000 ν
    · exact qmaFourRawCorrelation_001 ν
    · exact qmaFourRawCorrelation_002 ν
  · fin_cases μ
    · exact qmaFourRawCorrelation_010 ν
    · exact qmaFourRawCorrelation_011 ν
    · exact qmaFourRawCorrelation_012 ν
  · fin_cases μ
    · exact qmaFourRawCorrelation_020 ν
    · exact qmaFourRawCorrelation_021 ν
    · exact qmaFourRawCorrelation_022 ν
  · fin_cases μ
    · exact qmaFourRawCorrelation_030 ν
    · exact qmaFourRawCorrelation_031 ν
    · exact qmaFourRawCorrelation_032 ν

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row0_oai := @OAI.ContinuumCoulomb.qmaFourRawCorrelation_eq_row0_oai
