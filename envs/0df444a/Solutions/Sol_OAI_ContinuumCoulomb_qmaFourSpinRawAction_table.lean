-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourSpinRawAction_table
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:09:22.747496+00:00
-- url     : https://prove2.me/submissions/d0c7fe8f-cf28-447a-9675-ad9473f35f95

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

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse rational tables for the four-spin contractions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpinRawAction_table00 :
    qmaFourSpinRawAction 0 0 = qmaFourSpinTable00 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable00,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table01 :
    qmaFourSpinRawAction 0 1 = qmaFourSpinTable01 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable01,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table02 :
    qmaFourSpinRawAction 0 2 = qmaFourSpinTable02 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable02,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table10 :
    qmaFourSpinRawAction 1 0 = qmaFourSpinTable10 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable10,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table11 :
    qmaFourSpinRawAction 1 1 = qmaFourSpinTable11 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable11,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table12 :
    qmaFourSpinRawAction 1 2 = qmaFourSpinTable12 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable12,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table20 :
    qmaFourSpinRawAction 2 0 = qmaFourSpinTable20 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable20,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table21 :
    qmaFourSpinRawAction 2 1 = qmaFourSpinTable21 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable21,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table22 :
    qmaFourSpinRawAction 2 2 = qmaFourSpinTable22 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable22,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table30 :
    qmaFourSpinRawAction 3 0 = qmaFourSpinTable30 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable30,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table31 :
    qmaFourSpinRawAction 3 1 = qmaFourSpinTable31 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable31,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table32 :
    qmaFourSpinRawAction 3 2 = qmaFourSpinTable32 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinTable32,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_table_oai (i : Fin 4) (μ : Fin 3) :
    qmaFourSpinRawAction i μ = qmaFourSpinTable i μ := by
  fin_cases i
  · fin_cases μ
    · exact qmaFourSpinRawAction_table00
    · exact qmaFourSpinRawAction_table01
    · exact qmaFourSpinRawAction_table02
  · fin_cases μ
    · exact qmaFourSpinRawAction_table10
    · exact qmaFourSpinRawAction_table11
    · exact qmaFourSpinRawAction_table12
  · fin_cases μ
    · exact qmaFourSpinRawAction_table20
    · exact qmaFourSpinRawAction_table21
    · exact qmaFourSpinRawAction_table22
  · fin_cases μ
    · exact qmaFourSpinRawAction_table30
    · exact qmaFourSpinRawAction_table31
    · exact qmaFourSpinRawAction_table32

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourSpinRawAction_table_oai := @OAI.ContinuumCoulomb.qmaFourSpinRawAction_table_oai
