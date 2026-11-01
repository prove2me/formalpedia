-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:06:23.070709+00:00
-- url     : https://prove2.me/submissions/8985484d-edc8-4dae-bbd9-fa0fd27670e3

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinCertificate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed rational certificates for the one-spin excited columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpinRawAction_orthogonal00 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_orthogonal01 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_orthogonal02 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def] <;> norm_num

theorem qmaFourSpinRawAction_orthogonal_row0_oai (μ : Fin 3) :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 μ = 0 := by
  fin_cases μ
  · exact qmaFourSpinRawAction_orthogonal00
  · exact qmaFourSpinRawAction_orthogonal01
  · exact qmaFourSpinRawAction_orthogonal02

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row0_oai := @OAI.ContinuumCoulomb.qmaFourSpinRawAction_orthogonal_row0_oai
