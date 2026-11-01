-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourRawEncoding_action
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:02:34.581096+00:00
-- url     : https://prove2.me/submissions/badabc36-4e30-4b07-a3cf-d5ba0986b939

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
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A007

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHamiltonian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed square-lattice Heisenberg source

The finite source is the field-free Heisenberg problem of
Cubitt–Montanaro–Piddock, *Universal quantum Hamiltonians*,
arXiv:1701.05182v4, Theorem 48, Lemma 47 and Section 10.1.
The coordinate-swap action realizes `2 SWAP - I`. Coefficient-rounding
estimates hold for arbitrary many-spin states, including entangled states.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

theorem sourceSpinSwap_apply {n : ℕ} (i j : Fin n)
    (s : SourceSpinBasis n) (k : Fin n) :
    sourceSpinSwap i j s k = s (Equiv.swap i j k) := by
  simp [sourceSpinSwap, Equiv.arrowCongr_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourEncoding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two rational singlet columns spanning the four-spin encoded qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourExchangeRational_mulVec (i j : Fin 4) (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourExchangeRational i j *ᵥ v) s =
      2*v (qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)))-v s := by
  simp only [qmaFourExchangeRational,Matrix.mulVec,dotProduct,sub_mul,
    Finset.sum_sub_distrib,mul_assoc,ite_mul,one_mul,zero_mul,← Finset.mul_sum]
  simp

theorem qmaFourRawEncoding_action01 :
    qmaFourExchangeRational 0 1*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 1 := by
  ext s b
  change (qmaFourExchangeRational 0 1 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action02 :
    qmaFourExchangeRational 0 2*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 2 := by
  ext s b
  change (qmaFourExchangeRational 0 2 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action03 :
    qmaFourExchangeRational 0 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 3 := by
  ext s b
  change (qmaFourExchangeRational 0 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action12 :
    qmaFourExchangeRational 1 2*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 1 2 := by
  ext s b
  change (qmaFourExchangeRational 1 2 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action13 :
    qmaFourExchangeRational 1 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 1 3 := by
  ext s b
  change (qmaFourExchangeRational 1 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action23 :
    qmaFourExchangeRational 2 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 2 3 := by
  ext s b
  change (qmaFourExchangeRational 2 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two] <;> norm_num

theorem qmaFourRawEncoding_action_oai (i j : Fin 4) (hij : i < j) :
    qmaFourExchangeRational i j*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical i j := by
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · exact qmaFourRawEncoding_action01
    · exact qmaFourRawEncoding_action02
    · exact qmaFourRawEncoding_action03
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact qmaFourRawEncoding_action12
    · exact qmaFourRawEncoding_action13
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact qmaFourRawEncoding_action23
  · fin_cases j <;> norm_num at hij

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourRawEncoding_action_oai := @OAI.ContinuumCoulomb.qmaFourRawEncoding_action_oai
