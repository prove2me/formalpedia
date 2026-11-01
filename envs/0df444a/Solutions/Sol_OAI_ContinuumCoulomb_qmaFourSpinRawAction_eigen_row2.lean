-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:05:06.792581+00:00
-- url     : https://prove2.me/submissions/e3e55dd5-67ad-43fc-84c0-cae50539f2b0

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinCertificate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourPenaltyRational_mulVec (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourPenaltyRational *ᵥ v) s = 2*(
      v (qmaFourIndex (sourceSpinSwap 0 1 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 0 2 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 0 3 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 1 2 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 1 3 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 2 3 (qmaFourBits s)))) := by
  simp only [qmaFourPenaltyRational,Matrix.add_mulVec,Pi.add_apply,Matrix.smul_mulVec,
    Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,qmaFourExchangeRational_mulVec]
  ring

theorem qmaFourSpinRawAction_eigen20 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 0 =
      (4:ℚ) • qmaFourSpinRawAction 2 0 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 0 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply] <;> norm_num

theorem qmaFourSpinRawAction_eigen21 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 1 =
      (4:ℚ) • qmaFourSpinRawAction 2 1 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 1 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply] <;> norm_num

theorem qmaFourSpinRawAction_eigen22 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 2 =
      (4:ℚ) • qmaFourSpinRawAction 2 2 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 2 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    simp [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply] <;> norm_num

theorem qmaFourSpinRawAction_eigen_row2_oai (μ : Fin 3) :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 μ = (4:ℚ) • qmaFourSpinRawAction 2 μ := by
  fin_cases μ
  · exact qmaFourSpinRawAction_eigen20
  · exact qmaFourSpinRawAction_eigen21
  · exact qmaFourSpinRawAction_eigen22

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row2_oai := @OAI.ContinuumCoulomb.qmaFourSpinRawAction_eigen_row2_oai
