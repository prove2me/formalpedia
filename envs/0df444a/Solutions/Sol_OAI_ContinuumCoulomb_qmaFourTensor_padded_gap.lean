-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourTensor_padded_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:15:41.124334+00:00
-- url     : https://prove2.me/submissions/78709682-80cd-483a-b4cb-7c4716cc35ea

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit ordinary-spin coordinates for a simultaneous mediator stage.
The new sites are the two actual members of every fresh pair. -/

noncomputable section
namespace ContinuumCoulomb.MediatorGraph
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem submatrix_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (∑ e, M e).submatrix f g = ∑ e, (M e).submatrix f g := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

theorem submatrix_add_apply {ι κ α β : Type*} (M N : Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (M + N).submatrix f g = M.submatrix f g + N.submatrix f g := rfl

theorem kronecker_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : Matrix ι κ ℂ) (N : γ → Matrix α β ℂ) :
    M ⊗ₖ (∑ e, N e) = ∑ e, M ⊗ₖ N e := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumQuadratic
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix quadratic forms used by the explicit history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_add {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (M+N) u = qmaQuadratic M u+qmaQuadratic N u := by
  simp [qmaQuadratic,Matrix.add_mulVec,dotProduct_add]

theorem qmaQuadratic_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a : ℝ) (u : ι → ℂ) :
    qmaQuadratic ((a:ℂ) • M) u = a*qmaQuadratic M u := by
  simp [qmaQuadratic,Matrix.smul_mulVec,dotProduct_smul,Complex.mul_re]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRectangularOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Euclidean operators for the actual mediator columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem qmaMatrixOperator_square [DecidableEq α] (M : Matrix α α ℂ) :
    qmaMatrixOperator M = spinMatrixOperator M := rfl

theorem qmaEuclidean_real_inner (x y : EuclideanSpace ℂ α) :
    ⟪x,y⟫_ℝ = (⟪x,y⟫_ℂ).re := by
  simp only [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourEncoding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourRawEncoding_gram : qmaFourRawEncoding.transpose*qmaFourRawEncoding =
    Matrix.diagonal ![(4:ℚ),12] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ] <;> norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourGapCertificate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational positive factorization of the four-spin penalty above the
singlet projection. Each fixed row is checked separately at default limits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourGapRational_row0 (t : Fin 16) :
    qmaFourGapRational 0 t = qmaFourSymmetricRational 0 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row1 (t : Fin 16) :
    qmaFourGapRational 1 t = qmaFourSymmetricRational 1 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row2 (t : Fin 16) :
    qmaFourGapRational 2 t = qmaFourSymmetricRational 2 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row3 (t : Fin 16) :
    qmaFourGapRational 3 t = qmaFourSymmetricRational 3 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row4 (t : Fin 16) :
    qmaFourGapRational 4 t = qmaFourSymmetricRational 4 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row5 (t : Fin 16) :
    qmaFourGapRational 5 t = qmaFourSymmetricRational 5 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row6 (t : Fin 16) :
    qmaFourGapRational 6 t = qmaFourSymmetricRational 6 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row7 (t : Fin 16) :
    qmaFourGapRational 7 t = qmaFourSymmetricRational 7 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row8 (t : Fin 16) :
    qmaFourGapRational 8 t = qmaFourSymmetricRational 8 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row9 (t : Fin 16) :
    qmaFourGapRational 9 t = qmaFourSymmetricRational 9 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row10 (t : Fin 16) :
    qmaFourGapRational 10 t = qmaFourSymmetricRational 10 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row11 (t : Fin 16) :
    qmaFourGapRational 11 t = qmaFourSymmetricRational 11 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row12 (t : Fin 16) :
    qmaFourGapRational 12 t = qmaFourSymmetricRational 12 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row13 (t : Fin 16) :
    qmaFourGapRational 13 t = qmaFourSymmetricRational 13 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row14 (t : Fin 16) :
    qmaFourGapRational 14 t = qmaFourSymmetricRational 14 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_row15 (t : Fin 16) :
    qmaFourGapRational 15 t = qmaFourSymmetricRational 15 t := by
  fin_cases t <;>
    simp [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply] <;> norm_num

theorem qmaFourGapRational_factor : qmaFourGapRational = qmaFourSymmetricRational := by
  ext s t
  fin_cases s
  · exact qmaFourGapRational_row0 t
  · exact qmaFourGapRational_row1 t
  · exact qmaFourGapRational_row2 t
  · exact qmaFourGapRational_row3 t
  · exact qmaFourGapRational_row4 t
  · exact qmaFourGapRational_row5 t
  · exact qmaFourGapRational_row6 t
  · exact qmaFourGapRational_row7 t
  · exact qmaFourGapRational_row8 t
  · exact qmaFourGapRational_row9 t
  · exact qmaFourGapRational_row10 t
  · exact qmaFourGapRational_row11 t
  · exact qmaFourGapRational_row12 t
  · exact qmaFourGapRational_row13 t
  · exact qmaFourGapRational_row14 t
  · exact qmaFourGapRational_row15 t

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourIsometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the two exact singlet columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourRawComplex_adjoint : qmaFourRawComplex.conjTranspose =
    qmaFourRawEncoding.transpose.map (Rat.castHom ℂ) := by
  ext b s
  simp [qmaFourRawComplex,Matrix.conjTranspose_apply,Matrix.transpose_apply]

theorem qmaFourRawComplex_gram : qmaFourRawComplex.conjTranspose*qmaFourRawComplex =
    Matrix.diagonal ![(4:ℂ),12] := by
  rw [qmaFourRawComplex_adjoint]
  change qmaFourRawEncoding.transpose.map (Rat.castHom ℂ)*
    qmaFourRawEncoding.map (Rat.castHom ℂ) = _
  rw [← Matrix.map_mul,qmaFourRawEncoding_gram]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.diagonal_apply]

theorem qmaFourEncoding_gram : qmaFourEncoding.conjTranspose*qmaFourEncoding = 1 := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have htwo : (starRingEnd ℂ) (2:ℂ) = 2 := by
    exact Complex.conj_ofReal 2
  calc
    _ = qmaFourNormalization.conjTranspose*(qmaFourRawComplex.conjTranspose*qmaFourRawComplex)*
        qmaFourNormalization := by
      simp only [qmaFourEncoding,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = qmaFourNormalization.conjTranspose*Matrix.diagonal ![(4:ℂ),12]*qmaFourNormalization := by
      rw [qmaFourRawComplex_gram]
    _ = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.conjTranspose_apply,
          Matrix.diagonal_apply,Matrix.one_apply,Fin.sum_univ_two,Complex.star_def,htwo]
      field_simp
      rw [hs]
      norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOperatorQuadratic
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix quadratic forms agree with the real forms of their actual
complex Euclidean operators, including rectangular compressions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β]

theorem qmaQuadratic_operator (M : Matrix α α ℂ) (p : EuclideanSpace ℂ α) :
    qmaQuadratic M (fun i => p i) = ⟪p,qmaMatrixOperator M p⟫_ℝ := by
  rw [qmaEuclidean_real_inner]
  simp only [qmaQuadratic,PiLp.inner_apply,RCLike.inner_apply',qmaMatrixOperator_apply,
    Matrix.mulVec,dotProduct,Pi.star_apply,starRingEnd_apply]

theorem qmaQuadratic_sub (M N : Matrix α α ℂ) (p : α → ℂ) :
    qmaQuadratic (M-N) p = qmaQuadratic M p-qmaQuadratic N p := by
  have hn : qmaQuadratic (-N) p = -qmaQuadratic N p := by
    have h := qmaQuadratic_smul N (-1) p
    simpa using h
  simp only [sub_eq_add_neg,qmaQuadratic_add,hn]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourPositive
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The checked rational certificate is nonnegative on all complex states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSymmetricRational_factor :
    qmaFourSymmetricColumn*Matrix.diagonal qmaFourSymmetricWeights*qmaFourSymmetricColumn.transpose =
      qmaFourSymmetricRational := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,qmaFourSymmetricColumn]
  by_cases h : qmaFourWeight s = qmaFourWeight t
  · simp [qmaFourSymmetricRational,← h]
  · simp only [qmaFourSymmetricRational,h,ite_false, if_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hsk : qmaFourWeight s = k
    · have htk : qmaFourWeight t ≠ k := fun ht => h (hsk.trans ht.symm)
      simp [hsk,htk]
    · simp [hsk]

theorem qmaRatMatrix_adjoint {α β : Type*} (M : Matrix α β ℚ) :
    (M.map (Rat.castHom ℂ)).conjTranspose = M.transpose.map (Rat.castHom ℂ) := by
  ext a b
  simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]

theorem qmaFourSymmetricDiagonal_cast :
    (Matrix.diagonal qmaFourSymmetricWeights).map (Rat.castHom ℂ) = qmaFourSymmetricDiagonal := by
  ext a b
  by_cases h : a = b
  · subst b
    simp only [Matrix.map_apply,Matrix.diagonal_apply,ite_true, if_true,qmaFourSymmetricDiagonal]
    norm_cast
  · simp [h,qmaFourSymmetricDiagonal]

theorem qmaFourSymmetricComplex_factor :
    qmaFourSymmetricRational.map (Rat.castHom ℂ) = qmaFourSymmetricColumnComplex*
      qmaFourSymmetricDiagonal*qmaFourSymmetricColumnComplex.conjTranspose := by
  rw [← qmaFourSymmetricRational_factor,Matrix.map_mul,Matrix.map_mul,
    qmaFourSymmetricDiagonal_cast]
  rw [qmaFourSymmetricColumnComplex,qmaRatMatrix_adjoint]

theorem qmaFourGap_complex : qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection) =
    qmaFourSymmetricRational.map (Rat.castHom ℂ) := by
  rw [← qmaFourGapRational_factor]
  ext s t
  simp only [qmaFourPenalty,qmaFourProjection,qmaFourGapRational,Matrix.map_apply,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,map_sub,map_mul,map_ofNat,Matrix.one_apply]
  by_cases h : s = t <;> simp [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourProjector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational projection is exactly the normalized singlet range. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical

theorem qmaFourNormalization_square : qmaFourNormalization*qmaFourNormalization.conjTranspose =
    (Matrix.diagonal ![(1/4:ℚ),1/12]).map (Rat.castHom ℂ) := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have htwo : (starRingEnd ℂ) (2:ℂ) = 2 := Complex.conj_ofReal 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply,
      Matrix.diagonal_apply,Fin.sum_univ_two,Complex.star_def,htwo]
  field_simp
  rw [hs]
  norm_num

theorem qmaFourProjectionRational_factor :
    qmaFourRawEncoding*Matrix.diagonal ![(1/4:ℚ),1/12]*qmaFourRawEncoding.transpose =
      qmaFourProjectionRational := by
  ext s t
  simp [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply,Fin.sum_univ_two,
    qmaFourRawEncoding,qmaFourProjectionRational]
  ring

theorem qmaFourEncoding_projector : qmaFourEncoding*qmaFourEncoding.conjTranspose = qmaFourProjection := by
  calc
    _ = qmaFourRawComplex*(qmaFourNormalization*qmaFourNormalization.conjTranspose)*
        qmaFourRawComplex.conjTranspose := by
      simp only [qmaFourEncoding,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = qmaFourProjection := by
      rw [qmaFourNormalization_square,qmaFourRawComplex_adjoint,qmaFourRawComplex,
        ← Matrix.map_mul,← Matrix.map_mul,qmaFourProjectionRational_factor]
      rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourDoubleGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full two-block penalty has a gap above its four-dimensional code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical ComplexOrder

theorem qmaFourGap_posSemidef :
    (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection)).PosSemidef := by
  rw [qmaFourGap_complex,qmaFourSymmetricComplex_factor]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro k
  apply Complex.zero_le_real.mpr
  fin_cases k <;> norm_num [qmaFourSymmetricWeights]

theorem qmaFourComplement_posSemidef :
    (1-qmaFourProjection).PosSemidef := by
  have hP : qmaFourProjection*qmaFourProjection = qmaFourProjection := by
    rw [← qmaFourEncoding_projector]
    calc
      _ = qmaFourEncoding*(qmaFourEncoding.conjTranspose*qmaFourEncoding)*
          qmaFourEncoding.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [qmaFourEncoding_gram,Matrix.mul_one]
  have hstar : qmaFourProjection.conjTranspose = qmaFourProjection := by
    rw [← qmaFourEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have he : (1-qmaFourProjection).conjTranspose*(1-qmaFourProjection) =
      1-qmaFourProjection := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hstar]
    noncomm_ring [hP]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tensor matrices used to place the proved four-spin code at every site. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical ComplexOrder
variable {Q σ τ υ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [Fintype τ] [Fintype υ]

omit [Fintype σ] [Fintype υ] in
theorem qmaTensorMatrix_mul (A : Q → Matrix σ τ ℂ) (B : Q → Matrix τ υ ℂ) :
    qmaTensorMatrix A*qmaTensorMatrix B = qmaTensorMatrix (fun i => A i*B i) := by
  ext s t
  change (∑ r : Q → τ, (∏ i, A i (s i) (r i))*(∏ i, B i (r i) (t i))) = _
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => A i (s i) a*B i a (t i))).symm

omit [Fintype σ] [Fintype τ] [DecidableEq Q] in
theorem qmaTensorMatrix_star (A : Q → Matrix σ τ ℂ) :
    (qmaTensorMatrix A).conjTranspose = qmaTensorMatrix (fun i => (A i).conjTranspose) := by
  ext s t
  simp [qmaTensorMatrix,Matrix.conjTranspose_apply]

variable [DecidableEq σ]

omit [Fintype σ] [DecidableEq Q] in
theorem qmaTensorMatrix_one : qmaTensorMatrix (fun _ : Q => (1 : Matrix σ σ ℂ)) = 1 := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq σ] in
theorem qmaTensorMatrix_projector (P : Q → Matrix σ σ ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (hPP : ∀ i, P i*P i = P i) :
    (qmaTensorMatrix P).conjTranspose*qmaTensorMatrix P = qmaTensorMatrix P := by
  rw [qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simp only [hP,hPP]

theorem qmaTensorMatrix_complement_posSemidef (P : Q → Matrix σ σ ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (hPP : ∀ i, P i*P i = P i) :
    (1-qmaTensorMatrix P).PosSemidef := by
  have hstar : (qmaTensorMatrix P).conjTranspose = qmaTensorMatrix P := by
    rw [qmaTensorMatrix_star]
    simp only [hP]
  have hs : qmaTensorMatrix P*qmaTensorMatrix P = qmaTensorMatrix P := by
    simpa only [hstar] using qmaTensorMatrix_projector P hP hPP
  have he : (1-qmaTensorMatrix P).conjTranspose*(1-qmaTensorMatrix P) = 1-qmaTensorMatrix P := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hstar]
    noncomm_ring [hs]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorSucc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting off the first physical block in a finite tensor Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder
variable {σ τ : Type*} {n : ℕ}

theorem qmaTensorMatrix_succ (A : Fin (n+1) → Matrix σ τ ℂ) :
    qmaTensorMatrix A =
      (A 0 ⊗ₖ qmaTensorMatrix (fun i : Fin n => A i.succ)).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv τ n) := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Fin.prod_univ_succ]
  rfl

variable [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
theorem qmaSiteMatrix_succ_zero (H : Matrix σ σ ℂ) :
    qmaSiteMatrix (0:Fin (n+1)) H =
      (H ⊗ₖ (1 : Matrix (Fin n → σ) (Fin n → σ) ℂ)).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_succ]
  simp only [ite_true, if_true,Fin.succ_ne_zero,ite_false, if_false,qmaTensorMatrix_one]

omit [Fintype σ] in
theorem qmaSiteMatrix_succ_succ (i : Fin n) (H : Matrix σ σ ℂ) :
    qmaSiteMatrix i.succ H =
      ((1 : Matrix σ σ ℂ) ⊗ₖ qmaSiteMatrix i H).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_succ]
  have hz : (0:Fin (n+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp only [hz,ite_false, if_false,Fin.succ_inj]
  rfl

omit [Fintype σ] in
theorem qmaTensorPenalty_succ (H : Matrix σ σ ℂ) :
    qmaTensorPenalty (n+1) H =
      (H ⊗ₖ (1 : Matrix (Fin n → σ) (Fin n → σ) ℂ)+
        (1 : Matrix σ σ ℂ) ⊗ₖ qmaTensorPenalty n H).submatrix
        (qmaTensorSuccEquiv σ n) (qmaTensorSuccEquiv σ n) := by
  rw [qmaTensorPenalty,Fin.sum_univ_succ,qmaSiteMatrix_succ_zero]
  simp only [qmaSiteMatrix_succ_succ,← MediatorGraph.submatrix_sum,
    ← MediatorGraph.kronecker_sum,← MediatorGraph.submatrix_add_apply,qmaTensorPenalty]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual many-block four-spin penalty has a uniform full-complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder

theorem qmaFourProjection_star : qmaFourProjection.conjTranspose = qmaFourProjection := by
  rw [← qmaFourEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem qmaFourProjection_square : qmaFourProjection*qmaFourProjection = qmaFourProjection := by
  rw [← qmaFourEncoding_projector]
  calc
    _ = qmaFourEncoding*(qmaFourEncoding.conjTranspose*qmaFourEncoding)*
        qmaFourEncoding.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [qmaFourEncoding_gram,Matrix.mul_one]

theorem qmaFourTensorComplement_posSemidef (n : ℕ) :
    (1-qmaFourTensorProjection n).PosSemidef :=
  qmaTensorMatrix_complement_posSemidef _ (fun _ => qmaFourProjection_star)
    (fun _ => qmaFourProjection_square)

theorem qmaFourTensorGap_posSemidef (n : ℕ) :
    (qmaFourTensorPenalty n-(4:ℂ) • (1-qmaFourTensorProjection n)).PosSemidef := by
  induction n with
  | zero =>
    have hP : qmaFourTensorProjection 0 = 1 := by
      ext s t
      simp [qmaFourTensorProjection,qmaTensorMatrix,Matrix.one_apply,Subsingleton.elim s t]
    simpa only [qmaFourTensorPenalty,qmaTensorPenalty,Fin.sum_univ_zero,hP,sub_self,smul_zero,sub_zero]
      using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0 → Fin 16) (Fin 0 → Fin 16) ℂ).PosSemidef)
  | succ n ih =>
    let P := qmaFourTensorProjection n
    let H := qmaFourTensorPenalty n
    have he : qmaFourTensorPenalty (n+1)-(4:ℂ) • (1-qmaFourTensorProjection (n+1)) =
        (qmaFourPenalty ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ H-
            (4:ℂ) • (1-qmaFourProjection ⊗ₖ P)).submatrix
              (qmaTensorSuccEquiv (Fin 16) n) (qmaTensorSuccEquiv (Fin 16) n) := by
      rw [qmaFourTensorPenalty,qmaTensorPenalty_succ,qmaFourTensorProjection,qmaTensorMatrix_succ]
      simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
        Matrix.submatrix_one_equiv]
      rfl
    have hsplit : qmaFourPenalty ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ H-(4:ℂ) • (1-qmaFourProjection ⊗ₖ P) =
        (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection)) ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ (H-(4:ℂ) • (1-P))+
          (4:ℂ) • ((1-qmaFourProjection) ⊗ₖ (1-P)) := by
      ext s t
      rcases s with ⟨s₁,s₂⟩
      rcases t with ⟨t₁,t₂⟩
      by_cases h₁ : s₁ = t₁ <;> by_cases h₂ : s₂ = t₂ <;>
        simp [Matrix.kroneckerMap_apply,h₁,h₂,Prod.ext_iff] <;> ring
    rw [he,hsplit]
    apply Matrix.PosSemidef.submatrix
    exact ((qmaFourGap_posSemidef.kronecker Matrix.PosSemidef.one).add
      (Matrix.PosSemidef.one.kronecker ih)).add
        ((qmaFourComplement_posSemidef.kronecker (qmaFourTensorComplement_posSemidef n)).smul
          (by norm_num))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual low/high coordinates and the bounded padded inverse for the four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical ComplexOrder

theorem qmaFourTensor_padded_gap_oai (n : ℕ) (r : ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    (4*r^2)*‖x‖^2 ≤ ⟪x,qmaFourTensorPadded n r x⟫_ℝ := by
  have he : qmaFourTensorPaddedMatrix n-(4:ℂ) • 1 =
      qmaFourTensorPenalty n-(4:ℂ) • (1-qmaFourTensorProjection n) := by
    unfold qmaFourTensorPaddedMatrix
    module
  have hh := (Complex.nonneg_iff.mp
    ((he ▸ qmaFourTensorGap_posSemidef n).dotProduct_mulVec_nonneg (fun i => x i))).1
  change 0 ≤ qmaQuadratic (qmaFourTensorPaddedMatrix n-(4:ℂ) • 1) (fun i => x i) at hh
  rw [qmaQuadratic_sub] at hh
  have hone : qmaQuadratic ((4:ℂ) • (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ))
      (fun i => x i) = 4*‖x‖^2 := by
    rw [show (4:ℂ) = ((4:ℝ):ℂ) from rfl,qmaQuadratic_smul,qmaQuadratic_operator,
      qmaMatrixOperator_square,spinMatrixOperator_one,one_apply_eq_self,real_inner_self_eq_norm_sq]
  rw [hone] at hh
  have h := mul_le_mul_of_nonneg_left (sub_nonneg.mp hh) (sq_nonneg r)
  change _ ≤ ⟪x,r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x⟫_ℝ
  rw [inner_smul_right,← qmaQuadratic_operator]
  nlinarith

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourTensor_padded_gap_oai := @OAI.ContinuumCoulomb.qmaFourTensor_padded_gap_oai
