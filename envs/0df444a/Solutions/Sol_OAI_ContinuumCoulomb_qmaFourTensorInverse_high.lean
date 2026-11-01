-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourTensorInverse_high
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:11:30.330536+00:00
-- url     : https://prove2.me/submissions/385346ad-b53b-4b66-87d6-bc258f1d13a1

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
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawEncoding_action

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

theorem qmaMatrixOperator_smul (c : ℂ) (M : Matrix α β ℂ) :
    qmaMatrixOperator (c • M) = c • qmaMatrixOperator M := by
  unfold qmaMatrixOperator
  rw [map_smul,map_smul]

theorem qmaMatrixOperator_mul [DecidableEq γ] (M : Matrix α β ℂ) (N : Matrix β γ ℂ) :
    qmaMatrixOperator (M*N) = (qmaMatrixOperator M).comp (qmaMatrixOperator N) := by
  ext x a
  change Matrix.toLpLin 2 2 (M*N) x a = Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) a
  rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourLogical
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact logical actions of the six physical exchanges in the singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourLogical_normalize (i j : Fin 4) :
    (qmaFourRawLogical i j).map (Rat.castHom ℂ)*qmaFourNormalization =
      qmaFourNormalization*qmaFourLogical i j := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  unfold qmaFourRawLogical qmaFourLogical
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.map_apply,Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [hs]

theorem qmaFourEncoding_action (i j : Fin 4) (hij : i < j) :
    qmaFourExchange i j*qmaFourEncoding = qmaFourEncoding*qmaFourLogical i j := by
  have he := congrArg (fun M : Matrix (Fin 16) (Fin 2) ℚ => M.map (Rat.castHom ℂ))
    (qmaFourRawEncoding_action i j hij)
  rw [Matrix.map_mul,Matrix.map_mul] at he
  change qmaFourExchange i j*qmaFourRawComplex =
    qmaFourRawComplex*(qmaFourRawLogical i j).map (Rat.castHom ℂ) at he
  rw [qmaFourEncoding,← Matrix.mul_assoc,he,Matrix.mul_assoc,qmaFourLogical_normalize,
    ← Matrix.mul_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourGround
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four-spin penalty vanishes exactly on the encoded qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical

theorem qmaFourLogical_sum :
    qmaFourLogical 0 1+qmaFourLogical 0 2+qmaFourLogical 0 3+
      qmaFourLogical 1 2+qmaFourLogical 1 3+qmaFourLogical 2 3 =
        (-6:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [qmaFourLogical] <;> ring

theorem qmaFourPenalty_exchange : qmaFourPenalty =
    qmaFourExchange 0 1+qmaFourExchange 0 2+qmaFourExchange 0 3+
      qmaFourExchange 1 2+qmaFourExchange 1 3+qmaFourExchange 2 3+
        (6:ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  ext s t
  by_cases h : s = t
  all_goals
    simp [qmaFourPenalty,qmaFourPenaltyRational,qmaFourExchange,Matrix.map_apply,h]

theorem qmaFourPenalty_encoding : qmaFourPenalty*qmaFourEncoding = 0 := by
  rw [qmaFourPenalty_exchange]
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul]
  rw [qmaFourEncoding_action 0 1 (by decide),qmaFourEncoding_action 0 2 (by decide),
    qmaFourEncoding_action 0 3 (by decide),qmaFourEncoding_action 1 2 (by decide),
    qmaFourEncoding_action 1 3 (by decide),qmaFourEncoding_action 2 3 (by decide)]
  rw [← Matrix.mul_add,← Matrix.mul_add,← Matrix.mul_add,← Matrix.mul_add,
    ← Matrix.mul_add,qmaFourLogical_sum,Matrix.mul_smul,Matrix.mul_one]
  simp

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

omit [Fintype τ] [DecidableEq σ] in
theorem qmaTensorMatrix_gram [DecidableEq τ] (A : Q → Matrix σ τ ℂ)
    (hA : ∀ i, (A i).conjTranspose*A i = 1) :
    (qmaTensorMatrix A).conjTranspose*qmaTensorMatrix A = 1 := by
  rw [qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simpa only [hA] using (qmaTensorMatrix_one (Q := Q) (σ := τ))

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

theorem qmaFourTensorEncoding_gram (n : ℕ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorEncoding n = 1 :=
  qmaTensorMatrix_gram _ (fun _ => qmaFourEncoding_gram)

theorem qmaFourTensorEncoding_projector (n : ℕ) :
    qmaFourTensorEncoding n*(qmaFourTensorEncoding n).conjTranspose = qmaFourTensorProjection n := by
  rw [qmaFourTensorEncoding,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simp only [qmaFourEncoding_projector,qmaFourTensorProjection]

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorAction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local actions and excitation energies of actual finite tensor columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ τ : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype σ] [DecidableEq σ] [Fintype τ]

omit [Fintype τ] in
theorem qmaSiteMatrix_tensor (i : Q) (A : Matrix σ σ ℂ) (B : Q → Matrix σ τ ℂ) :
    qmaSiteMatrix i A*qmaTensorMatrix B =
      qmaTensorMatrix (fun j => if j = i then A*B j else B j) := by
  rw [qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] in
theorem qmaTensorMatrix_smul_at (A : Q → Matrix σ τ ℂ) (i : Q) (c : ℂ) :
    qmaTensorMatrix (fun j => if j = i then c • A j else A j) = c • qmaTensorMatrix A := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.smul_apply,smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, if_true,Matrix.smul_apply,smul_eq_mul]
  have hp : (∏ j ∈ Finset.univ.erase i,
      (if j = i then c • A j else A j) (s j) (t j)) =
      ∏ j ∈ Finset.univ.erase i, A j (s j) (t j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hp]
  ring

omit [Fintype τ] in
theorem qmaSiteMatrix_tensor_eigen (i : Q) (H : Matrix σ σ ℂ) (A : Q → Matrix σ τ ℂ)
    (c : ℂ) (hA : H*A i = c • A i) :
    qmaSiteMatrix i H*qmaTensorMatrix A = c • qmaTensorMatrix A := by
  rw [qmaSiteMatrix_tensor,← qmaTensorMatrix_smul_at A i c]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true, if_true,hA]
  · simp only [hj,ite_false, if_false]

variable {n : ℕ}

omit [Fintype τ] in
theorem qmaTensorPenalty_eigen (H : Matrix σ σ ℂ) (A : Fin n → Matrix σ τ ℂ)
    (c : Fin n → ℂ) (hA : ∀ i, H*A i = c i • A i) :
    qmaTensorPenalty n H*qmaTensorMatrix A = (∑ i, c i) • qmaTensorMatrix A := by
  rw [qmaTensorPenalty,Matrix.sum_mul]
  simp only [qmaSiteMatrix_tensor_eigen _ H A _ (hA _),Finset.sum_smul]

theorem qmaFourTensorPenalty_encoding (n : ℕ) :
    qmaFourTensorPenalty n*qmaFourTensorEncoding n = 0 := by
  have h := qmaTensorPenalty_eigen qmaFourPenalty (fun _ : Fin n => qmaFourEncoding)
    (fun _ => (0:ℂ)) (by intro i; simp [qmaFourPenalty_encoding])
  simpa only [qmaFourTensorPenalty,qmaFourTensorEncoding,Finset.sum_const_zero,zero_smul] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorHilbert
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourTensor_projection_star (n : ℕ) :
    (qmaFourTensorProjection n).conjTranspose = qmaFourTensorProjection n := by
  rw [← qmaFourTensorEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem qmaFourTensor_penalty_star (n : ℕ) :
    (qmaFourTensorPenalty n).conjTranspose = qmaFourTensorPenalty n := by
  have h := (qmaFourTensorGap_posSemidef n).isHermitian
  have hp := qmaFourTensor_projection_star n
  have hs : ((4:ℂ) • (1-qmaFourTensorProjection n)).conjTranspose =
      (4:ℂ) • (1-qmaFourTensorProjection n) := by
    simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hp]
    norm_num
  have he := congrArg (fun M : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ =>
      M+(4:ℂ) • (1-qmaFourTensorProjection n)) h.eq
  simpa only [Matrix.conjTranspose_sub,hs,sub_add_cancel] using he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorInverse
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded inverse acts exactly on the physical two-block excitations. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_padded_star (n : ℕ) :
    (qmaFourTensorPaddedMatrix n).conjTranspose = qmaFourTensorPaddedMatrix n := by
  simp only [qmaFourTensorPaddedMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    qmaFourTensor_penalty_star,qmaFourTensor_projection_star]
  norm_num

theorem qmaFourTensorPadded_encoding (n : ℕ) :
    qmaFourTensorPaddedMatrix n*qmaFourTensorEncoding n = (4:ℂ) • qmaFourTensorEncoding n := by
  rw [qmaFourTensorPaddedMatrix,Matrix.add_mul,qmaFourTensorPenalty_encoding,
    Matrix.smul_mul,← qmaFourTensorEncoding_projector,Matrix.mul_assoc,qmaFourTensorEncoding_gram,
    Matrix.mul_one,zero_add]

theorem qmaFourTensorPadded_restrict (n : ℕ) (r : ℝ)
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaFourTensorRestriction n (qmaFourTensorPadded n r x) =
      (4*r^2) • qmaFourTensorRestriction n x := by
  have hm := congrArg Matrix.conjTranspose (qmaFourTensorPadded_encoding n)
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,qmaFourTensor_padded_star] at hm
  norm_num at hm
  have he := congrArg (fun M => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at he
  change qmaFourTensorRestriction n (qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x) =
    (4:ℂ) • qmaFourTensorRestriction n x at he
  change qmaFourTensorRestriction n (r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x) = _
  rw [map_smul,he]
  ext s
  simp only [PiLp.smul_apply,Complex.real_smul]
  push_cast
  ring

theorem qmaFourTensorInverse_high_oai {r : ℝ} (hr : 0 < r)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x)
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) (hx : qmaFourTensorRestriction n x = 0) :
    qmaFourTensorRestriction n (T x) = 0 := by
  have h := congrArg (qmaFourTensorRestriction n) (hAT x)
  rw [qmaFourTensorPadded_restrict,hx] at h
  exact (smul_eq_zero.mp h).resolve_left (by positivity)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.qmaFourTensorInverse_high_oai := @OAI.ContinuumCoulomb.qmaFourTensorInverse_high_oai
