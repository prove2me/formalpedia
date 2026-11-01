-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourTensorFull_effective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:11:04.474118+00:00
-- url     : https://prove2.me/submissions/6bbeacbd-c3ed-4456-aa0c-a9b7a262a8e7

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
import Definitions.Def_OAIQ092A006
import Definitions.Def_OAIQ092A007
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawCorrelation_eq_row0
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawCorrelation_eq_row1
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawCorrelation_eq_row2
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawCorrelation_eq_row3
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawEncoding_action
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row0
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row1
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row2
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row3

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinMatrixNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent operator bounds for the actual spin matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual one-site Paulis are Hermitian. -/
theorem pauli_star (μ : Fin 3) : (pauli μ).conjTranspose = pauli μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

theorem sourceTensor_star (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor n M).conjTranspose = sourceTensor n (fun i => (M i).conjTranspose) := by
  ext s t
  simp only [sourceTensor, Matrix.conjTranspose_apply, star_prod]

theorem sourceLocalPauli_star (n : ℕ) (i : Fin n) (μ : Fin 3) :
    (sourceLocalPauli n i μ).conjTranspose = sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_star]
  congr 1
  funext k
  by_cases hki : k = i <;> simp [hki, pauli_star]

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

theorem qmaRatMatrix_adjoint {α β : Type*} (M : Matrix α β ℚ) :
    (M.map (Rat.castHom ℂ)).conjTranspose = M.transpose.map (Rat.castHom ℂ) := by
  ext a b
  simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]

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

theorem qmaFourEncoding_compression (i j : Fin 4) (hij : i < j) :
    qmaFourEncoding.conjTranspose*qmaFourExchange i j*qmaFourEncoding = qmaFourLogical i j := by
  rw [Matrix.mul_assoc,qmaFourEncoding_action i j hij,← Matrix.mul_assoc,qmaFourEncoding_gram,
    Matrix.one_mul]

theorem qmaFourLogical_Z : qmaFourLogical 0 1 = -(1 : Matrix (Fin 2) (Fin 2) ℂ)-(2:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [qmaFourLogical,pauliZ,Matrix.one_apply]

theorem qmaFourLogical_X : qmaFourLogical 0 3-qmaFourLogical 0 2 =
    (2*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [qmaFourLogical,pauliX]
  all_goals ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourFields
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logical X and Z fields are realized by internal physical exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourField_compression (x z : ℝ) :
    qmaFourEncoding.conjTranspose*qmaFourField x z*qmaFourEncoding =
      (x:ℂ) • pauliX+(z:ℂ) • pauliZ+((z/2:ℝ):ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [qmaFourField,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [qmaFourEncoding_compression 0 3 (by decide),
    qmaFourEncoding_compression 0 2 (by decide),qmaFourEncoding_compression 0 1 (by decide),
    qmaFourLogical_X,qmaFourLogical_Z]
  push_cast
  simp only [smul_smul,smul_sub,smul_neg]
  have hx : ((x:ℂ)/(2*(Real.sqrt 3:ℂ)))*(2*(Real.sqrt 3:ℂ)) = x := by field_simp
  have hz : ((z:ℂ)/2)*2 = z := by ring
  rw [hx,hz]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpin
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical single-spin actions on the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpin_source (i : Fin 4) (μ : Fin 3) : qmaFourSpin i μ =
    (sourceLocalPauli 4 i μ).submatrix qmaFourBits qmaFourBits := by
  ext s t
  have he : qmaFourSpinIndex i μ s = t ↔
      Function.update (qmaFourBits s) i (qmaPauliBit μ (qmaFourBits s i)) = qmaFourBits t :=
    qmaFourBasisEquiv.eq_symm_apply.symm
  simp only [qmaFourSpin,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,
    qmaFourSpinRational,map_mul,Matrix.submatrix_apply,qmaLocalPauli_monomial]
  by_cases h : qmaFourSpinIndex i μ s = t
  · simp [h,he.mp h]
  · have ht := mt he.mpr h
    simp [h,ht]

theorem qmaFourSpinRational_mulVec (i : Fin 4) (μ : Fin 3) (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourSpinRational i μ *ᵥ v) s =
      qmaPhysicalPauliSign μ (qmaFourBits s i)*v (qmaFourSpinIndex i μ s) := by
  simp only [qmaFourSpinRational,Matrix.mulVec,dotProduct,mul_assoc,← Finset.mul_sum,
    ite_mul,one_mul,zero_mul]
  simp

theorem qmaFourSpinRawAction_eq (i : Fin 4) (μ : Fin 3) :
    qmaFourSpinRational i μ*qmaFourRawEncoding = qmaFourSpinRawAction i μ := by
  ext s b
  exact qmaFourSpinRational_mulVec i μ (fun t => qmaFourRawEncoding t b) s

theorem qmaFourSpin_encoding (i : Fin 4) (μ : Fin 3) :
    qmaFourSpin i μ*qmaFourEncoding = qmaPauliPhase μ •
      ((qmaFourSpinRawAction i μ).map (Rat.castHom ℂ)*qmaFourNormalization) := by
  rw [qmaFourSpin,qmaFourEncoding,Matrix.smul_mul,← Matrix.mul_assoc,qmaFourRawComplex,
    ← Matrix.map_mul,qmaFourSpinRawAction_eq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinCertificate
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

theorem qmaFourSpinRawAction_orthogonal (i : Fin 4) (μ : Fin 3) :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction i μ = 0 := by
  fin_cases i
  · exact qmaFourSpinRawAction_orthogonal_row0 μ
  · exact qmaFourSpinRawAction_orthogonal_row1 μ
  · exact qmaFourSpinRawAction_orthogonal_row2 μ
  · exact qmaFourSpinRawAction_orthogonal_row3 μ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCorrelationCertificate
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

theorem qmaFourRawCorrelation_eq (i j : Fin 4) (μ ν : Fin 3) :
    (qmaFourSpinRawAction i μ).transpose*qmaFourSpinRawAction j ν =
      if μ = ν then qmaFourRawCorrelation i j else 0 := by
  fin_cases i
  · exact qmaFourRawCorrelation_eq_row0 j μ ν
  · exact qmaFourRawCorrelation_eq_row1 j μ ν
  · exact qmaFourRawCorrelation_eq_row2 j μ ν
  · exact qmaFourRawCorrelation_eq_row3 j μ ν

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourSpinTransition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Single-spin transitions leave the singlet code and have penalty four. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpin_star (i : Fin 4) (μ : Fin 3) :
    (qmaFourSpin i μ).conjTranspose = qmaFourSpin i μ := by
  rw [qmaFourSpin_source,Matrix.conjTranspose_submatrix,sourceLocalPauli_star]

theorem qmaFourSpin_orthogonal (i : Fin 4) (μ : Fin 3) :
    qmaFourEncoding.conjTranspose*qmaFourSpin i μ*qmaFourEncoding = 0 := by
  rw [Matrix.mul_assoc,qmaFourSpin_encoding,Matrix.mul_smul]
  have he : qmaFourEncoding.conjTranspose*
      ((qmaFourSpinRawAction i μ).map (Rat.castHom ℂ)*qmaFourNormalization) = 0 := by
    rw [qmaFourEncoding,Matrix.conjTranspose_mul,qmaFourRawComplex_adjoint]
    calc
      _ = qmaFourNormalization.conjTranspose*
          ((qmaFourRawEncoding.transpose*qmaFourSpinRawAction i μ).map (Rat.castHom ℂ))*
          qmaFourNormalization := by rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [qmaFourSpinRawAction_orthogonal]; simp
  rw [he,smul_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCorrelation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isotropic physical-spin correlations in the normalized singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCorrelation_comm (i j : Fin 4) : qmaFourCorrelation i j = qmaFourCorrelation j i := by
  simp only [qmaFourCorrelation,eq_comm,min_comm,max_comm]

theorem qmaFourNormalization_gram :
    qmaFourNormalization.conjTranspose*
      (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*qmaFourNormalization = 1 := by
  have he := qmaFourEncoding_gram
  rw [qmaFourEncoding,Matrix.conjTranspose_mul,qmaFourRawComplex_adjoint,
    qmaFourRawComplex] at he
  calc
    _ = qmaFourNormalization.conjTranspose*
        ((qmaFourRawEncoding.transpose*qmaFourRawEncoding).map (Rat.castHom ℂ))*
        qmaFourNormalization := by rw [qmaFourRawEncoding_gram]
    _ = 1 := by rw [Matrix.map_mul]; simpa only [Matrix.mul_assoc] using he

theorem qmaFourRawCorrelation_normalized (i j : Fin 4) :
    qmaFourNormalization.conjTranspose*(qmaFourRawCorrelation i j).map (Rat.castHom ℂ)*
      qmaFourNormalization = qmaFourCorrelation i j := by
  by_cases hij : i = j
  · simp only [qmaFourRawCorrelation,qmaFourCorrelation,hij,ite_true, if_true]
    exact qmaFourNormalization_gram
  · simp only [qmaFourRawCorrelation,qmaFourCorrelation,hij,ite_false, if_false]
    have hmap : ((1/3:ℚ) • (Matrix.diagonal ![(4:ℚ),12]*
        qmaFourRawLogical (min i j) (max i j))).map (Rat.castHom ℂ) =
        (1/3:ℂ) • ((Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          (qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)) := by
      calc
        _ = (1/3:ℂ) • ((Matrix.diagonal ![(4:ℚ),12]*
            qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)) := by
          ext a b
          simp
        _ = _ := by rw [Matrix.map_mul]
    rw [hmap,Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    calc
      _ = qmaFourNormalization.conjTranspose*
          (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          ((qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)*
            qmaFourNormalization) := by simp only [Matrix.mul_assoc]
      _ = qmaFourNormalization.conjTranspose*
          (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          (qmaFourNormalization*qmaFourLogical (min i j) (max i j)) := by
        rw [qmaFourLogical_normalize]
      _ = _ := by rw [← Matrix.mul_assoc,qmaFourNormalization_gram,Matrix.one_mul]

theorem qmaFourPauliPhase_norm (μ : Fin 3) :
    star (qmaPauliPhase μ)*qmaPauliPhase μ = 1 := by
  fin_cases μ <;> norm_num [qmaPauliPhase,Complex.star_def]

theorem qmaFourSpin_correlation (i j : Fin 4) (μ ν : Fin 3) :
    (qmaFourSpin i μ*qmaFourEncoding).conjTranspose*(qmaFourSpin j ν*qmaFourEncoding) =
      if μ = ν then qmaFourCorrelation i j else 0 := by
  rw [qmaFourSpin_encoding,qmaFourSpin_encoding,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul,qmaRatMatrix_adjoint,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have he : (qmaFourNormalization.conjTranspose*
      (qmaFourSpinRawAction i μ).transpose.map (Rat.castHom ℂ))*
      ((qmaFourSpinRawAction j ν).map (Rat.castHom ℂ)*qmaFourNormalization) =
      qmaFourNormalization.conjTranspose*
        ((qmaFourSpinRawAction i μ).transpose*qmaFourSpinRawAction j ν).map (Rat.castHom ℂ)*
        qmaFourNormalization := by
    rw [Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  rw [he,qmaFourRawCorrelation_eq]
  by_cases h : μ = ν
  · subst ν
    rw [ite_eq_left (rfl : μ = μ),qmaFourRawCorrelation_normalized,
      ite_eq_left (rfl : μ = μ),qmaFourPauliPhase_norm,one_smul]
  · simp [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourStencils
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational physical-spin weights giving shifted logical X and Z. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourXWeights_true :
    qmaFourWeightedCorrelation (qmaFourXWeights true) =
      (400:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(128*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaFourWeightedCorrelation,qmaFourXWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliX] <;> norm_num <;> ring

theorem qmaFourXWeights_false :
    qmaFourWeightedCorrelation (qmaFourXWeights false) =
      (400:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(-128*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaFourWeightedCorrelation,qmaFourXWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliX] <;> norm_num <;> ring

theorem qmaFourZWeights_true :
    qmaFourWeightedCorrelation (qmaFourZWeights true) =
      (8/3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(4/3:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaFourWeightedCorrelation,qmaFourZWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliZ] <;> norm_num

theorem qmaFourZWeights_false :
    qmaFourWeightedCorrelation (qmaFourZWeights false) =
      (4/3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(-4/3:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaFourWeightedCorrelation,qmaFourZWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliZ] <;> norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourAxis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common interface for the fixed X and Z exchange encodings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisScale_pos (a : Fin 2) : 0 < qmaFourAxisScale a := by
  fin_cases a <;> simp only [qmaFourAxisScale,Fin.zero_eta,ite_true, if_true,Fin.isValue,Fin.mk_one,
    Fin.reduceEq,ite_false, if_false]
  · positivity
  · norm_num

theorem qmaFourAxisWeights_correlation (a : Fin 2) (p : Bool) :
    qmaFourWeightedCorrelation (qmaFourAxisWeights a p) =
      (qmaFourAxisShift a p:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      ((qmaFourAxisSign p*qmaFourAxisScale a:ℝ):ℂ) • qmaFourAxis a := by
  fin_cases a <;> cases p <;>
    simp [qmaFourAxisWeights,qmaFourAxisShift,qmaFourAxisSign,qmaFourAxisScale,qmaFourAxis,
      qmaFourXWeights_true,qmaFourXWeights_false,qmaFourZWeights_true,qmaFourZWeights_false,neg_div,neg_smul]

theorem qmaFourAxisField_compression (a : Fin 2) (t : ℝ) :
    qmaFourEncoding.conjTranspose*qmaFourAxisField a t*qmaFourEncoding =
      (t:ℂ) • qmaFourAxis a+(qmaFourAxisFieldShift a t:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases a <;> simp [qmaFourAxisField,qmaFourAxis,qmaFourAxisFieldShift,qmaFourField_compression]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCouplingScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration of the physical inter-block strength for either coupling sign. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCouplingSize_square (a b : Fin 2) (j : ℝ) :
    (3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*qmaFourAxisScale b = |j| := by
  have ha := qmaFourAxisScale_pos a
  have hb := qmaFourAxisScale_pos b
  have hane : qmaFourAxisScale a ≠ 0 := ne_of_gt ha
  have hbne : qmaFourAxisScale b ≠ 0 := ne_of_gt hb
  have hden : 0 < 3*qmaFourAxisScale a*qmaFourAxisScale b := by positivity
  have hnon : 0 ≤ 8*|j|/(3*qmaFourAxisScale a*qmaFourAxisScale b) := by positivity
  rw [qmaFourCouplingSize,Real.sq_sqrt hnon]
  field_simp

theorem qmaFourCouplingSign_calibration (a b : Fin 2) (j : ℝ) :
    -(3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*
      (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b) = j := by
  have he := qmaFourCouplingSize_square a b j
  calc
    _ = -((3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*qmaFourAxisScale b)*
        qmaFourAxisSign (qmaFourCouplingSign j) := by ring
    _ = -|j| *qmaFourAxisSign (qmaFourCouplingSign j) := by rw [he]
    _ = j := by
      by_cases hj : j ≤ 0
      · simp [qmaFourAxisSign,qmaFourCouplingSign,hj,abs_of_nonpos hj]
      · simp [qmaFourAxisSign,qmaFourCouplingSign,hj,abs_of_pos (lt_of_not_ge hj)]

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

omit [Fintype σ] in
theorem qmaSiteMatrix_one (i : Q) : qmaSiteMatrix i (1 : Matrix σ σ ℂ) = 1 := by
  simp only [qmaSiteMatrix,ite_self,qmaTensorMatrix_one]

omit [Fintype σ] in
theorem qmaSiteMatrix_apply (i : Q) (A : Matrix σ σ ℂ) (s t : Q → σ) :
    qmaSiteMatrix i A s t = A (s i) (t i)*
      ∏ j ∈ Finset.univ.erase i, if s j = t j then (1:ℂ) else 0 := by
  unfold qmaSiteMatrix qmaTensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1,Matrix.one_apply]

omit [Fintype σ] in
theorem qmaSiteMatrix_add (i : Q) (A B : Matrix σ σ ℂ) :
    qmaSiteMatrix i (A+B) = qmaSiteMatrix i A+qmaSiteMatrix i B := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.add_apply,add_mul]

omit [Fintype σ] in
theorem qmaSiteMatrix_smul (i : Q) (c : ℂ) (A : Matrix σ σ ℂ) :
    qmaSiteMatrix i (c • A) = c • qmaSiteMatrix i A := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorGap
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

theorem qmaFourTensorEncoding_gram (n : ℕ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorEncoding n = 1 :=
  qmaTensorMatrix_gram _ (fun _ => qmaFourEncoding_gram)

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

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq Q] in
theorem qmaTensorMatrix_zero_at (A : Q → Matrix σ τ ℂ) (i : Q) (hA : A i = 0) :
    qmaTensorMatrix A = 0 := by
  ext s t
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hA])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorPair
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-block tensor placements and their exact algebra. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]

theorem qmaPairMatrix_eq_mul (i j : Q) (hij : i ≠ j) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j A B = qmaSiteMatrix i A*qmaSiteMatrix j B := by
  rw [qmaPairMatrix,qmaSiteMatrix,qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki,hkj]

theorem qmaPairMatrix_add_left (i j : Q) (hij : i ≠ j) (A B C : Matrix σ σ ℂ) :
    qmaPairMatrix i j (A+B) C = qmaPairMatrix i j A C+qmaPairMatrix i j B C := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_add,Matrix.add_mul]

theorem qmaPairMatrix_add_right (i j : Q) (hij : i ≠ j) (A B C : Matrix σ σ ℂ) :
    qmaPairMatrix i j A (B+C) = qmaPairMatrix i j A B+qmaPairMatrix i j A C := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_add,Matrix.mul_add]

theorem qmaPairMatrix_smul_left (i j : Q) (hij : i ≠ j) (r : ℂ) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j (r • A) B = r • qmaPairMatrix i j A B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_smul,Matrix.smul_mul]

theorem qmaPairMatrix_smul_right (i j : Q) (hij : i ≠ j) (r : ℂ) (A B : Matrix σ σ ℂ) :
    qmaPairMatrix i j A (r • B) = r • qmaPairMatrix i j A B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_smul,Matrix.mul_smul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorCross
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual inter-block Heisenberg columns in the many-block four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourTensorCross_column (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    qmaFourTensorCross i j p q*qmaFourTensorEncoding n =
      ∑ μ : Fin 3, qmaFourTensorPairColumn i j p q μ := by
  rw [qmaFourTensorCross,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Matrix.mul_assoc,qmaFourTensorEncoding,qmaSiteMatrix_tensor,qmaSiteMatrix_tensor,qmaFourTensorPairColumn]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki,hkj]

theorem qmaFourTensorPairColumn_gram (i j : Fin n)
    (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*qmaFourTensorPairColumn i j r s ν =
      if μ = ν then qmaPairMatrix i j (qmaFourCorrelation p r) (qmaFourCorrelation q s) else 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  by_cases hμ : μ = ν
  · subst ν
    rw [ite_eq_left rfl,qmaPairMatrix]
    congr 1
    funext k
    by_cases hki : k = i
    · simp only [hki,ite_true, if_true,qmaFourSpin_correlation]
    · by_cases hkj : k = j
      · subst k
        simp only [hki,ite_true, if_true,ite_false, if_false,qmaFourSpin_correlation]
      · simp only [hki,hkj,ite_false, if_false,qmaFourEncoding_gram]
  · rw [ite_eq_right hμ]
    apply qmaTensorMatrix_zero_at _ i
    simp only [ite_true, if_true,qmaFourSpin_correlation,hμ,ite_false, if_false]

theorem qmaFourTensorCross_gram (i j : Fin n) (hij : i ≠ j) (p q r s : Fin 4) :
    (qmaFourTensorCross i j p q*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCross i j r s*qmaFourTensorEncoding n) =
        (3:ℂ) • qmaPairMatrix i j (qmaFourCorrelation p r) (qmaFourCorrelation q s) := by
  rw [qmaFourTensorCross_column i j hij,qmaFourTensorCross_column i j hij]
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorPairColumn_gram i j,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,Finset.sum_const]
  norm_cast

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact one-block and two-block compression in the full tensor encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourTensor_site_compression (i : Fin n) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaSiteMatrix i A*qmaFourTensorEncoding n =
      qmaSiteMatrix i (qmaFourEncoding.conjTranspose*A*qmaFourEncoding) := by
  simp only [qmaFourTensorEncoding,qmaSiteMatrix,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases h : k = i
  · simp only [h,ite_true, if_true]
  · simp only [h,ite_false, if_false,Matrix.mul_one,qmaFourEncoding_gram]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOrthogonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct logical pairs have orthogonal first-excited columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourSpin_column_adjoint (p : Fin 4) (μ : Fin 3) :
    (qmaFourSpin p μ*qmaFourEncoding).conjTranspose*qmaFourEncoding = 0 := by
  rw [Matrix.conjTranspose_mul,qmaFourSpin_star]
  exact qmaFourSpin_orthogonal p μ

theorem qmaFourTensorPairColumn_unmatched_first (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ i
  simp only [ite_true, if_true,hik,hil,ite_false, if_false,qmaFourSpin_column_adjoint]

theorem qmaFourTensorPairColumn_unmatched_second (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hjl : j ≠ l) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  rw [qmaFourTensorPairColumn,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ j
  simp only [Ne.symm hij,ite_false, if_false,ite_true, if_true,hjk,hjl,qmaFourSpin_column_adjoint]

theorem qmaFourTensorPairColumn_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (p q r s : Fin 4) (μ ν : Fin 3) :
    (qmaFourTensorPairColumn i j p q μ).conjTranspose*
      qmaFourTensorPairColumn k l r s ν = 0 := by
  by_cases hi : i ∈ ({k,l} : Finset (Fin n))
  · by_cases hj : j ∈ ({k,l} : Finset (Fin n))
    · exfalso
      apply hne
      have hsub : ({i,j} : Finset (Fin n)) ⊆ {k,l} := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · simpa only [Finset.mem_singleton.mp hx] using hj
      exact Finset.eq_of_subset_of_card_le hsub (by simp [hij,hkl])
    · have hj' : j ≠ k ∧ j ≠ l := by simpa using hj
      exact qmaFourTensorPairColumn_unmatched_second i j k l hij hj'.1 hj'.2 p q r s μ ν
  · have hi' : i ≠ k ∧ i ≠ l := by simpa using hi
    exact qmaFourTensorPairColumn_unmatched_first i j k l hi'.1 hi'.2 p q r s μ ν

theorem qmaFourTensorCross_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (p q r s : Fin 4) :
    (qmaFourTensorCross i j p q*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCross k l r s*qmaFourTensorEncoding n) = 0 := by
  rw [qmaFourTensorCross_column i j hij,qmaFourTensorCross_column k l hkl]
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorPairColumn_distinct i j k l hij hkl hne,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTensorPairLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinearity of two-site placements in the finite tensor product. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q σ α : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ] [Fintype α]

omit [Fintype σ] in
theorem qmaSiteMatrix_sum (i : Q) (A : α → Matrix σ σ ℂ) :
    qmaSiteMatrix i (∑ a, A a) = ∑ a, qmaSiteMatrix i (A a) := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.sum_apply,Finset.sum_mul]

theorem qmaPairMatrix_sum_left (i j : Q) (hij : i ≠ j)
    (A : α → Matrix σ σ ℂ) (B : Matrix σ σ ℂ) :
    qmaPairMatrix i j (∑ a, A a) B = ∑ a, qmaPairMatrix i j (A a) B := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_sum,Matrix.sum_mul]

theorem qmaPairMatrix_sum_right (i j : Q) (hij : i ≠ j)
    (A : Matrix σ σ ℂ) (B : α → Matrix σ σ ℂ) :
    qmaPairMatrix i j A (∑ a, B a) = ∑ a, qmaPairMatrix i j A (B a) := by
  simp only [qmaPairMatrix_eq_mul _ _ hij,qmaSiteMatrix_sum,Matrix.mul_sum]

omit [Fintype α] in
theorem qmaPairMatrix_one_right (i j : Q) (hij : i ≠ j) (A : Matrix σ σ ℂ) :
    qmaPairMatrix i j A 1 = qmaSiteMatrix i A := by
  rw [qmaPairMatrix_eq_mul i j hij,qmaSiteMatrix_one,Matrix.mul_one]

omit [Fintype α] in
theorem qmaPairMatrix_one_left (i j : Q) (hij : i ≠ j) (A : Matrix σ σ ℂ) :
    qmaPairMatrix i j 1 A = qmaSiteMatrix j A := by
  rw [qmaPairMatrix_eq_mul i j hij,qmaSiteMatrix_one,Matrix.one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factorized Heisenberg couplings in the full many-block tensor code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourTensorWeighted_gram (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) =
        (3:ℂ) • qmaPairMatrix i j (qmaFourWeightedCorrelation a) (qmaFourWeightedCorrelation b) := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,Matrix.mul_sum,Matrix.mul_smul,smul_smul,
    Complex.star_def,Complex.conj_ofReal,qmaFourTensorCross_gram i j hij,qmaFourWeightedCorrelation,
    qmaPairMatrix_sum_left _ _ hij,qmaPairMatrix_sum_right _ _ hij,
    qmaPairMatrix_smul_left _ _ hij,qmaPairMatrix_smul_right _ _ hij,Finset.smul_sum,smul_smul]
  have hswap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 →
      Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
      (∑ p, ∑ q, ∑ r, ∑ s, f p q r s) = ∑ p, ∑ r, ∑ q, ∑ s, f p q r s := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  rw [qmaFourCorrelation_comm s q,qmaFourCorrelation_comm r p]
  congr 1
  push_cast
  ring

theorem qmaFourTensorWeighted_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (a b c d : Fin 4 → ℝ) :
    (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorWeighted k l c d*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_distinct i j k l hij hkl hne,smul_zero,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorEffective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical counterterms calibrate each edge of the full tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourTensorEffective_tensor (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorEffective i j a b t = (-qmaFourCouplingFactor a b t:ℂ) •
      qmaPairMatrix i j
        ((qmaFourAxisShift a true:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
          (qmaFourAxisScale a:ℂ) • qmaFourAxis a)
        ((qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
          ((qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b:ℝ):ℂ) • qmaFourAxis b) := by
  rw [qmaFourTensorEffective,qmaFourTensorCoupling,Matrix.smul_mul,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_smul]
  rw [qmaFourTensorWeighted_gram i j hij,qmaFourAxisWeights_correlation,qmaFourAxisWeights_correlation]
  simp only [qmaFourAxisSign,ite_true, if_true,one_mul,Complex.star_def,Complex.conj_ofReal,
    smul_smul,qmaFourCouplingFactor]
  push_cast
  congr 1
  ring

theorem qmaFourTensorEffective_expansion (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorEffective i j a b t =
      (-qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)+
      (-qmaFourCouplingFactor a b t*qmaFourAxisScale a*
        qmaFourAxisShift b (qmaFourCouplingSign t):ℂ) • qmaSiteMatrix i (qmaFourAxis a)+
      (-qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
        (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b):ℂ) • qmaSiteMatrix j (qmaFourAxis b)+
      (t:ℂ) • qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b) := by
  have hc : (-qmaFourCouplingFactor a b t*qmaFourAxisScale a*
      (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b):ℂ) = t := by
    have h := qmaFourCouplingSign_calibration a b t
    have he : -qmaFourCouplingFactor a b t*qmaFourAxisScale a*
        (qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisScale b) = t := by
      unfold qmaFourCouplingFactor
      nlinarith [h]
    exact_mod_cast he
  rw [← hc,qmaFourTensorEffective_tensor i j hij]
  simp only [qmaPairMatrix_add_left _ _ hij,qmaPairMatrix_add_right _ _ hij,
    qmaPairMatrix_smul_left _ _ hij,qmaPairMatrix_smul_right _ _ hij,
    qmaPairMatrix_one_right _ _ hij,qmaPairMatrix_one_left _ _ hij,qmaSiteMatrix_one,
    smul_add,smul_smul]
  push_cast
  module

theorem qmaFourTensorCounterterm_effective (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorCounterterm i j a b t*qmaFourTensorEncoding n+
      qmaFourTensorEffective i j a b t =
      (t:ℂ) • qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)+
      (qmaFourEnergyOffset a b t:ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  rw [qmaFourTensorCounterterm,Matrix.mul_add,Matrix.add_mul,
    qmaFourTensor_site_compression,qmaFourTensor_site_compression,
    qmaFourAxisField_compression,qmaFourAxisField_compression,qmaFourTensorEffective_expansion i j hij]
  simp only [qmaSiteMatrix_add,qmaSiteMatrix_smul,qmaSiteMatrix_one,
    qmaFourEnergyOffset,qmaFourCounterA,qmaFourCounterB]
  push_cast
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact effective Hamiltonian of a family of distinct logical edges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ τ κ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [DecidableEq κ]

omit [Fintype τ] [DecidableEq κ] in
theorem qmaOrthogonalColumns_sum_gram (W : κ → Matrix σ τ ℂ)
    (hW : ∀ e f, e ≠ f → (W e).conjTranspose*W f = 0) :
    (∑ e, W e).conjTranspose*(∑ e, W e) = ∑ e, (W e).conjTranspose*W e := by
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_eq_single e
  · intro f _ hfe
    exact hW f e hfe
  · intro he
    exact (he (Finset.mem_univ e)).elim

variable {n : ℕ}

theorem qmaFourTensorCoupling_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (a b c d : Fin 2) (t u : ℝ) :
    (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCoupling k l c d u*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.conjTranspose_smul,
    Matrix.mul_smul,qmaFourTensorWeighted_distinct i j k l hij hkl hne,smul_zero]

omit [DecidableEq κ] in
theorem qmaFourTensorFamily_effective (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f}) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorFamilyCounterterm left right a b t*
        qmaFourTensorEncoding n +
      (-1/8:ℂ) • ((qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n).conjTranspose*
        (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n)) =
      (∑ e, (t e:ℂ) • qmaPairMatrix (left e) (right e) (qmaFourAxis (a e)) (qmaFourAxis (b e)))+
      ((∑ e, qmaFourEnergyOffset (a e) (b e) (t e):ℝ):ℂ) •
        (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  have hW (e f : κ) (hef : e ≠ f) :
      (qmaFourTensorCoupling (left e) (right e) (a e) (b e) (t e)*qmaFourTensorEncoding n).conjTranspose*
        (qmaFourTensorCoupling (left f) (right f) (a f) (b f) (t f)*qmaFourTensorEncoding n) = 0 :=
    qmaFourTensorCoupling_distinct _ _ _ _ (hneq e) (hneq f) (hdist e f hef) _ _ _ _ _ _
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul]
  rw [qmaOrthogonalColumns_sum_gram _ hW]
  simp only [qmaFourTensorFamilyCounterterm,Matrix.mul_sum,Matrix.sum_mul,Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  have he (e : κ) := qmaFourTensorCounterterm_effective (left e) (right e) (hneq e) (a e) (b e) (t e)
  simp only [qmaFourTensorEffective] at he
  simp only [he,Finset.sum_add_distrib,← Finset.sum_smul,Complex.ofReal_sum]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFamilyAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial-precision simulator for an arbitrary family of distinct X/Z pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaFourTensorFamily_effective_eq (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f}) :
    qmaFourTensorEffectiveMatrix (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFamilyCounterterm left right a b t) = qmaFourTensorFamilyTarget left right a b t := by
  have h := qmaFourTensorFamily_effective left right a b t hneq hdist
  change _ = qmaFourTensorFamilyTarget left right a b t at h
  rw [qmaFourTensorEffectiveMatrix]
  rw [← h]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOnsite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal physical exchanges encode the one-site and scalar X/Z terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {τ : Type*} [Fintype τ]

theorem qmaFourTensorOnsite_compression (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorOnsite site axis weight constant*qmaFourTensorEncoding n =
      (∑ e, (weight e:ℂ) • qmaSiteMatrix (site e) (qmaFourAxis (axis e)))+(constant:ℂ) • 1 := by
  simp only [qmaFourTensorOnsite,qmaFourTensorFields,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sum,Matrix.sum_mul,qmaFourTensor_site_compression,qmaFourAxisField_compression,
    qmaSiteMatrix_add,qmaSiteMatrix_smul,qmaSiteMatrix_one,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,qmaFourTensorEncoding_gram,Finset.sum_add_distrib,← Finset.sum_smul]
  simp only [← Complex.ofReal_sum,qmaFourTensorFieldShift]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFullFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full X/Z families, including scalar and one-site terms, have polynomial simulators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaFourTensorFull_effective_oai (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    qmaFourTensorEffectiveMatrix (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFullCounterterm left right a b t site axis weight constant) =
        qmaFourTensorFullTarget left right a b t site axis weight constant := by
  rw [qmaFourTensorFullTarget,← qmaFourTensorFamily_effective_eq left right a b t hneq hdist]
  simp only [qmaFourTensorEffectiveMatrix,qmaFourTensorFullCounterterm,Matrix.mul_add,Matrix.add_mul]
  rw [qmaFourTensorOnsite_compression]
  abel

end ContinuumCoulomb

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ContinuumCoulomb.qmaFourTensorFull_effective_oai.{u_1, u_2} := @OAI.ContinuumCoulomb.qmaFourTensorFull_effective_oai.{u_1, u_2}
