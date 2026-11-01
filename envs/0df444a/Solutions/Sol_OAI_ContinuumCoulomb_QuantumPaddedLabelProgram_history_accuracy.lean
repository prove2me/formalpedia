-- Prove2me | solution 1 for OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.history_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:39:40.496716+00:00
-- url     : https://prove2.me/submissions/4eddd7cb-d9ee-4473-b40f-ec523690a533

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
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.Order.Interval.Finset.Nat
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
import Definitions.Def_OAIQ092A010
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumOrderedXZ_threeEnergy_error
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensorFull_accuracy_of_budget
import Theorems.Thm_OAI_ContinuumCoulomb_qmaThirdGadget_polynomial_accuracy
import Theorems.Thm_OAI_ContinuumCoulomb_qmaXZSubdivision_accuracy

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_HubbardFermionSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

end ContinuumCoulomb.HubbardGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourcePauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-site Pauli matrices on the complete source spin basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem pauli_sq (μ : Fin 3) : pauli μ * pauli μ = 1 := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sourceLocalPauli_sq (n : ℕ) (i : Fin n) (μ : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n i μ = 1 := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul]
  have h (k : Fin n) :
      (if k = i then pauli μ else 1) * (if k = i then pauli μ else 1) = 1 := by
    by_cases hki : k = i <;> simp [hki, pauli_sq]
  simp_rw [h]
  exact sourceTensor_one n

/-- The Pauli contraction on two actual two-state spins. -/
theorem pauli_entry_sum (a b c d : Fin 2) :
    (∑ μ : Fin 3, pauli μ a c * pauli μ b d) =
      2 * (if a = d ∧ b = c then (1 : ℂ) else 0) -
        (if a = c ∧ b = d then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_succ]

theorem sourceSpinSwap_eq_iff {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (s t : SourceSpinBasis n) :
    sourceSpinSwap i j s = t ↔ s j = t i ∧ s i = t j ∧
      ∀ k, k ≠ i → k ≠ j → s k = t k := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceSpinSwap_apply] using congrFun h i
    · simpa [sourceSpinSwap_apply] using congrFun h j
    · intro k hki hkj
      simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using congrFun h k
  · rintro ⟨hi, hj, hrest⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa [sourceSpinSwap_apply] using hi
    · by_cases hkj : k = j
      · subst k
        simpa [sourceSpinSwap_apply] using hj
      · simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hrest k hki hkj

/-- The Pauli sum on distinct sites equals the complete source Hamiltonian
matrix, with every other spin acting as an untouched spectator. -/
theorem sourceLocalPauli_sum (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ μ : Fin 3, sourceLocalPauli n i μ * sourceLocalPauli n j μ) =
      sourceHeisenbergMatrix n i j := by
  classical
  ext s t
  rw [Matrix.sum_apply]
  simp_rw [sourceLocalPauli_product_entry n i j hij]
  rw [← Finset.sum_mul, pauli_entry_sum]
  by_cases hrest : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [sourceSpectatorDelta_eq_one n i j s t hrest, mul_one]
    have hsame : s = t ↔ s i = t i ∧ s j = t j := by
      constructor
      · intro h
        exact ⟨congrFun h i, congrFun h j⟩
      · rintro ⟨hi, hj⟩
        funext k
        by_cases hki : k = i
        · simpa [hki] using hi
        · by_cases hkj : k = j
          · simpa [hkj] using hj
          · exact hrest k hki hkj
    have hswap : sourceSpinSwap i j s = t ↔ s i = t j ∧ s j = t i := by
      rw [sourceSpinSwap_eq_iff i j hij]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hrest⟩⟩
    change _ = 2 * (if sourceSpinSwap i j s = t then (1 : ℂ) else 0) -
      (if s = t then 1 else 0)
    simp only [hswap, hsame]
  · rw [sourceSpectatorDelta_eq_zero n i j s t hrest, mul_zero]
    have hswap : sourceSpinSwap i j s ≠ t := by
      intro h
      exact hrest ((sourceSpinSwap_eq_iff i j hij s t).mp h).2.2
    have hsame : s ≠ t := by
      intro h
      apply hrest
      intro k _ _
      exact congrFun h k
    simp [sourceHeisenbergMatrix, hswap, hsame]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_SpinMatrixNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.spinMatrixOperator_diagonal _root_.OAI.ContinuumCoulomb.spinMatrixOperator_sub _root_.OAI.ContinuumCoulomb.spinMatrixOperator_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem spinMatrixOperator_sum {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ) :
    spinMatrixOperator (∑ k ∈ s, M k) = ∑ k ∈ s, spinMatrixOperator (M k) := by
  unfold spinMatrixOperator
  rw [map_sum, map_sum]

theorem spinMatrixOperator_unitary_norm_map (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) (x : EuclideanSpace ℂ ι) :
    ‖spinMatrixOperator M x‖ = ‖x‖ := by
  have hcomp : (spinMatrixOperator M).adjoint.comp (spinMatrixOperator M) = 1 := by
    rw [← spinMatrixOperator_star, ← spinMatrixOperator_mul, hM, spinMatrixOperator_one]
  have hsq : ‖spinMatrixOperator M x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hcomp]
    simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem spinMatrixOperator_unitary_norm (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) : ‖spinMatrixOperator M‖ ≤ 1 := by
  apply (spinMatrixOperator M).opNorm_le_bound zero_le_one
  intro x
  rw [spinMatrixOperator_unitary_norm_map M hM, one_mul]

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

theorem sourceLocalPauli_operator_norm (n : ℕ) (i : Fin n) (μ : Fin 3) :
    ‖spinMatrixOperator (sourceLocalPauli n i μ)‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [sourceLocalPauli_star, sourceLocalPauli_sq]

theorem sourceHeisenbergMatrix_operator_norm (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ‖spinMatrixOperator (sourceHeisenbergMatrix n i j)‖ ≤ 3 := by
  rw [← sourceLocalPauli_sum n i j hij, spinMatrixOperator_sum]
  simp only [spinMatrixOperator_mul]
  calc
    _ ≤ ∑ μ : Fin 3, ‖(spinMatrixOperator (sourceLocalPauli n i μ)).comp
        (spinMatrixOperator (sourceLocalPauli n j μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (sourceLocalPauli_operator_norm n i μ)
          (sourceLocalPauli_operator_norm n j μ) (norm_nonneg _) zero_le_one).trans_eq
            (one_mul _))
    _ = 3 := by norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

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

theorem submatrix_smul_apply {ι κ α β : Type*} (c : ℂ) (M : Matrix ι κ ℂ)
    (f : α → ι) (g : β → κ) : (c • M).submatrix f g = c • M.submatrix f g := rfl

theorem sum_kronecker {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (N : Matrix α β ℂ) :
    (∑ e, M e) ⊗ₖ N = ∑ e, M e ⊗ₖ N := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem reindex_operator_apply (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (spinMatrixOperator (H.submatrix e e) x) =
      spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) := by
  ext k
  change (∑ j, H (e (e.symm k)) (e j) * x j) = ∑ j, H k j * x (e.symm j)
  simp only [Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using
    e.sum_comp (fun j => H k j * x (e.symm j))

theorem reindex_form (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    ⟪x, spinMatrixOperator (H.submatrix e e) x⟫_ℝ =
      ⟪LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x,
        spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x)⟫_ℝ := by
  rw [← reindex_operator_apply]
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  exact congrArg Complex.re
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).inner_map_map x
      (spinMatrixOperator (H.submatrix e e) x)).symm

theorem normalizedBottom_reindex (e : ι ≃ κ) (H : Matrix κ κ ℂ) :
    normalizedBottom (H.submatrix e e) = normalizedBottom H := by
  unfold normalizedBottom
  congr 1
  ext a
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨U x, (U.norm_map x).trans hx, reindex_form e H x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.symm x, (U.symm.norm_map x).trans hx, ?_⟩
    rw [reindex_form]
    change ⟪x, spinMatrixOperator H x⟫_ℝ = ⟪U (U.symm x), spinMatrixOperator H (U (U.symm x))⟫_ℝ
    rw [U.apply_symm_apply]

end Reindex

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |(value (b, q) : ℝ) - Real.sqrt (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  have h := DyadicRootProgram.value_error b q.num.toNat q.den q.pos
  rw [hre] at h
  change |(DyadicRootProgram.value b q.num.toNat q.den : ℝ) - Real.sqrt (q : ℝ)| ≤ _
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2.le.trans_eq (by simp only [one_div, inv_pow])

theorem sqrt_perturbation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  apply Real.abs_le_sqrt
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  by_cases hab : a ≤ b
  · have hs := Real.sqrt_le_sqrt hab
    have hm := mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hs)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt (le_of_not_ge hab)
    have hm := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
    nlinarith

end ContinuumCoulomb.RationalSquareRoot

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli expansion on the bounded supports of the circuit terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauli_hermitian (i : Fin 4) : (qmaPauli i).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaPauli,pauli,pauliX,pauliY,pauliZ]

theorem qmaPauli_kernel (a b c d : Fin 2) :
    (∑ i : Fin 4, qmaPauli i a b*qmaPauli i c d) =
      2*(if a = d ∧ c = b then (1:ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [qmaPauli,pauli,pauliX,pauliY,pauliZ,Fin.sum_univ_succ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qmaPauliWord_hermitian (w : ι → Fin 4) : (qmaPauliWord w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  change star (∏ i, qmaPauli (w i) (t i) (s i)) = ∏ i, qmaPauli (w i) (s i) (t i)
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (qmaPauli_hermitian (w i)).apply _ _

theorem qmaPauliWord_kernel (s t u v : ι → Fin 2) :
    (∑ w : ι → Fin 4, qmaPauliWord w s t*qmaPauliWord w u v) =
      (2:ℂ)^Fintype.card ι*(if s = v ∧ u = t then 1 else 0) := by
  simp only [qmaPauliWord,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (i : ι) (a : Fin 4) =>
    qmaPauli a (s i) (t i)*qmaPauli a (u i) (v i))]
  simp only [qmaPauli_kernel,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  congr 1
  by_cases hs : s = v
  · subst v
    by_cases hu : u = t
    · subst u
      simp
    · rw [ite_eq_right (by simp [hu])]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · rw [ite_eq_right (by simp [hs])]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicScalar
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_neg _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar arithmetic for the H,T,CNOT history compiler.  A real
scalar is a+b/sqrt(2); a complex scalar consists of two such pairs.  The
representation is rational data throughout, including multiplication. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

theorem sample_error (k : ℕ) (x : RealScalar) :
    |(sample k x:ℝ)-realValue x| ≤ |(x.2:ℝ)| * (2:ℝ)⁻¹^k := by
  have h := RationalSquareRoot.value_error k (q := 1/2) (by norm_num)
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  have he : (sample k x:ℝ)-realValue x =
      (x.2:ℝ)*((RationalSquareRoot.value (k,1/2):ℝ)-Real.sqrt (1/2:ℝ)) := by
    simp only [sample,realValue,Rat.cast_add,Rat.cast_mul]
    ring
  rw [he,abs_mul]
  simpa only [one_div] using mul_le_mul_of_nonneg_left h (abs_nonneg (x.2:ℝ))

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient-height bounds for the fixed history expressions.
These bounds provide a polynomial precision budget before real evaluation. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar
open scoped BigOperators

theorem realHeight_nonnegative (x : RealScalar) : 0 ≤ realHeight x :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem height_nonnegative (x : Scalar) : 0 ≤ height x :=
  add_nonneg (realHeight_nonnegative _) (realHeight_nonnegative _)

theorem realHeight_add (x y : RealScalar) :
    realHeight (realAdd x y) ≤ realHeight x+realHeight y := by
  have ha := abs_add_le x.1 y.1
  have hb := abs_add_le x.2 y.2
  dsimp only [realHeight,realAdd]
  linarith

theorem realHeight_sub (x y : RealScalar) :
    realHeight (realSub x y) ≤ realHeight x+realHeight y := by
  simpa only [realSub,realHeight_neg] using realHeight_add x (realNeg y)

theorem realHeight_mul (x y : RealScalar) :
    realHeight (realMul x y) ≤ realHeight x*realHeight y := by
  have ha := abs_add_le (x.1*y.1) (x.2*y.2/2)
  have hb := abs_add_le (x.1*y.2) (x.2*y.1)
  norm_num only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℚ) < 2)] at ha hb
  dsimp only [realHeight,realMul]
  nlinarith [mul_nonneg (abs_nonneg x.2) (abs_nonneg y.2)]

theorem height_add (x y : Scalar) : height (add x y) ≤ height x+height y := by
  have ha := realHeight_add x.1 y.1
  have hb := realHeight_add x.2 y.2
  dsimp only [height,add]
  linarith

theorem height_sub (x y : Scalar) : height (sub x y) ≤ height x+height y := by
  simpa only [sub,height_neg] using height_add x (neg y)

theorem height_mul (x y : Scalar) : height (mul x y) ≤ height x*height y := by
  have hr := realHeight_sub (realMul x.1 y.1) (realMul x.2 y.2)
  have hi := realHeight_add (realMul x.1 y.2) (realMul x.2 y.1)
  have hrr := realHeight_mul x.1 y.1
  have hii := realHeight_mul x.2 y.2
  have hri := realHeight_mul x.1 y.2
  have hir := realHeight_mul x.2 y.1
  dsimp only [height,mul]
  nlinarith

theorem height_realPart (x : Scalar) : height (realPart x) ≤ height x := by
  simp only [height,realPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_right (realHeight_nonnegative _)

theorem height_imagPart (x : Scalar) : height (imagPart x) ≤ height x := by
  simp only [height,imagPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_left (realHeight_nonnegative _)

theorem height_sum (xs : List Scalar) : height (sum xs) ≤ (xs.map height).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    change height (add x (sum xs)) ≤ height x+(xs.map height).sum
    exact (height_add x (sum xs)).trans (add_le_add (le_refl (height x)) ih)

theorem height_product (xs : List Scalar) : height (product xs) ≤ (xs.map height).prod := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih =>
    change height (mul x (product xs)) ≤ height x*(xs.map height).prod
    exact (height_mul x (product xs)).trans
      (mul_le_mul_of_nonneg_left ih (height_nonnegative x))

theorem sample_error_height (k : ℕ) (x : RealScalar) :
    |(sample k x:ℝ)-realValue x| ≤ (realHeight x:ℝ)*(2:ℝ)⁻¹^k := by
  apply (sample_error k x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h : |x.2| ≤ realHeight x := le_add_of_nonneg_left (abs_nonneg _)
  exact_mod_cast h

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliExpansion
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the actual small local matrices in the Pauli basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauli_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    (∑ w : ι → Fin 4, qmaPauliCoefficient A w • qmaPauliWord w) = A := by
  ext i j
  have hswap :
      (∑ w : ι → Fin 4, ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
        A s t*(qmaPauliWord w i j*qmaPauliWord w t s)) =
      ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, ∑ w : ι → Fin 4,
        A s t*(qmaPauliWord w i j*qmaPauliWord w t s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  calc
    _ = ((2:ℂ)^Fintype.card ι)⁻¹ *
        ∑ w : ι → Fin 4, ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
          A s t*(qmaPauliWord w i j*qmaPauliWord w t s) := by
      simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,qmaPauliCoefficient,
        Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ((2:ℂ)^Fintype.card ι)⁻¹ *
        ∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
          A s t*(∑ w : ι → Fin 4, qmaPauliWord w i j*qmaPauliWord w t s) := by
      rw [hswap]
      simp only [Finset.mul_sum]
    _ = A i j := by
      simp_rw [qmaPauliWord_kernel]
      simp only [mul_ite,ite_and,mul_one,mul_zero,Finset.sum_ite_irrel,
        Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
      have hp : (2:ℂ)^Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hermitian local matrices have real Pauli coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliCoefficient_star (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) (w : ι → Fin 4) :
    star (qmaPauliCoefficient A w) = qmaPauliCoefficient A w := by
  have hs : star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) =
      ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s := by
    calc
      _ = ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A t s*qmaPauliWord w s t := by
        simp only [star_sum,star_mul,hA.apply,(qmaPauliWord_hermitian w).apply]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := Finset.sum_comm
  simp [qmaPauliCoefficient,hs]

theorem qmaPauliCoefficient_real (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) (w : ι → Fin 4) : (qmaPauliCoefficient A w).im = 0 := by
  have h := congrArg Complex.im (qmaPauliCoefficient_star A hA w)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

theorem qmaPauli_real_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : A.IsHermitian) :
    (∑ w : ι → Fin 4, ((qmaPauliCoefficient A w).re : ℂ) • qmaPauliWord w) = A := by
  have he (w : ι → Fin 4) : ((qmaPauliCoefficient A w).re : ℂ) = qmaPauliCoefficient A w := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (qmaPauliCoefficient_real A hA w).symm
  simp only [he,qmaPauli_expansion]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity Pauli traces evaluated entirely in rational registers.
The interpretation is the actual complex Pauli coefficient, not an
assumed list of Hamiltonian coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar Matrix
open scoped BigOperators Classical

theorem value_finiteSum {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteSum f) = ∑ a, value (f a) := by
  simp only [finiteSum,value_sum,enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp (fun a => value (f a))

theorem value_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteProduct f) = ∏ a, value (f a) := by
  simp only [finiteProduct,value_product,enumerate,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun a => value (f a))

theorem value_pauli (μ : Fin 4) (a b : Fin 2) :
    value (pauli μ a b) = qmaPauli μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,qmaPauli,pauliX,pauliY,pauliZ]

theorem value_word {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → Fin 4) (s t : ι → Fin 2) :
    value (word w s t) = qmaPauliWord w s t := by
  rw [word,value_finiteProduct]
  simp only [value_pauli,qmaPauliWord]

theorem value_coefficient {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) :
    value (coefficient A w) = qmaPauliCoefficient (fun s t => value (A s t)) w := by
  simp only [coefficient,value_mul,value_rat,value_finiteSum,value_word,
    qmaPauliCoefficient,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]
  norm_num
  apply Finset.sum_congr (by ext; simp)
  intro s _
  apply Finset.sum_congr (by ext; simp)
  intro t _
  rfl

theorem realCoefficient_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4) :
    realValue (realCoefficient A w) =
      (qmaPauliCoefficient (fun s t => value (A s t)) w).re := by
  rw [← value_coefficient]
  exact (value_re _).symm

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalCore
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small support matrix is recovered canonically by fixing every
spectator qubit to zero, preserving real entries and Hermiticity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalCore_lift (S : Finset ι)
    (B : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalCore S (qmaLocalLift S B) = B := by
  ext u v
  change qmaLocalLift S B (qmaSupportExtend S u) (qmaSupportExtend S v) = B u v
  rw [qmaLocalLift_apply]
  have hs (u : QMASupportBasis S) :
      (fun i : {i // i ∈ S} => qmaSupportExtend S u i.val) = u := by
    funext i
    simp [qmaSupportExtend,i.property]
  have hr : (fun i : {i // i ∉ S} => qmaSupportExtend S u i.val) =
      (fun i : {i // i ∉ S} => qmaSupportExtend S v i.val) := by
    funext i
    simp [qmaSupportExtend,i.property]
  rw [hs,hs,ite_eq_left hr,mul_one]

theorem QMALocalOn.core_lift {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) : qmaLocalLift S (qmaLocalCore S A) = A := by
  obtain ⟨B,rfl⟩ := hA
  rw [qmaLocalCore_lift]

omit [Fintype ι] in
theorem qmaLocalCore_hermitian (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) : (qmaLocalCore S A).IsHermitian :=
  hA.submatrix (qmaSupportExtend S)

omit [Fintype ι] in
theorem qmaLocalCore_real (S : Finset ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : ∀ s t, (A s t).im = 0) (u v : QMASupportBasis S) :
    (qmaLocalCore S A u v).im = 0 := hA _ _

theorem qmaLocalLift_zero (S : Finset ι) :
    qmaLocalLift S (0 : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) = 0 := by
  ext s t
  simp [qmaLocalLift_apply]

theorem qmaLocalLift_sum {κ : Type*} [Fintype κ] (S : Finset ι)
    (B : κ → Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) :
    qmaLocalLift S (∑ i, B i) = ∑ i, qmaLocalLift S (B i) := by
  have hs (s : Finset κ) : qmaLocalLift S (∑ i ∈ s, B i) = ∑ i ∈ s, qmaLocalLift S (B i) := by
    induction s using Finset.induction_on with
    | empty => simp [qmaLocalLift_zero]
    | @insert a s ha ih => simp only [Finset.sum_insert ha,qmaLocalLift_add,ih]
  exact hs Finset.univ

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliParity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real Hermitian matrix contains only Pauli words with an even number
of imaginary Y factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauli_conjugate (i : Fin 4) (a b : Fin 2) :
    star (qmaPauli i a b) = qmaPauliSign i*qmaPauli i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [qmaPauli,qmaPauliSign,pauliX,pauliY,pauliZ, Fin.ext_iff] <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qmaPauliWord_conjugate (w : ι → Fin 4) (s t : ι → Fin 2) :
    star (qmaPauliWord w s t) = (-1:ℂ)^qmaPauliYCount w*qmaPauliWord w s t := by
  simp only [qmaPauliWord,star_prod,qmaPauli_conjugate,Finset.prod_mul_distrib]
  congr 1
  simp [qmaPauliSign,qmaPauliYCount,Finset.prod_ite]

theorem qmaPauliCoefficient_conjugate_of_real
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : ∀ s t, (A s t).im = 0)
    (w : ι → Fin 4) :
    star (qmaPauliCoefficient A w) = (-1:ℂ)^qmaPauliYCount w*qmaPauliCoefficient A w := by
  have ha (s t : ι → Fin 2) : star (A s t) = A s t := by
    apply Complex.ext
    · rfl
    · simp [hA]
  have hs : star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) =
      (-1:ℂ)^qmaPauliYCount w*(∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) := by
    simp only [star_sum,star_mul,ha,qmaPauliWord_conjugate,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hi : star (((2:ℂ)^Fintype.card ι)⁻¹) = ((2:ℂ)^Fintype.card ι)⁻¹ := by
    change (starRingEnd ℂ) (((2:ℂ)^Fintype.card ι)⁻¹) = _
    rw [map_inv₀,map_pow]
    have h2 : (starRingEnd ℂ) (2:ℂ) = 2 := by simp only [starRingEnd_apply]; norm_num
    rw [h2]
  unfold qmaPauliCoefficient
  calc
    _ = star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s)*
        star (((2:ℂ)^Fintype.card ι)⁻¹) := star_mul _ _
    _ = ((-1:ℂ)^qmaPauliYCount w*(∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
        A s t*qmaPauliWord w t s))*((2:ℂ)^Fintype.card ι)⁻¹ := congrArg₂ (· * ·) hs hi
    _ = _ := by ring

theorem qmaPauliCoefficient_odd_zero (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0)
    (w : ι → Fin 4) (hw : Odd (qmaPauliYCount w)) : qmaPauliCoefficient A w = 0 := by
  have hs := qmaPauliCoefficient_conjugate_of_real A hR w
  rw [qmaPauliCoefficient_star A hH w,hw.neg_one_pow] at hs
  have he : (2:ℂ)*qmaPauliCoefficient A w = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliAlgebra
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Pauli factors used by the mediator gadgets are Hermitian
involutions, and disjoint factors commute exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauli_zero : qmaPauli 0 = 1 := rfl

theorem qmaPauli_square (i : Fin 4) : qmaPauli i*qmaPauli i = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaPauli,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliWord_mul_apply (w v : ι → Fin 4) (s t : ι → Fin 2) :
    (qmaPauliWord w*qmaPauliWord v) s t =
      ∏ i, (qmaPauli (w i)*qmaPauli (v i)) (s i) (t i) := by
  change (∑ r : ι → Fin 2, (∏ i, qmaPauli (w i) (s i) (r i))*(∏ i, qmaPauli (v i) (r i) (t i))) = _
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => qmaPauli (w i) (s i) a*qmaPauli (v i) a (t i))).symm

theorem qmaPauliWord_square (w : ι → Fin 4) : qmaPauliWord w*qmaPauliWord w = 1 := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  simp only [qmaPauli_square,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem qmaPauliWord_gram (w : ι → Fin 4) :
    (qmaPauliWord w).conjTranspose*qmaPauliWord w = 1 := by
  rw [qmaPauliWord_hermitian w,qmaPauliWord_square]

theorem qmaPauliWord_disjoint_commute (w v : ι → Fin 4)
    (h : ∀ i, w i = 0 ∨ v i = 0) : qmaPauliWord w*qmaPauliWord v = qmaPauliWord v*qmaPauliWord w := by
  ext s t
  rw [qmaPauliWord_mul_apply,qmaPauliWord_mul_apply]
  apply Finset.prod_congr rfl
  intro i _
  rcases h i with hi | hi <;> simp [hi,qmaPauli_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact supports and tensor joins of the Pauli words used in the reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem qmaPauliWord_join (w : ι → Fin 4) (v : κ → Fin 4) :
    qmaJoinMatrix (qmaPauliWord w) (qmaPauliWord v) = qmaPauliWord (Sum.elim w v) := by
  ext s t
  change (∏ i, qmaPauli (w i) (s (Sum.inl i)) (t (Sum.inl i)))*
    (∏ k, qmaPauli (v k) (s (Sum.inr k)) (t (Sum.inr k))) =
      ∏ a : ι ⊕ κ, qmaPauli (Sum.elim w v a) (s a) (t a)
  rw [Fintype.prod_sum_type]
  rfl

theorem qmaPauliSupport_join (w : ι → Fin 4) (v : κ → Fin 4) :
    qmaPauliSupport (Sum.elim w v) =
      (qmaPauliSupport w).map Function.Embedding.inl ∪
      (qmaPauliSupport v).map Function.Embedding.inr := by
  ext a
  cases a <;> simp [qmaPauliSupport]

theorem qmaPauliSupport_join_card (w : ι → Fin 4) (v : κ → Fin 4) :
    (qmaPauliSupport (Sum.elim w v)).card = (qmaPauliSupport w).card+(qmaPauliSupport v).card := by
  rw [qmaPauliSupport_join,Finset.card_union_of_disjoint,Finset.card_map,Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp ha
  obtain ⟨k,_,hk⟩ := Finset.mem_map.mp hb
  exact Sum.inl_ne_inr (hi.trans hk.symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliSplit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced disjoint factorizations for the two subdivision stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliRestrict_commute (S T : Finset ι) (w : ι → Fin 4) (hST : Disjoint S T) :
    qmaPauliWord (qmaPauliRestrict S w)*qmaPauliWord (qmaPauliRestrict T w) =
      qmaPauliWord (qmaPauliRestrict T w)*qmaPauliWord (qmaPauliRestrict S w) := by
  apply qmaPauliWord_disjoint_commute
  intro i
  by_cases hi : i ∈ S
  · right
    have ht : i ∉ T := fun ht => Finset.disjoint_left.mp hST hi ht
    simp [qmaPauliRestrict,ht]
  · left
    simp [qmaPauliRestrict,hi]

theorem qmaPauliRestrict_factor (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T) :
    qmaPauliWord (qmaPauliRestrict S w)*qmaPauliWord (qmaPauliRestrict T w) = qmaPauliWord w := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i ∈ S
  · have ht : i ∉ T := fun ht => Finset.disjoint_left.mp hST hs ht
    simp [qmaPauliRestrict,hs,ht,qmaPauli_zero]
  · by_cases ht : i ∈ T
    · simp [qmaPauliRestrict,hs,ht,qmaPauli_zero]
    · have hw : w i = 0 := by
        by_contra h
        have hm := hcover (show i ∈ qmaPauliSupport w by simp [qmaPauliSupport,h])
        simp [hs,ht] at hm
      simp [qmaPauliRestrict,hs,ht,hw,qmaPauli_zero]

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

theorem qmaMatrixOperator_mul [DecidableEq γ] (M : Matrix α β ℂ) (N : Matrix β γ ℂ) :
    qmaMatrixOperator (M*N) = (qmaMatrixOperator M).comp (qmaMatrixOperator N) := by
  ext x a
  change Matrix.toLpLin 2 2 (M*N) x a = Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) a
  rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]

theorem qmaMatrixOperator_star (M : Matrix α β ℂ) :
    qmaMatrixOperator M.conjTranspose = (qmaMatrixOperator M).adjoint := by
  unfold qmaMatrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

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

theorem qmaMatrixOperator_real_adjoint (B : Matrix α β ℂ)
    (p : EuclideanSpace ℂ β) (y : EuclideanSpace ℂ α) :
    ⟪qmaMatrixOperator B p,y⟫_ℝ = ⟪p,qmaMatrixOperator B.conjTranspose y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator B) p y
  rw [← qmaMatrixOperator_star] at h
  exact congrArg Complex.re h.symm

theorem qmaQuadratic_operator (M : Matrix α α ℂ) (p : EuclideanSpace ℂ α) :
    qmaQuadratic M (fun i => p i) = ⟪p,qmaMatrixOperator M p⟫_ℝ := by
  rw [qmaEuclidean_real_inner]
  simp only [qmaQuadratic,PiLp.inner_apply,RCLike.inner_apply',qmaMatrixOperator_apply,
    Matrix.mulVec,dotProduct,Pi.star_apply,starRingEnd_apply]

theorem qmaQuadratic_sandwich [DecidableEq α] [DecidableEq β] (B : Matrix α β ℂ) (M : Matrix α α ℂ)
    (p : EuclideanSpace ℂ β) :
    qmaQuadratic (B.conjTranspose*M*B) (fun i => p i) =
      ⟪qmaMatrixOperator B p,qmaMatrixOperator M (qmaMatrixOperator B p)⟫_ℝ := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_mul,qmaMatrixOperator_mul]
  simp only [ContinuousLinearMap.comp_apply]
  exact (qmaMatrixOperator_real_adjoint B p _).symm

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGroundComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Operator-norm perturbations of the actual finite spin ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaQuadratic_norm_bound (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    |qmaQuadratic M (fun i => x i)| ≤ ‖spinMatrixOperator M‖*‖x‖^2 := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  calc
    _ ≤ ‖x‖*‖spinMatrixOperator M x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖spinMatrixOperator M‖*‖x‖) :=
      mul_le_mul_of_nonneg_left ((spinMatrixOperator M).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

theorem qmaNormalizedBottom_bddBelow (M : Matrix σ σ ℂ) :
    BddBelow {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
      e = ⟪x,spinMatrixOperator M x⟫_ℝ} := by
  refine ⟨-‖spinMatrixOperator M‖,?_⟩
  rintro e ⟨x,hx,rfl⟩
  have h := (abs_le.mp (qmaQuadratic_norm_bound M x)).1
  simpa only [hx,one_pow,mul_one,qmaQuadratic_operator,qmaMatrixOperator_square] using h

theorem qmaNormalizedBottom_le (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ)
    (hx : ‖x‖ = 1) :
    MediatorGraph.normalizedBottom M ≤ qmaQuadratic M (fun i => x i) := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  exact csInf_le (qmaNormalizedBottom_bddBelow M) ⟨x,hx,rfl⟩

theorem le_qmaNormalizedBottom (M : Matrix σ σ ℂ) (u : EuclideanSpace ℂ σ)
    (hu : ‖u‖ = 1) {b : ℝ}
    (h : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 → b ≤ qmaQuadratic M (fun i => x i)) :
    b ≤ MediatorGraph.normalizedBottom M := by
  apply le_csInf (show {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
    e = ⟪x,spinMatrixOperator M x⟫_ℝ}.Nonempty from ⟨_,u,hu,rfl⟩)
  rintro e ⟨x,hx,rfl⟩
  simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using h x hx

theorem qmaNormalizedBottom_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 →
      |qmaQuadratic M (fun i => x i)-qmaQuadratic N (fun i => x i)| ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  have hMN : MediatorGraph.normalizedBottom N-δ ≤ MediatorGraph.normalizedBottom M := by
    apply le_qmaNormalizedBottom M u hu
    intro x hx
    have hN := qmaNormalizedBottom_le N x hx
    have he := (abs_le.mp (herror x hx)).1
    linarith
  have hNM : MediatorGraph.normalizedBottom M-δ ≤ MediatorGraph.normalizedBottom N := by
    apply le_qmaNormalizedBottom N u hu
    intro x hx
    have hM := qmaNormalizedBottom_le M x hx
    have he := (abs_le.mp (herror x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem qmaNormalizedBottom_norm_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ‖spinMatrixOperator (M-N)‖ ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  apply qmaNormalizedBottom_error M N u hu
  intro x hx
  rw [← qmaQuadratic_sub]
  have h := (qmaQuadratic_norm_bound (M-N) x).trans
    (mul_le_mul_of_nonneg_right herror (sq_nonneg ‖x‖))
  simpa only [hx,one_pow,mul_one] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnitaryGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unitary changes of basis preserve the actual finite ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaUnitary_sandwich_form (U H : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    ⟪x,spinMatrixOperator (U.conjTranspose*H*U) x⟫_ℝ =
      ⟪spinMatrixOperator U x,spinMatrixOperator H (spinMatrixOperator U x)⟫_ℝ := by
  simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using qmaQuadratic_sandwich U H x

theorem qmaNormalizedBottom_unitary (U H : Matrix σ σ ℂ)
    (hU : U.conjTranspose*U = 1) (hU' : U*U.conjTranspose = 1) :
    MediatorGraph.normalizedBottom (U.conjTranspose*H*U) = MediatorGraph.normalizedBottom H := by
  have hnorm := spinMatrixOperator_unitary_norm_map U hU
  have hnorm' := spinMatrixOperator_unitary_norm_map U.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hU')
  have hinv (x : EuclideanSpace ℂ σ) :
      spinMatrixOperator U (spinMatrixOperator U.conjTranspose x) = x := by
    have hm := congrArg (fun M : Matrix σ σ ℂ => spinMatrixOperator M x) hU'
    simpa only [spinMatrixOperator_mul,ContinuousLinearMap.comp_apply,
      spinMatrixOperator_one,one_apply_eq_self] using hm
  unfold MediatorGraph.normalizedBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨spinMatrixOperator U x,(hnorm x).trans hx,qmaUnitary_sandwich_form U H x⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨spinMatrixOperator U.conjTranspose x,(hnorm' x).trans hx,?_⟩
    rw [qmaUnitary_sandwich_form,hinv]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhase
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A diagonal unitary rotates any chosen mediator X couplings to Y. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem qmaPhaseFactor_gram (m : Bool) (a : Fin 2) :
    star (qmaPhaseFactor m a)*qmaPhaseFactor m a = 1 := by
  cases m <;> fin_cases a <;> norm_num [qmaPhaseFactor]

theorem qmaPhaseFactor_flip (m : Bool) (a : Fin 2) :
    star (qmaPhaseFactor m (Equiv.swap (0:Fin 2) 1 a))*qmaPhaseFactor m a =
      if m = true then (if a = 1 then -Complex.I else Complex.I) else 1 := by
  cases m <;> fin_cases a <;> norm_num [qmaPhaseFactor]

omit [DecidableEq κ] in
theorem qmaAncillaPhase_gram (m : κ → Bool) (a : κ → Fin 2) :
    star (qmaAncillaPhase m a)*qmaAncillaPhase m a = 1 := by
  simp only [qmaAncillaPhase,star_prod,← Finset.prod_mul_distrib,qmaPhaseFactor_gram,Finset.prod_const_one]

theorem qmaPhaseMatrix_gram (m : κ → Bool) : (qmaPhaseMatrix m).conjTranspose*qmaPhaseMatrix m = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply]
    exact qmaAncillaPhase_gram m a
  · simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply,h]

theorem qmaPhaseMatrix_cogram (m : κ → Bool) : qmaPhaseMatrix m*(qmaPhaseMatrix m).conjTranspose = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simpa [qmaPhaseMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      mul_comm] using qmaAncillaPhase_gram m a
  · simp [qmaPhaseMatrix,Matrix.mul_apply,Matrix.diagonal_apply,h]

theorem qmaAncillaPhase_flip (m : κ → Bool) (e : κ) (b : κ → Fin 2) :
    star (qmaAncillaPhase m (qmaBitFlip e b))*qmaAncillaPhase m b =
      if m e = true then (if b e = 1 then -Complex.I else Complex.I) else 1 := by
  unfold qmaAncillaPhase
  rw [star_prod,← Finset.prod_mul_distrib,Finset.prod_eq_single e]
  · simpa only [qmaBitFlip,Function.update_self] using qmaPhaseFactor_flip (m e) (b e)
  · intro f _ hfe
    simp only [qmaBitFlip,Function.update_of_ne hfe]
    exact qmaPhaseFactor_gram (m f) (b f)
  · intro h
    exact False.elim (h (Finset.mem_univ e))

theorem qmaDiagonal_sandwich {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℂ) (M : Matrix α α ℂ) (a b : α) :
    ((Matrix.diagonal f).conjTranspose*M*Matrix.diagonal f) a b = star (f a)*M a b*f b := by
  simp [Matrix.mul_apply,Matrix.diagonal_apply]

theorem qmaPhaseMatrix_flip (m : κ → Bool) (e : κ) :
    (qmaPhaseMatrix m).conjTranspose*qmaBitFlipMatrix e*qmaPhaseMatrix m = qmaPolarizedFlip m e := by
  ext a b
  rw [qmaPhaseMatrix,qmaDiagonal_sandwich]
  by_cases h : a = qmaBitFlip e b
  · subst a
    simp only [qmaBitFlipMatrix,qmaPolarizedFlip,ite_true, if_true,mul_one]
    exact qmaAncillaPhase_flip m e b
  · simp [qmaBitFlipMatrix,qmaPolarizedFlip,h]

theorem qmaPhaseMatrix_diagonal (m : κ → Bool) (d : (κ → Fin 2) → ℂ) :
    (qmaPhaseMatrix m).conjTranspose*Matrix.diagonal d*qmaPhaseMatrix m = Matrix.diagonal d := by
  ext a b
  rw [qmaPhaseMatrix,qmaDiagonal_sandwich]
  by_cases h : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
    calc
      _ = (star (qmaAncillaPhase m a)*qmaAncillaPhase m a)*d a := by ring
      _ = _ := by rw [qmaAncillaPhase_gram,one_mul]
  · simp [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhaseLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotated mediator couplings are still one-local and have the required
entry parity to keep the physical Hamiltonian real. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem qmaPolarizedFlip_eq (m : κ → Bool) (e : κ) :
    qmaPolarizedFlip m e = if m e = true then
      Complex.I • (qmaBitFlipMatrix e*qmaBitZ e) else qmaBitFlipMatrix e := by
  ext a b
  have hdiag : (qmaBitFlipMatrix e*qmaBitZ e) a b =
      qmaBitFlipMatrix e a b*(if b e = 1 then -1 else 1) := by
    simp [qmaBitZ,Matrix.mul_apply,Matrix.diagonal_apply]
  by_cases hm : m e = true
  · simp only [hm,ite_true, if_true,Matrix.smul_apply,smul_eq_mul,hdiag,qmaBitFlipMatrix,qmaPolarizedFlip]
    split_ifs <;> ring
  · simp [qmaPolarizedFlip,qmaBitFlipMatrix,hm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEntryParity
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and purely imaginary entry parities determine the mediator phase. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ : Type*}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliYCount_restrict (S : Finset ι) (w : ι → Fin 4) :
    qmaPauliYCount (qmaPauliRestrict S w) = (S.filter (fun i => w i = 2)).card := by
  unfold qmaPauliYCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i ∈ S <;> simp [qmaPauliRestrict,hi]

theorem qmaPauliYCount_split (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T) :
    qmaPauliYCount (qmaPauliRestrict S w)+qmaPauliYCount (qmaPauliRestrict T w) =
      qmaPauliYCount w := by
  rw [qmaPauliYCount_restrict,qmaPauliYCount_restrict]
  have hd : Disjoint (S.filter (fun i => w i = 2)) (T.filter (fun i => w i = 2)) :=
    hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.card_union_of_disjoint hd]
  unfold qmaPauliYCount
  congr 1
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi <;> simpa using (Finset.mem_filter.mp hi).2
  · intro hi
    have hw := (Finset.mem_filter.mp hi).2
    have hs : i ∈ qmaPauliSupport w := by simp [qmaPauliSupport,hw]
    rcases Finset.mem_union.mp (hcover hs) with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,hw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hw⟩)

theorem qmaPauliRestrict_same_parity (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T)
    (hw : Even (qmaPauliYCount w)) :
    decide (Odd (qmaPauliYCount (qmaPauliRestrict S w))) =
      decide (Odd (qmaPauliYCount (qmaPauliRestrict T w))) := by
  have hsum := qmaPauliYCount_split S T w hST hcover
  simp only [Nat.even_iff] at hw
  have he : Odd (qmaPauliYCount (qmaPauliRestrict S w)) ↔
      Odd (qmaPauliYCount (qmaPauliRestrict T w)) := by
    simp only [Nat.odd_iff]
    omega
  simp only [he]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliExtend
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending a Pauli word by identities is exactly the local tensor lift. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliExtend_support (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliSupport (qmaPauliExtend S w) ⊆ S := by
  intro i hi
  by_contra h
  simp [qmaPauliSupport,qmaPauliExtend,h] at hi

theorem qmaPauliExtend_lift (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliWord (qmaPauliExtend S w) = qmaLocalLift S (qmaPauliWord w) := by
  ext s t
  rw [qmaLocalLift_apply]
  change (∏ i, qmaPauli (qmaPauliExtend S w i) (s i) (t i)) =
    (∏ i : {i // i ∈ S}, qmaPauli (w i) (s i.val) (t i.val))*
      (if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0)
  by_cases hr : (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)
  · rw [ite_eq_left hr,mul_one]
    have he (i : ι) (_hi : i ∈ Finset.univ) (hi : i ∉ S) :
        qmaPauli (qmaPauliExtend S w i) (s i) (t i) = 1 := by
      simp only [qmaPauliExtend,hi,dite_false,qmaPauli_zero,Matrix.one_apply]
      exact ite_eq_left (congrFun hr ⟨i,hi⟩)
    have hp := Finset.prod_subset (Finset.subset_univ S) he
    have hs := Finset.prod_subtype (F := inferInstance) S
      (by simp : ∀ i, i ∈ S ↔ i ∈ S) (fun i => qmaPauli (qmaPauliExtend S w i) (s i) (t i))
    have hex := hp.symm.trans hs
    have hw (i : {i // i ∈ S}) : qmaPauliExtend S w i.val = w i := by
      simp [qmaPauliExtend,i.property]
    simpa only [hw] using hex
  · rw [ite_eq_right hr,mul_zero]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    simp only [qmaPauliExtend,i.property,dite_false,qmaPauli_zero,Matrix.one_apply]
    exact ite_eq_right hi

theorem qmaPauliExtend_yCount (S : Finset ι) (w : {i // i ∈ S} → Fin 4) :
    qmaPauliYCount (qmaPauliExtend S w) = qmaPauliYCount w := by
  unfold qmaPauliYCount
  have he : Finset.univ.filter (fun i => qmaPauliExtend S w i = 2) =
      (Finset.univ.filter (fun i : {i // i ∈ S} => w i = 2)).map
        ⟨Subtype.val,Subtype.val_injective⟩ := by
    ext i
    constructor
    · intro hi
      have he := (Finset.mem_filter.mp hi).2
      by_cases hS : i ∈ S
      · exact Finset.mem_map.mpr ⟨⟨i,hS⟩,by simpa [qmaPauliExtend,hS] using he,rfl⟩
      · simp [qmaPauliExtend,hS] at he
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change qmaPauliExtend S w j.val = 2
      simpa [qmaPauliExtend,j.property] using (Finset.mem_filter.mp hj).2
  rw [he,Finset.card_map]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitPhasePhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent mediator phase rotations preserve the full physical spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaPhaseLift_gram (m : κ → Bool) :
    (qmaPhaseLift (σ := σ) m).conjTranspose*qmaPhaseLift m = 1 := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,qmaPhaseMatrix_gram,Matrix.one_kronecker_one]

theorem qmaPhaseLift_cogram (m : κ → Bool) :
    qmaPhaseLift (σ := σ) m*(qmaPhaseLift m).conjTranspose = 1 := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,qmaPhaseMatrix_cogram,Matrix.one_kronecker_one]

theorem qmaPhaseLift_sandwich (m : κ → Bool) (M : Matrix σ σ ℂ)
    (N : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ N)*qmaPhaseLift m =
      M ⊗ₖ ((qmaPhaseMatrix m).conjTranspose*N*qmaPhaseMatrix m) := by
  unfold qmaPhaseLift
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one,one_mul,mul_one]

theorem qmaPhaseLift_diagonal (m : κ → Bool) (M : Matrix σ σ ℂ)
    (d : (κ → Fin 2) → ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ Matrix.diagonal d)*qmaPhaseLift m = M ⊗ₖ Matrix.diagonal d := by
  rw [qmaPhaseLift_sandwich,qmaPhaseMatrix_diagonal]

theorem qmaPhaseLift_old (m : κ → Bool) (M : Matrix σ σ ℂ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*qmaPhaseLift m =
      M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) := by
  rw [qmaPhaseLift_sandwich,mul_one,qmaPhaseMatrix_gram]

theorem qmaPhaseLift_flip (m : κ → Bool) (M : Matrix σ σ ℂ) (e : κ) :
    (qmaPhaseLift m).conjTranspose*(M ⊗ₖ qmaBitFlipMatrix e)*qmaPhaseLift m =
      M ⊗ₖ qmaPolarizedFlip m e := by
  rw [qmaPhaseLift_sandwich,qmaPhaseMatrix_flip]

theorem qmaPhaseLift_physical (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) :
    (qmaPhaseLift m).conjTranspose*qmaPhysicalMediatorMatrix g L D V*qmaPhaseLift m =
      qmaPolarizedPhysical g L D V m := by
  have hpen : (qmaPhaseLift m).conjTranspose*qmaPhysicalPenaltyMatrix (σ := σ) g*qmaPhaseLift m =
      qmaPhysicalPenaltyMatrix g := qmaPhaseLift_diagonal m 1 _
  have hocc (e : κ) :
      (qmaPhaseLift m).conjTranspose*(D e ⊗ₖ qmaAncillaOccupation e)*qmaPhaseLift m =
        D e ⊗ₖ qmaAncillaOccupation e := qmaPhaseLift_diagonal m (D e) _
  unfold qmaPhysicalMediatorMatrix qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
    qmaPolarizedPhysical
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,
    hpen,hocc,qmaPhaseLift_old,qmaPhaseLift_flip]
  rfl

theorem qmaPolarizedPhysical_bottom (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaPolarizedPhysical g L D V m) =
      MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g L D V) := by
  rw [← qmaPhaseLift_physical]
  exact qmaNormalizedBottom_unitary (qmaPhaseLift m) (qmaPhysicalMediatorMatrix g L D V)
    (qmaPhaseLift_gram m) (qmaPhaseLift_cogram m)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdDecomposition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical gadget is a sum of seven explicit terms per mediator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaFinTwo_cast (a : Fin 2) : (a.val : ℂ) = if a = 1 then 1 else 0 := by
  fin_cases a <;> norm_num

omit [Fintype σ] [DecidableEq κ] in
theorem qmaPhysicalPenalty_sum (g : ℝ) : qmaPhysicalPenaltyMatrix (σ := σ) (κ := κ) g =
    ∑ e, (g:ℂ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e) := by
  ext p q
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [qmaPhysicalPenaltyMatrix,qmaAncillaDiagonal,Matrix.kronecker_apply,
    qmaAncillaOccupation,Matrix.diagonal_apply,Matrix.one_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  by_cases hst : s = t <;> by_cases hab : a = b
  · subst t
    subst b
    simp only [ite_true, if_true,one_mul,qmaAncillaNumber,Nat.cast_sum]
    push_cast
    rw [Finset.mul_sum]
    simp only [qmaFinTwo_cast]
  · simp [hst,hab]
  · simp [hst,hab]
  · simp [hst,hab]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliTripleSplit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every real three-local Pauli word splits into one real factor and two
single-site factors of the same entry parity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaPauliRestrict_restrict (L S : Finset ι) (w : ι → Fin 4) (hL : L ⊆ S) :
    qmaPauliRestrict L (qmaPauliRestrict S w) = qmaPauliRestrict L w := by
  funext i
  by_cases hi : i ∈ L
  · simp [qmaPauliRestrict,hi,hL hi]
  · simp [qmaPauliRestrict,hi]

omit [DecidableEq ι] in
theorem qmaPauliYCount_zero (w : ι → Fin 4) (h : ∀ i, w i ≠ 2) : qmaPauliYCount w = 0 := by
  simp [qmaPauliYCount,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitThirdPhased
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-order family with the real-preserving mediator phases. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ ι κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaThirdPhasedPiece_sum (A B C : Matrix σ σ ℂ) (e : κ) (R j : ℝ) (m : κ → Bool) :
    (∑ k, qmaThirdPhasedPiece A B C e R j m k) =
      (R^3:ℝ) • ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)+
      qmaThirdSeriesCounter A B C R j ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
      ((R^2:ℝ) • C) ⊗ₖ qmaAncillaOccupation e+
      ((R^2:ℝ) • qmaThirdSeriesPair A B j) ⊗ₖ qmaPolarizedFlip m e := by
  have hr (r : ℝ) (M : Matrix σ σ ℂ) : r • M = (r:ℂ) • M := rfl
  have hp (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  have hk (M N : Matrix σ σ ℂ) :
      (M-N) ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) =
        M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)-
          N ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) := by
    ext p q
    rcases p with ⟨s,a⟩
    rcases q with ⟨t,b⟩
    simp only [Matrix.kronecker_apply,Matrix.sub_apply,sub_mul]
  simp only [qmaThirdPhasedPiece,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,qmaThirdSeriesCounter,qmaThirdSeriesPair,
    hr,hp,Matrix.add_kronecker,hk,Matrix.smul_kronecker,Matrix.one_kronecker_one,
    smul_add,smul_smul]
  push_cast
  module

theorem qmaThirdPhased_decomposition (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    qmaThirdPhased H A B C R J m =
      H ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)+
        ∑ e, ∑ k, qmaThirdPhasedPiece (A e) (B e) (C e) e R (J e) m k := by
  simp only [qmaThirdPhased,qmaPolarizedPhysical,qmaMediatorOccupations,qmaThirdSeriesLow,
    qmaPhysicalPenalty_sum,Matrix.add_kronecker,MediatorGraph.sum_kronecker,
    qmaThirdPhasedPiece_sum,Finset.sum_add_distrib]
  have hs (r : ℝ) (M : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hs]
  abel

theorem qmaThirdPhased_bottom (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) (m : κ → Bool) :
    MediatorGraph.normalizedBottom (qmaThirdPhased H A B C R J m) =
      MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J) :=
  qmaPolarizedPhysical_bottom _ _ _ _ _

theorem qmaThirdPhasedLocalPiece_eq (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) :
    qmaThirdPhasedLocalPiece A B C e R j m =
      ![(R^3:ℝ) • qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (qmaAncillaOccupation e),
        (R*(1+(j/2)^2):ℝ) • (1 : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ),
        (R*j:ℝ) • qmaJoinMatrix (A*B) (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
        (-(1+(j/2)^2):ℝ) • qmaJoinMatrix C (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ),
        (R^2:ℝ) • qmaJoinMatrix C (qmaAncillaOccupation e),
        (R^2:ℝ) • qmaJoinMatrix A (qmaPolarizedFlip m e),
        (R^2*j/2:ℝ) • qmaJoinMatrix B (qmaPolarizedFlip m e)] := by
  funext k
  fin_cases k <;> simp [qmaThirdPhasedLocalPiece,qmaThirdPhasedPiece,qmaJoinMatrix,
    Matrix.submatrix_smul,Matrix.submatrix_one_equiv]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_sqrtHalf _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual ordered history cores have exact four-rational entries.  The
propagation Gram is formed on its at-most-five-site core; the construction
does not sum over spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem denote_mul {α β γ : Type} [Fintype β]
    (A : Matrix α β Scalar) (B : Matrix β γ Scalar) :
    denote (matMul A B) = denote A * denote B := by
  ext s t
  simp only [denote,matMul,value_finiteSum,value_mul,Matrix.mul_apply]

theorem denote_adjoint {α β : Type} (A : Matrix α β Scalar) :
    denote (adjoint A) = (denote A).conjTranspose := by
  ext s t
  simp only [denote,adjoint,value_conj,Matrix.conjTranspose_apply]

theorem value_hadamard (s t : Fin 2) : value (hadamard s t) = qmaHadamard s t := by
  fin_cases s <;> fin_cases t <;> simp [hadamard,qmaHadamard]

theorem value_phaseT (s t : Fin 2) : value (phaseT s t) = qmaPhaseT s t := by
  fin_cases s <;> fin_cases t <;> simp [phaseT,qmaPhaseT]

theorem value_identity {α : Type} [DecidableEq α] (s t : α) :
    value (identity s t) = (1 : Matrix α α ℂ) s t := by
  by_cases h : s = t <;> simp [identity,Matrix.one_apply,h]

theorem value_gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) :
    value (gate work g s t) = qmaGateMatrix work g s t := by
  cases g with
  | hadamard i =>
    rw [gate,value_finiteProduct]
    unfold qmaGateMatrix sourceTensor
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = qmaQubit work i
    · simp only [h,ite_true, if_true,value_hadamard]
    · simp only [h,ite_false, if_false,value_identity]
  | phaseT i =>
    rw [gate,value_finiteProduct]
    unfold qmaGateMatrix sourceTensor
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = qmaQubit work i
    · simp only [h,ite_true, if_true,value_phaseT]
    · simp only [h,ite_false, if_false,value_identity]
  | controlledNot i j =>
    by_cases h : s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t
    <;> simp [gate,qmaGateMatrix,h]

theorem value_delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) :
    value (delta c t s r) = qmaLocalPropagationDelta c t s r := by
  rw [qmaLocalPropagationDelta,qmaGuardProjection,Matrix.diagonal_mul]
  by_cases h : QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0
  · simp [delta,h,Matrix.sub_apply,qmaBitFlipMatrix,qmaJoinMatrix,
      Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,qmaStepMatrix,
      value_identity,value_gate]
    rfl
  · simp [delta,h]

theorem denote_deltaCore (c : QMACircuit) (t : Fin c.gates.length) :
    denote (deltaCore c t) = qmaLocalCore (qmaPropagationSites c t)
      (qmaLocalPropagationDelta c t) := by
  ext s r
  exact value_delta c t _ _

theorem core_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) (hB : QMALocalOn S B) :
    qmaLocalCore S (A*B) = qmaLocalCore S A*qmaLocalCore S B := by
  obtain ⟨A,rfl⟩ := hA
  obtain ⟨B,rfl⟩ := hB
  rw [← qmaLocalLift_mul,qmaLocalCore_lift,qmaLocalCore_lift,qmaLocalCore_lift]

theorem core_adjoint {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Finset ι} {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : QMALocalOn S A) :
    qmaLocalCore S A.conjTranspose = (qmaLocalCore S A).conjTranspose := by
  obtain ⟨A,rfl⟩ := hA
  rw [← qmaLocalLift_adjoint,qmaLocalCore_lift,qmaLocalCore_lift]

theorem denote_propagationCore (c : QMACircuit) (t : Fin c.gates.length) :
    denote (propagationCore c t) = qmaLocalCore (qmaPropagationSites c t)
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t) := by
  rw [propagationCore,denote_mul,denote_adjoint,denote_deltaCore,
    core_mul (qmaLocalPropagationDelta_local c t).adjoint (qmaLocalPropagationDelta_local c t),
    core_adjoint (qmaLocalPropagationDelta_local c t)]

theorem denote_lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar) :
    denote (lift S A) = qmaLocalLift S (denote A) := by
  ext s t
  simp only [denote,lift,value_mul,value_identity,Matrix.one_apply,qmaLocalLift_apply]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed four-spin coordinates for the exchange-only encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourExchange_source (i j : Fin 4) : qmaFourExchange i j =
    (sourceHeisenbergMatrix 4 i j).submatrix qmaFourBits qmaFourBits := by
  have hs (s t : Fin 16) : qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)) = t ↔
      sourceSpinSwap i j (qmaFourBits s) = qmaFourBits t := by
    exact (qmaFourBasisEquiv.eq_symm_apply).symm
  have he (s t : Fin 16) : s = t ↔ qmaFourBits s = qmaFourBits t :=
    qmaFourBasisEquiv.symm.injective.eq_iff.symm
  ext s t
  simp only [qmaFourExchange,qmaFourExchangeRational,sourceHeisenbergMatrix,Matrix.submatrix_apply]
  simp only [hs,he]
  split_ifs <;> norm_num

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

theorem qmaFourPenalty_exchange : qmaFourPenalty =
    qmaFourExchange 0 1+qmaFourExchange 0 2+qmaFourExchange 0 3+
      qmaFourExchange 1 2+qmaFourExchange 1 3+qmaFourExchange 2 3+
        (6:ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  ext s t
  by_cases h : s = t
  all_goals
    simp [qmaFourPenalty,qmaFourPenaltyRational,qmaFourExchange,Matrix.map_apply,h]

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

theorem qmaSiteMatrix_mul (i : Q) (A B : Matrix σ σ ℂ) :
    qmaSiteMatrix i A*qmaSiteMatrix i B = qmaSiteMatrix i (A*B) := by
  rw [qmaSiteMatrix,qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent operator bounds for the actual exchange encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisWeights_abs_sum (a : Fin 2) (p : Bool) :
    (∑ i, |qmaFourAxisWeights a p i|) ≤ 28 := by
  fin_cases a <;> cases p <;>
    norm_num [qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights,Fin.sum_univ_succ]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourCouplingBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the physically calibrated inter-block interaction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisScale_bounds (a : Fin 2) : 1 ≤ qmaFourAxisScale a ∧ qmaFourAxisScale a ≤ 256 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · norm_num [qmaFourAxisScale]
    constructor <;> nlinarith
  · norm_num [qmaFourAxisScale]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Internal physical exchange fields retain bounds in every tensor block. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourExchange_pauli (p q : Fin 4) (hpq : p ≠ q) :
    qmaFourExchange p q = ∑ μ : Fin 3, qmaFourSpin p μ*qmaFourSpin q μ := by
  rw [qmaFourExchange_source]
  change (sourceHeisenbergMatrix 4 p q).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm = _
  rw [← sourceLocalPauli_sum 4 p q hpq,MediatorGraph.submatrix_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,qmaFourSpin_source,qmaFourSpin_source]
  rfl

theorem qmaSiteMatrix_neg (i : Fin n) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (-A) = -qmaSiteMatrix i A := by
  rw [← neg_one_smul ℂ A,qmaSiteMatrix_smul,neg_one_smul]

theorem qmaSiteMatrix_sub (i : Fin n) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (A-B) = qmaSiteMatrix i A-qmaSiteMatrix i B := by
  simp only [sub_eq_add_neg,qmaSiteMatrix_add,qmaSiteMatrix_neg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the internal counterterm coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCouplingFactor_nonneg (a b : Fin 2) (t : ℝ) : 0 ≤ qmaFourCouplingFactor a b t := by
  unfold qmaFourCouplingFactor
  positivity

theorem qmaFourCouplingFactor_bound (a b : Fin 2) (t : ℝ) : qmaFourCouplingFactor a b t ≤ |t| := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hf := qmaFourCouplingFactor_nonneg a b t
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a := by nlinarith
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b := by
      exact le_mul_of_one_le_right (mul_nonneg hf (le_trans (by norm_num) ha)) hb
    _ = _ := he

theorem qmaFourAxisShift_abs_bound (a : Fin 2) (p : Bool) : |qmaFourAxisShift a p| ≤ 400 := by
  fin_cases a <;> cases p <;> norm_num [qmaFourAxisShift]

theorem qmaFourAxisScale_abs_bound (a : Fin 2) : |qmaFourAxisScale a| ≤ 256 := by
  rw [abs_of_pos (qmaFourAxisScale_pos a)]
  exact (qmaFourAxisScale_bounds a).2

theorem qmaFourAxisSign_abs (p : Bool) : |qmaFourAxisSign p| = 1 := by
  cases p <;> norm_num [qmaFourAxisSign]

theorem qmaFourCounterA_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterA a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterA,abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 256)*400 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisScale_abs_bound a)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem qmaFourCounterB_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterB a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterB,abs_mul,abs_mul,abs_mul,qmaFourAxisSign_abs,one_mul,
    abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 400)*256 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisScale_abs_bound b)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOnsite
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourAxisFieldShift_abs (a : Fin 2) (t : ℝ) : |qmaFourAxisFieldShift a t| ≤ |t| := by
  unfold qmaFourAxisFieldShift
  split_ifs
  · simpa only [abs_zero] using abs_nonneg t
  · rw [abs_div]
    norm_num

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockBasis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tensor code's physical coordinates are exactly ordinary groups of four qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaBlockBasisEquiv_symm_site (n : ℕ) (x : Fin n → Fin 16) (i : Fin n) (p : Fin 4) :
    (qmaBlockBasisEquiv n).symm x (finProdFinEquiv (i,p)) = qmaFourBits (x i) p := by
  change qmaFourBasisEquiv.symm (x (finProdFinEquiv.symm (finProdFinEquiv (i,p))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i,p))).2 = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem qmaBlockTensor_source (n : ℕ) (A : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (n*4) (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
        qmaTensorMatrix (fun i => (sourceTensor 4 (A i)).submatrix qmaFourBits qmaFourBits) := by
  ext x y
  change (∏ k : Fin (n*4), A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    ((qmaBlockBasisEquiv n).symm x k) ((qmaBlockBasisEquiv n).symm y k)) =
    ∏ i, ∏ p, A i p (qmaFourBits (x i) p) (qmaFourBits (y i) p)
  rw [← finProdFinEquiv.prod_comp]
  simp only [Equiv.symm_apply_apply,qmaBlockBasisEquiv_symm_site,Fintype.prod_prod_type]

theorem qmaBlockPauli_source (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    (sourceLocalPauli (n*4) (finProdFinEquiv (i,p)) μ).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaSiteMatrix i (qmaFourSpin p μ) := by
  have hsource : sourceLocalPauli (n*4) (finProdFinEquiv (i,p)) μ =
      sourceTensor (n*4) (fun k => if (finProdFinEquiv.symm k).1 = i then
        (if (finProdFinEquiv.symm k).2 = p then pauli μ else 1) else 1) := by
    unfold sourceLocalPauli
    congr 1
    funext k
    obtain ⟨⟨j,q⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
    by_cases hj : j = i <;> by_cases hq : q = p <;> simp [hj,hq]
  rw [hsource,qmaBlockTensor_source n (fun j q => if j = i then (if q = p then pauli μ else 1) else 1),qmaSiteMatrix]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true, if_true,qmaFourSpin_source,sourceLocalPauli]
  · simp only [hj,ite_false, if_false,sourceTensor_one]
    exact Matrix.submatrix_one_equiv qmaFourBasisEquiv.symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both internal and cross-block couplings are ordinary source Heisenberg exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaBlockExchange_source (i : Fin n) (p q : Fin 4) (hpq : p ≠ q) :
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (i,q))).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaSiteMatrix i (qmaFourExchange p q) := by
  have hij : finProdFinEquiv (i,p) ≠ finProdFinEquiv (i,q) := by
    intro h
    exact hpq (congrArg Prod.snd (finProdFinEquiv.injective h))
  rw [← sourceLocalPauli_sum (n*4) _ _ hij,MediatorGraph.submatrix_sum,
    qmaFourExchange_pauli p q hpq,qmaSiteMatrix_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ (qmaBlockBasisEquiv n).symm _,
    qmaBlockPauli_source,qmaBlockPauli_source,qmaSiteMatrix_mul]

theorem qmaBlockCross_source (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q))).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaFourTensorCross i j p q := by
  have hne : finProdFinEquiv (i,p) ≠ finProdFinEquiv (j,q) := by
    intro h
    exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))
  rw [← sourceLocalPauli_sum (n*4) _ _ hne,MediatorGraph.submatrix_sum,qmaFourTensorCross]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ (qmaBlockBasisEquiv n).symm _,
    qmaBlockPauli_source,qmaBlockPauli_source]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal exchange sums for the real-coefficient four-spin Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourPenalty_edgeSum : qmaFourPenalty =
    (∑ e : Fin 6, qmaFourExchange (qmaFourEdgeLeft e) (qmaFourEdgeRight e))+
      (6:ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  rw [qmaFourPenalty_exchange]
  simp only [qmaFourEdgeLeft,qmaFourEdgeRight,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  abel

theorem qmaBlockSourcePenalty_reindex (n : ℕ) :
    (qmaBlockSourcePenalty n).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorPenalty n := by
  simp only [qmaBlockSourcePenalty,MediatorGraph.submatrix_add_apply,MediatorGraph.submatrix_sum,
    MediatorGraph.submatrix_smul_apply,Matrix.submatrix_one_equiv,
    qmaBlockExchange_source _ _ _ (qmaFourEdge_distinct _),qmaFourTensorPenalty,qmaTensorPenalty,
    qmaFourPenalty_edgeSum,qmaSiteMatrix_add,qmaSiteMatrix_sum,qmaSiteMatrix_smul,qmaSiteMatrix_one,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  module

theorem qmaBlockSourceField_reindex (i : Fin n) (x z : ℝ) :
    (qmaBlockSourceField i x z).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaSiteMatrix i (qmaFourField x z) := by
  simp only [qmaBlockSourceField,Matrix.submatrix_sub,Pi.sub_apply,MediatorGraph.submatrix_smul_apply,
    qmaBlockExchange_source i 0 3 (by decide),qmaBlockExchange_source i 0 2 (by decide),
    qmaBlockExchange_source i 0 1 (by decide),qmaFourField,qmaSiteMatrix_sub,qmaSiteMatrix_smul]

theorem qmaBlockSourceAxisField_reindex (i : Fin n) (a : Fin 2) (t : ℝ) :
    (qmaBlockSourceAxisField i a t).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaSiteMatrix i (qmaFourAxisField a t) := by
  unfold qmaBlockSourceAxisField qmaFourAxisField
  split_ifs <;> exact qmaBlockSourceField_reindex _ _ _

theorem qmaBlockSourceCoupling_reindex (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaBlockSourceCoupling i j a b t).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorCoupling i j a b t := by
  simp only [qmaBlockSourceCoupling,MediatorGraph.submatrix_smul_apply,MediatorGraph.submatrix_sum,
    qmaBlockCross_source i j hij,qmaFourTensorCoupling,qmaFourTensorWeighted]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical simulator as a sum of ordinary Heisenberg exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaBlockSourceCounterterm_reindex (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    (qmaBlockSourceCounterterm i j a b t).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaFourTensorCounterterm i j a b t := by
  simp only [qmaBlockSourceCounterterm,MediatorGraph.submatrix_add_apply,
    qmaBlockSourceAxisField_reindex,qmaFourTensorCounterterm]

theorem qmaBlockSourceOnsite_reindex (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaBlockSourceOnsite site axis weight constant).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorOnsite site axis weight constant := by
  simp only [qmaBlockSourceOnsite,MediatorGraph.submatrix_add_apply,
    MediatorGraph.submatrix_sum,qmaBlockSourceAxisField_reindex,
    MediatorGraph.submatrix_smul_apply,Matrix.submatrix_one_equiv,
    qmaFourTensorOnsite,qmaFourTensorFields]

theorem qmaBlockSourceFull_reindex (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (hneq : ∀ e, left e ≠ right e)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    (qmaBlockSourceFull r left right a b t site axis weight constant).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorPhysicalMatrix r
        ((r:ℂ) • qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFullCounterterm left right a b t site axis weight constant) := by
  simp only [qmaBlockSourceFull,MediatorGraph.submatrix_add_apply,
    MediatorGraph.submatrix_smul_apply,MediatorGraph.submatrix_sum,qmaBlockSourcePenalty_reindex,
    qmaBlockSourceCoupling_reindex _ _ (hneq _),qmaBlockSourceCounterterm_reindex,
    qmaBlockSourceOnsite_reindex,qmaFourTensorPhysicalMatrix,qmaFourTensorFamilyCoupling,
    qmaFourTensorFullCounterterm,qmaFourTensorFamilyCounterterm,Complex.ofReal_pow]
  abel

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite list of physical exchanges, with no implicit many-body terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaBlockSourceAxisField_edges (i : Fin n) (a : Fin 2) (t : ℝ) :
    qmaBlockSourceAxisField i a t = ∑ k : Fin 3, (qmaFieldEdgeWeight a t k:ℂ) •
      sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,qmaFieldEdgeRight k)) := by
  unfold qmaBlockSourceAxisField qmaFieldEdgeWeight
  split_ifs <;>
    simp only [qmaFieldEdgeRight,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,add_zero,qmaBlockSourceField,zero_div,Complex.ofReal_zero,
      zero_smul,sub_zero,zero_sub,zero_add,neg_div,Complex.ofReal_neg,neg_smul]
  · rw [smul_sub]
    rw [sub_eq_add_neg]

omit [Fintype κ] [Fintype τ] in
theorem qmaFourExchange_distinct (left right : κ → Fin n) (site : τ → Fin n)
    (hne : ∀ e, left e ≠ right e) (x : QMAFourExchangeIndex n κ τ) :
    qmaFourExchangeLeft left right site x ≠ qmaFourExchangeRight left right site x := by
  cases x with
  | inl x =>
    intro h
    exact qmaFourEdge_distinct x.2 (congrArg Prod.snd (finProdFinEquiv.injective h))
  | inr x =>
    cases x with
    | inl x =>
      intro h
      exact hne x.1 (congrArg Prod.fst (finProdFinEquiv.injective h))
    | inr x =>
      cases x with
      | inl x =>
        intro h
        exact qmaFieldEdgeRight_ne x.2.2 (congrArg Prod.snd (finProdFinEquiv.injective h))
      | inr x =>
        intro h
        exact qmaFieldEdgeRight_ne x.2 (congrArg Prod.snd (finProdFinEquiv.injective h))

theorem qmaFourExchange_count : Fintype.card (QMAFourExchangeIndex n κ τ) =
    6*n+22*Fintype.card κ+3*Fintype.card τ := by
  simp only [QMAFourExchangeIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

theorem qmaFourExchange_sum (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (∑ x : QMAFourExchangeIndex n κ τ,
      (qmaFourExchangeWeight r a b t axis weight x:ℂ) • sourceHeisenbergMatrix (n*4)
        (qmaFourExchangeLeft left right site x) (qmaFourExchangeRight left right site x))+
      (qmaFourExchangeScalar n r axis weight constant:ℂ) • 1 =
        qmaBlockSourceFull r left right a b t site axis weight constant := by
  simp only [QMAFourExchangeIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourExchangeWeight,
    qmaBlockSourceFull,qmaBlockSourcePenalty,qmaBlockSourceCoupling,
    qmaBlockSourceCounterterm,qmaBlockSourceOnsite,qmaBlockSourceAxisField_edges,
    Fin.sum_univ_two,ite_true, if_true,show (1:Fin 2) ≠ 0 by decide,ite_false, if_false]
  simp only [smul_add,Finset.smul_sum,smul_smul,Finset.sum_add_distrib,
    qmaFourExchangeScalar,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_natCast,mul_assoc]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational coefficient rounding controls the full physical ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaExchangeMatrix_sub (left right : κ → Fin n) (J K : κ → ℝ) (s u : ℝ) :
    qmaExchangeMatrix left right J s-qmaExchangeMatrix left right K u =
      qmaExchangeMatrix left right (fun e => J e-K e) (s-u) := by
  simp only [qmaExchangeMatrix,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  abel

theorem qmaExchangeMatrix_norm (left right : κ → Fin n) (hne : ∀ e, left e ≠ right e)
    (J : κ → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaExchangeMatrix left right J constant)‖ ≤
      3*(∑ e, |J e|)+|constant| := by
  have hI : ‖spinMatrixOperator (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  have hs : ‖spinMatrixOperator ((∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)))‖ ≤
      3*(∑ e, |J e|) := by
    rw [spinMatrixOperator_sum,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro e _
    rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_right (sourceHeisenbergMatrix_operator_norm n _ _ (hne e)) (abs_nonneg _)
  rw [qmaExchangeMatrix,spinMatrixOperator_add]
  apply (norm_add_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_left hI (abs_nonneg constant)
  linarith

theorem qmaExchangeMatrix_ground_error (left right : κ → Fin n)
    (hne : ∀ e, left e ≠ right e) (J K : κ → ℝ) (s u : ℝ) :
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix left right J s)-
      MediatorGraph.normalizedBottom (qmaExchangeMatrix left right K u)| ≤
        3*(∑ e, |J e-K e|)+|s-u| := by
  apply qmaNormalizedBottom_norm_error _ _ (EuclideanSpace.single (fun _ => 0) 1) (by simp [PiLp.norm_single])
  rw [qmaExchangeMatrix_sub]
  exact qmaExchangeMatrix_norm left right hne _ _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliProduct
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli multiplication, including the scalar phases needed to
replace a YY interaction by commuting real X/Z factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPauli_product (a b : Fin 4) :
    qmaPauli a*qmaPauli b = qmaPauliProductPhase a b • qmaPauli (qmaPauliProductIndex a b) := by
  fin_cases a <;> fin_cases b <;> ext s t <;> fin_cases s <;> fin_cases t <;>
    simp [qmaPauliProductIndex,qmaPauliProductPhase,qmaPauli,pauliX,pauliY,pauliZ,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply] <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliWord_product (a b : ι → Fin 4) :
    qmaPauliWord a*qmaPauliWord b = (∏ i, qmaPauliProductPhase (a i) (b i)) •
      qmaPauliWord (fun i => qmaPauliProductIndex (a i) (b i)) := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  simp only [qmaPauli_product,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,qmaPauliWord]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumYYFactor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A YY term is a product of commuting real XZ and ZX involutions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaTwoPauliWord_support (i j : ι) (a b : Fin 4) :
    qmaPauliSupport (qmaTwoPauliWord i j a b) ⊆ {i,j} := by
  intro k hk
  by_contra hn
  have hki : k ≠ i := fun h => hn (by simp [h])
  have hkj : k ≠ j := fun h => hn (by simp [h])
  have hz : qmaTwoPauliWord i j a b k ≠ 0 := (Finset.mem_filter.mp hk).2
  simp [qmaTwoPauliWord,hki,hkj] at hz

theorem qmaYY_factor (i j : ι) (hij : i ≠ j) :
    qmaPauliWord (qmaTwoPauliWord i j 1 3)*qmaPauliWord (qmaTwoPauliWord i j 3 1) =
      qmaPauliWord (qmaTwoPauliWord i j 2 2) := by
  rw [qmaPauliWord_product]
  have hindex : (fun k => qmaPauliProductIndex (qmaTwoPauliWord i j 1 3 k)
      (qmaTwoPauliWord i j 3 1 k)) = qmaTwoPauliWord i j 2 2 := by
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [qmaTwoPauliWord,qmaPauliProductIndex,hki,hkj,Ne.symm hij]
  rw [hindex]
  have hphase : (∏ k, qmaPauliProductPhase (qmaTwoPauliWord i j 1 3 k)
      (qmaTwoPauliWord i j 3 1 k)) = 1 := by
    rw [← Finset.prod_subset (Finset.subset_univ ({i,j} : Finset ι))]
    · simp [qmaTwoPauliWord,qmaPauliProductPhase,hij,Ne.symm hij]
    · intro k _ hk
      have hki : k ≠ i := fun h => hk (by simp [h])
      have hkj : k ≠ j := fun h => hk (by simp [h])
      simp [qmaTwoPauliWord,qmaPauliProductPhase,hki,hkj]
  rw [hphase,one_smul]

theorem qmaYY_factor_commute (i j : ι) (hij : i ≠ j) :
    qmaPauliWord (qmaTwoPauliWord i j 1 3)*qmaPauliWord (qmaTwoPauliWord i j 3 1) =
      qmaPauliWord (qmaTwoPauliWord i j 3 1)*qmaPauliWord (qmaTwoPauliWord i j 1 3) := by
  have h := congrArg Matrix.conjTranspose (qmaYY_factor i j hij)
  rw [Matrix.conjTranspose_mul,(qmaPauliWord_hermitian _).eq,
    (qmaPauliWord_hermitian _).eq,(qmaPauliWord_hermitian _).eq] at h
  exact (qmaYY_factor i j hij).trans h.symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumYYElimination
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The only Y-containing real two-local Pauli words are YY words. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qmaPauliWord_zero : qmaPauliWord (fun _ : ι => 0) = 1 := by
  ext s t
  simp only [qmaPauliWord,qmaPauli_zero,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem qmaTwoLocalEvenY_cases (w : ι → Fin 4)
    (hw : (qmaPauliSupport w).card ≤ 2) (he : Even (qmaPauliYCount w)) :
    (∀ i, w i ≠ 2) ∨ ∃ i j, i ≠ j ∧ w = qmaTwoPauliWord i j 2 2 := by
  by_cases hnone : ∀ i, w i ≠ 2
  · exact Or.inl hnone
  · right
    push Not at hnone
    obtain ⟨i,hi⟩ := hnone
    let Y := Finset.univ.filter (fun k => w k = 2)
    have hsub : Y ⊆ qmaPauliSupport w := by
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      simp [qmaPauliSupport,h]
    have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨i,by simp [Y,hi]⟩
    have hbound : Y.card ≤ 2 := (Finset.card_le_card hsub).trans hw
    have hcard : Y.card = 2 := by
      change Even Y.card at he
      obtain ⟨k,hk⟩ := he
      omega
    obtain ⟨a,b,hab,hY⟩ := Finset.card_eq_two.mp hcard
    have hsupport : Y = qmaPauliSupport w :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hw)
    have ha : w a = 2 := (Finset.mem_filter.mp (show a ∈ Y by rw [hY]; simp)).2
    have hb : w b = 2 := (Finset.mem_filter.mp (show b ∈ Y by rw [hY]; simp)).2
    refine ⟨a,b,hab,?_⟩
    funext k
    by_cases hka : k = a
    · simp [qmaTwoPauliWord,hka,ha]
    · by_cases hkb : k = b
      · simp [qmaTwoPauliWord,hkb,hb,Ne.symm hab]
      · have hz : w k = 0 := by
          by_contra hn
          have hk : k ∈ qmaPauliSupport w := by simp [qmaPauliSupport,hn]
          rw [← hsupport,hY] at hk
          simp [hka,hkb] at hk
        simp [qmaTwoPauliWord,hka,hkb,hz]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliSingle
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli words for the mediator flip and occupation matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaSinglePauliWord_apply (i : ι) (a : Fin 4) (s t : ι → Fin 2) :
    qmaPauliWord (qmaSinglePauliWord i a) s t =
      qmaPauli a (s i) (t i)*(∏ k ∈ Finset.univ.erase i, if s k = t k then (1:ℂ) else 0) := by
  rw [qmaPauliWord,← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [qmaSinglePauliWord,ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp [(Finset.mem_erase.mp hk).1,qmaPauli_zero,Matrix.one_apply]

theorem qmaSinglePauliWord_support (i : ι) (a : Fin 4) :
    qmaPauliSupport (qmaSinglePauliWord i a) ⊆ {i} := by
  intro k hk
  by_contra hn
  have hki : k ≠ i := by simpa using hn
  have ha := (Finset.mem_filter.mp hk).2
  simp [qmaSinglePauliWord,hki] at ha

theorem qmaSinglePauliWord_X (i : ι) :
    qmaPauliWord (qmaSinglePauliWord i 1) = qmaBitFlipMatrix i := by
  have hX (u v : Fin 2) : qmaPauli 1 u v =
      if u = Equiv.swap (0:Fin 2) 1 v then (1:ℂ) else 0 := by
    fin_cases u <;> fin_cases v <;> simp [qmaPauli,pauliX,Equiv.swap_apply_def] <;> norm_num
  ext s t
  rw [qmaSinglePauliWord_apply,hX]
  change _ = if s = qmaBitFlip i t then (1:ℂ) else 0
  by_cases h : s = qmaBitFlip i t
  · subst s
    simp only [ite_true, if_true]
    have he : qmaBitFlip i t i = Equiv.swap (0:Fin 2) 1 (t i) := by simp [qmaBitFlip]
    rw [ite_eq_left he,one_mul]
    apply Finset.prod_eq_one
    intro k hk
    simp [qmaBitFlip,(Finset.mem_erase.mp hk).1]
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    by_cases hki : k = i
    · subst k
      have he : s i ≠ Equiv.swap (0:Fin 2) 1 (t i) := by simpa [qmaBitFlip] using hk
      rw [ite_eq_right he,zero_mul]
    · have he : s k ≠ t k := by simpa [qmaBitFlip,hki] using hk
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
        (ite_eq_right he),mul_zero]

theorem qmaSinglePauliWord_Z (i : ι) :
    qmaPauliWord (qmaSinglePauliWord i 3) =
      Matrix.diagonal (fun s => if s i = 1 then (-1:ℂ) else 1) := by
  have hZ (u v : Fin 2) : qmaPauli 3 u v =
      if u = v then (if u = 1 then (-1:ℂ) else 1) else 0 := by
    fin_cases u <;> fin_cases v <;> simp [qmaPauli,pauliZ] <;> norm_num
  ext s t
  rw [qmaSinglePauliWord_apply,hZ,Matrix.diagonal_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    by_cases hki : k = i
    · subst k
      rw [ite_eq_right hk,zero_mul]
    · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩)
        (ite_eq_right hk),mul_zero]

theorem qmaAncillaOccupation_pauli (i : ι) : qmaAncillaOccupation i =
    (1/2:ℂ) • (1-qmaPauliWord (qmaSinglePauliWord i 3)) := by
  rw [qmaSinglePauliWord_Z]
  ext s t
  by_cases h : s = t
  · subst t
    generalize hs : s i = v
    fin_cases v <;> simp [qmaAncillaOccupation,Matrix.diagonal_apply,Matrix.one_apply,hs] <;> norm_num
  · simp [qmaAncillaOccupation,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSubdivision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit X/Z Pauli output for subdivision, including its occupation term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem qmaXZSubdivision_noY (a b : ι → Fin 4) (e : κ)
    (ha : ∀ i, a i ≠ 2) (hb : ∀ i, b i ≠ 2) (k : Fin 4) (x : ι ⊕ κ) :
    qmaXZSubdivisionWord a b e k x ≠ 2 := by
  fin_cases k <;> cases x <;> simp [qmaXZSubdivisionWord,qmaSinglePauliWord,ha,hb] <;> split_ifs <;> decide

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint single-site X/Z factors, retaining their explicit two-site product. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaPauliRestrict_noY (S : Finset ι) (w : ι → Fin 4) (hw : ∀ i, w i ≠ 2) :
    ∀ i, qmaPauliRestrict S w i ≠ 2 := by
  intro i
  simp only [qmaPauliRestrict]
  split_ifs
  · exact hw i
  · decide

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Seven explicit X/Z words for the third-order three-to-two-local gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
theorem qmaJoinOccupation_expand (M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (e : κ) :
    qmaJoinMatrix M (qmaAncillaOccupation e) = (1/2:ℂ) •
      (qmaJoinMatrix M 1-qmaJoinMatrix M (qmaPauliWord (qmaSinglePauliWord e 3))) := by
  rw [qmaAncillaOccupation_pauli]
  ext s t
  simp only [qmaJoinMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZPrivate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Private subdivision mediators prevent distinct two-body terms from sharing a pair. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaSinglePauliWord_support_eq (i : ι) (a : Fin 4) (ha : a ≠ 0) :
    qmaPauliSupport (qmaSinglePauliWord i a) = {i} := by
  ext k
  by_cases hk : k = i <;> simp [qmaPauliSupport,qmaSinglePauliWord,hk,ha]

omit [DecidableEq ι] in
theorem qmaXZSubdivision_inr_mem (a b : ι → Fin 4) (e t : κ) (k : Fin 4) :
    Sum.inr t ∈ qmaPauliSupport (qmaXZSubdivisionWord a b e k) ↔ k ≠ 0 ∧ t = e := by
  fin_cases k <;> simp [qmaXZSubdivisionWord,qmaPauliSupport,qmaSinglePauliWord]

theorem qmaXZSubdivision_pair_index (a b : ι → Fin 4) (e : κ) (k : Fin 4)
    (h : (qmaPauliSupport (qmaXZSubdivisionWord a b e k)).card = 2) : k = 2 ∨ k = 3 := by
  fin_cases k
  · change (qmaPauliSupport (fun _ : ι ⊕ κ => 0)).card = 2 at h
    simp [qmaPauliSupport] at h
  · change (qmaPauliSupport (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3))).card = 2 at h
    rw [qmaPauliSupport_join_card,qmaSinglePauliWord_support_eq e 3 (by decide)] at h
    simp [qmaPauliSupport] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem qmaXZSubdivision_private_pair (a b : κ → ι → Fin 4)
    (hd : ∀ e, Disjoint (qmaPauliSupport (a e)) (qmaPauliSupport (b e)))
    (e f : κ) (k l : Fin 4)
    (hk : (qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k)).card = 2)
    (heq : qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k) =
      qmaPauliSupport (qmaXZSubdivisionWord (a f) (b f) f l)) : e = f ∧ k = l := by
  have hl := heq ▸ hk
  have hk' := qmaXZSubdivision_pair_index (a e) (b e) e k hk
  have hl' := qmaXZSubdivision_pair_index (a f) (b f) f l hl
  have hk0 : k ≠ 0 := by rcases hk' with rfl | rfl <;> decide
  have hin : Sum.inr e ∈ qmaPauliSupport (qmaXZSubdivisionWord (a e) (b e) e k) :=
    (qmaXZSubdivision_inr_mem _ _ _ _ _).mpr ⟨hk0,rfl⟩
  rw [heq] at hin
  have hef := ((qmaXZSubdivision_inr_mem _ _ _ _ _).mp hin).2
  subst f
  refine ⟨rfl,?_⟩
  rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
  · rfl
  · change qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1)) =
      qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1)) at heq
    have hab : qmaPauliSupport (a e) = qmaPauliSupport (b e) := by
      ext i
      have h := Finset.ext_iff.mp heq (Sum.inl i)
      simpa [qmaPauliSupport] using h
    have hz : qmaPauliSupport (a e) = ∅ :=
      (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hab] using hd e)
    change (qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1))).card = 2 at hk
    rw [qmaPauliSupport_join_card,hz,qmaSinglePauliWord_support_eq e 1 (by decide)] at hk
    norm_num at hk
  · change qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1)) =
      qmaPauliSupport (Sum.elim (a e) (qmaSinglePauliWord e 1)) at heq
    have hab : qmaPauliSupport (b e) = qmaPauliSupport (a e) := by
      ext i
      have h := Finset.ext_iff.mp heq (Sum.inl i)
      simpa [qmaPauliSupport] using h
    have hz : qmaPauliSupport (b e) = ∅ :=
      (Finset.disjoint_self_iff_empty _).mp (by simpa only [← hab] using (hd e).symm)
    change (qmaPauliSupport (Sum.elim (b e) (qmaSinglePauliWord e 1))).card = 2 at hk
    rw [qmaPauliSupport_join_card,hz,qmaSinglePauliWord_support_eq e 1 (by decide)] at hk
    norm_num at hk
  · rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit scalar, one-site and two-site terms for the X/Z circuit family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaXZLabel_pauli (a : Fin 2) : qmaPauli (qmaXZLabel a) = qmaFourAxis a := by
  fin_cases a <;> rfl

theorem QMAXZTerm.word_matrix {n : ℕ} (t : QMAXZTerm n) : qmaPauliWord t.word = t.matrix := by
  change qmaTensorMatrix (fun k => qmaPauli (t.word k)) = _
  cases t with
  | scalar =>
    simpa only [QMAXZTerm.word,QMAXZTerm.matrix,qmaPauli_zero] using qmaTensorMatrix_one (Q := Fin n) (σ := Fin 2)
  | field i a =>
    change qmaTensorMatrix _ = qmaSiteMatrix i (qmaFourAxis a)
    rw [qmaSiteMatrix]
    congr 1
    funext k
    by_cases h : k = i <;> simp only [QMAXZTerm.word,h,ite_true, if_true,ite_false, if_false,qmaXZLabel_pauli,qmaPauli_zero]
  | pair i j hij a b =>
    change qmaTensorMatrix _ = qmaPairMatrix i j (qmaFourAxis a) (qmaFourAxis b)
    rw [qmaPairMatrix]
    congr 1
    funext k
    by_cases hi : k = i
    · simp only [QMAXZTerm.word,hi,ite_true, if_true,qmaXZLabel_pauli]
    · by_cases hj : k = j
      · subst k
        simp only [QMAXZTerm.word,hi,ite_true, if_true,ite_false, if_false,qmaXZLabel_pauli]
      · simp only [QMAXZTerm.word,hi,hj,ite_false, if_false,qmaPauli_zero]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZFamilySplit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual word family splits into the three kinds of physical simulator terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem QMAXZTerm.pair_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) :
    t.matrix = qmaPairMatrix (t.asPair h).left (t.asPair h).right
      (qmaFourAxis (t.asPair h).axisLeft) (qmaFourAxis (t.asPair h).axisRight) := by
  cases t <;> first | exact h.elim | rfl

theorem QMAXZTerm.field_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsField) :
    t.matrix = qmaSiteMatrix (t.asField h).site (qmaFourAxis (t.asField h).axis) := by
  cases t <;> first | exact h.elim | rfl

theorem QMAXZTerm.scalar_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsScalar) : t.matrix = 1 := by
  cases t <;> first | exact h.elim | rfl

theorem qmaXZLabel_ne_zero (a : Fin 2) : qmaXZLabel a ≠ 0 := by
  fin_cases a <;> decide

theorem QMAXZTerm.pair_support {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) :
    qmaPauliSupport t.word = {(t.asPair h).left,(t.asPair h).right} := by
  cases t with
  | scalar => exact h.elim
  | field => exact h.elim
  | pair i j hij a b =>
    change qmaPauliSupport (QMAXZTerm.pair i j hij a b).word = {i,j}
    apply Finset.ext
    intro k
    unfold qmaPauliSupport
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,QMAXZTerm.word]
    by_cases hi : k = i
    · subst k
      simp only [ite_true, if_true,true_or,iff_true]
      exact qmaXZLabel_ne_zero a
    · by_cases hj : k = j
      · subst k
        simp only [hi,ite_false, if_false,ite_true, if_true,or_true,iff_true]
        exact qmaXZLabel_ne_zero b
      · simp only [hi,hj,ite_false, if_false,ne_eq,not_true_eq_false,or_self]

variable {n : ℕ} {κ : Type*} [Fintype κ]

omit [Fintype κ] in
theorem qmaXZPairData_distinct (t : κ → QMAXZTerm n)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (e f : QMAXZPairIndex t) (hef : e ≠ f) :
    ({(qmaXZPairData t e).left,(qmaXZPairData t e).right} : Finset (Fin n)) ≠
      {(qmaXZPairData t f).left,(qmaXZPairData t f).right} := by
  intro heq
  apply hef
  apply Subtype.ext
  apply hprivate e.val f.val
  · rw [(t e.val).pair_support e.property]
    exact Finset.card_pair ((qmaXZPairData t e).distinct)
  · rw [(t e.val).pair_support e.property,(t f.val).pair_support f.property]
    exact heq

theorem qmaSum_subtype_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ e : {x // p x}, f e.val) = ∑ e, if p e then f e else 0 := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun e => if p e then f e else 0)
  have hp : (∑ e : {x // p x}, if p e.val then f e.val else 0) = ∑ e : {x // p x}, f e.val := by
    apply Finset.sum_congr rfl
    intro e _
    exact ite_eq_left e.property
  have hn : (∑ e : {x // ¬p x}, if p e.val then f e.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact ite_eq_right e.property
  simpa only [hp,hn,add_zero] using h

theorem qmaXZFamily_split (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    (∑ e, (J e:ℂ) • (t e).matrix) =
      (∑ e : QMAXZPairIndex t, (J e.val:ℂ) • qmaPairMatrix
        (qmaXZPairData t e).left (qmaXZPairData t e).right
        (qmaFourAxis (qmaXZPairData t e).axisLeft) (qmaFourAxis (qmaXZPairData t e).axisRight))+
      (∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • qmaSiteMatrix
        (qmaXZFieldData t e).site (qmaFourAxis (qmaXZFieldData t e).axis))+
      ((∑ e : QMAXZScalarIndex t, J e.val:ℝ):ℂ) • 1 := by
  have hp : (∑ e : QMAXZPairIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ∑ e : QMAXZPairIndex t, (J e.val:ℂ) • qmaPairMatrix
        (qmaXZPairData t e).left (qmaXZPairData t e).right
        (qmaFourAxis (qmaXZPairData t e).axisLeft) (qmaFourAxis (qmaXZPairData t e).axisRight) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).pair_matrix e.property]
    rfl
  have hf : (∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • qmaSiteMatrix
        (qmaXZFieldData t e).site (qmaFourAxis (qmaXZFieldData t e).axis) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).field_matrix e.property]
    rfl
  have hs : (∑ e : QMAXZScalarIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ((∑ e : QMAXZScalarIndex t, J e.val:ℝ):ℂ) • 1 := by
    rw [Complex.ofReal_sum,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).scalar_matrix e.property]
  rw [← hp,← hf,← hs]
  rw [qmaSum_subtype_ite (fun e => (t e).IsPair) (fun e => (J e:ℂ) • (t e).matrix),
    qmaSum_subtype_ite (fun e => (t e).IsField) (fun e => (J e:ℂ) • (t e).matrix),
    qmaSum_subtype_ite (fun e => (t e).IsScalar) (fun e => (J e:ℂ) • (t e).matrix)]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases t e <;> simp [QMAXZTerm.IsPair,QMAXZTerm.IsField,QMAXZTerm.IsScalar]

theorem qmaXZFamily_target (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    qmaFourTensorFullTarget
      (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
      (fun e => J e.val)
      (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
      (fun e => J e.val) (qmaXZFamilyConstant t J) = ∑ e, (J e:ℂ) • (t e).matrix := by
  rw [qmaXZFamily_split t J]
  simp only [qmaFourTensorFullTarget,qmaFourTensorFamilyTarget,qmaXZFamilyConstant,Complex.ofReal_sub]
  module

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational finite Heisenberg family with controlled error, before lattice routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaBlockSourceFull_exchange (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    qmaBlockSourceFull r left right a b t site axis weight constant =
      qmaExchangeMatrix (qmaFourExchangeLeft left right site) (qmaFourExchangeRight left right site)
        (qmaFourExchangeWeight r a b t axis weight) (qmaFourExchangeScalar n r axis weight constant) :=
  (qmaFourExchange_sum r left right a b t site axis weight constant).symm

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockCoefficientBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial magnitude bounds for the physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFieldEdgeWeight_bound (a : Fin 2) (t : ℝ) (k : Fin 3) :
    |qmaFieldEdgeWeight a t k| ≤ |t| := by
  have hs : 1 ≤ Real.sqrt 3 := by
    have hs0 := Real.sqrt_nonneg 3
    have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hd : |t/(2*Real.sqrt 3)| ≤ |t| := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt 3)]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt 3)).mpr
    nlinarith [abs_nonneg t]
  have hz : |t/2| ≤ |t| := by rw [abs_div]; norm_num
  by_cases ha : a = 0
  · subst a
    fin_cases k
    · simpa [qmaFieldEdgeWeight] using hd
    · simpa [qmaFieldEdgeWeight,neg_div] using hd
    · simp [qmaFieldEdgeWeight]
  · fin_cases k
    · simp [qmaFieldEdgeWeight,ha]
    · simp [qmaFieldEdgeWeight,ha]
    · simpa [qmaFieldEdgeWeight,ha,neg_div] using hz

theorem qmaFourAxisWeights_pointwise (a : Fin 2) (s : Bool) (p : Fin 4) :
    |qmaFourAxisWeights a s p| ≤ 28 :=
  (Finset.single_le_sum (fun q _ => abs_nonneg (qmaFourAxisWeights a s q))
    (Finset.mem_univ p)).trans (qmaFourAxisWeights_abs_sum a s)

theorem qmaFourEnergyOffset_bound (a b : Fin 2) (t : ℝ) :
    |qmaFourEnergyOffset a b t| ≤ 364800*|t| := by
  have ha := qmaFourAxisFieldShift_abs a (qmaFourCounterA a b t)
  have hb := qmaFourAxisFieldShift_abs b (qmaFourCounterB a b t)
  have hca := qmaFourCounterA_bound a b t
  have hcb := qmaFourCounterB_bound a b t
  have hm : |qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign t)| ≤ 160000*|t| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
    calc
      _ ≤ (|t| * 400)*400 := mul_le_mul
        (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum := abs_add_le (qmaFourAxisFieldShift a (qmaFourCounterA a b t))
    (qmaFourAxisFieldShift b (qmaFourCounterB a b t))
  have hsub := abs_sub
    (qmaFourAxisFieldShift a (qmaFourCounterA a b t)+qmaFourAxisFieldShift b (qmaFourCounterB a b t))
    (qmaFourCouplingFactor a b t*qmaFourAxisShift a true*qmaFourAxisShift b (qmaFourCouplingSign t))
  unfold qmaFourEnergyOffset
  linarith

variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

omit [Fintype τ] in
theorem qmaSum_subtype_abs_le (p : κ → Prop) [DecidablePred p] (J : κ → ℝ) :
    (∑ e : {x // p x}, |J e.val|) ≤ ∑ e, |J e| := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun e => |J e|)
  have hn : 0 ≤ ∑ e : {x // ¬p x}, |J e.val| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

omit [Fintype τ] in
theorem qmaXZFamilyConstant_bound (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    |qmaXZFamilyConstant t J| ≤ 364801*(∑ e, |J e|) := by
  have hp := qmaSum_subtype_abs_le (fun e => (t e).IsPair) J
  have hs := qmaSum_subtype_abs_le (fun e => (t e).IsScalar) J
  have hsp := Finset.abs_sum_le_sum_abs (fun e : QMAXZScalarIndex t => J e.val) Finset.univ
  have hpp := Finset.abs_sum_le_sum_abs (fun e : QMAXZPairIndex t =>
      qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)) Finset.univ
  have he : (∑ e : QMAXZPairIndex t,
      |qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)|) ≤
        364800*(∑ e : QMAXZPairIndex t, |J e.val|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun _ _ => qmaFourEnergyOffset_bound _ _ _)
  have hd := abs_sub (∑ e : QMAXZScalarIndex t, J e.val)
    (∑ e : QMAXZPairIndex t, qmaFourEnergyOffset
      (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val))
  unfold qmaXZFamilyConstant
  linarith

omit [Fintype τ] in
theorem qmaXZBlock_exchange_count (t : κ → QMAXZTerm n) :
    Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)) ≤
      6*n+25*Fintype.card κ := by
  rw [qmaFourExchange_count]
  have hp := Fintype.card_subtype_le (fun e => (t e).IsPair)
  have hf := Fintype.card_subtype_le (fun e => (t e).IsField)
  change Fintype.card (QMAXZPairIndex t) ≤ Fintype.card κ at hp
  change Fintype.card (QMAXZFieldIndex t) ≤ Fintype.card κ at hf
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational sampling of the fixed algebraic constants in the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

theorem inverseScale_mul (a : Fin 2) : inverseScale a*qmaFourAxisScale a = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale,qmaFourAxisScale]
    nlinarith
  · norm_num [inverseScale,qmaFourAxisScale]

theorem inverseScale_bounds (a : Fin 2) : 0 ≤ inverseScale a ∧ inverseScale a ≤ 1 := by
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale]
    constructor <;> nlinarith
  · norm_num [inverseScale]

theorem root_nonneg (k : ℕ) (q : ℚ) : 0 ≤ RationalSquareRoot.value (k,q) := by
  unfold RationalSquareRoot.value DyadicRootProgram.value
  positivity

theorem value_nonneg (k : ℕ) (a : Fin 2) : 0 ≤ value k a := by
  unfold value
  split_ifs
  · exact div_nonneg (root_nonneg k 3) (by norm_num)
  · norm_num

theorem value_error (k : ℕ) (a : Fin 2) :
    |(value k a:ℝ)-inverseScale a| ≤ (2:ℝ)⁻¹^k := by
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  norm_num only [Rat.cast_ofNat] at h
  by_cases ha : a = 0
  · simp only [value,inverseScale,ha,ite_true, if_true,Rat.cast_div,Rat.cast_ofNat]
    obtain ⟨hl,hu⟩ := abs_le.mp h
    apply abs_le.mpr
    constructor <;> linarith
  · simp [value,inverseScale,ha]

theorem value_bounds (k : ℕ) (a : Fin 2) : 0 ≤ (value k a:ℝ) ∧ (value k a:ℝ) ≤ 1 := by
  have hn : (0:ℝ) ≤ value k a := by exact_mod_cast value_nonneg k a
  refine ⟨hn,?_⟩
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases ha : a = 0
  · simp only [value,ha,ite_true, if_true,Rat.cast_div,Rat.cast_ofNat]
    have hh := (abs_le.mp h).2
    norm_num only [Rat.cast_ofNat] at hh
    nlinarith
  · norm_num [value,ha]

theorem product_error (k : ℕ) (a b : Fin 2) :
    |(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| ≤ 2*(2:ℝ)⁻¹^k := by
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have ha := value_error k a
  have hb := value_error k b
  have hav : |inverseScale a| ≤ 1 := by rw [abs_of_nonneg (inverseScale_bounds a).1]; exact (inverseScale_bounds a).2
  have hbv : |(value k b:ℝ)| ≤ 1 := by rw [abs_of_nonneg (value_bounds k b).1]; exact (value_bounds k b).2
  calc
    _ = |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)+inverseScale a*((value k b:ℝ)-inverseScale b)| := by
      congr 1
      ring
    _ ≤ |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)|+|inverseScale a*((value k b:ℝ)-inverseScale b)| := abs_add_le _ _
    _ = |(value k a:ℝ)-inverseScale a| * |(value k b:ℝ)|+
        |inverseScale a| * |(value k b:ℝ)-inverseScale b| := by rw [abs_mul,abs_mul]
    _ ≤ (2:ℝ)⁻¹^k*1+1*(2:ℝ)⁻¹^k := add_le_add
      (mul_le_mul ha hbv (abs_nonneg _) hd) (mul_le_mul hav hb (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem radicand_nonneg (k : ℕ) (a b : Fin 2) (t : ℚ) : 0 ≤ radicand k a b t := by
  unfold radicand
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg t)) (value_nonneg k a))
    (value_nonneg k b)

theorem coupling_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingSize a b t = Real.sqrt ((8/3)*|t| *inverseScale a*inverseScale b) := by
  unfold qmaFourCouplingSize
  congr 1
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have han := (qmaFourAxisScale_pos a).ne'
  have hbn := (qmaFourAxisScale_pos b).ne'
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) han) hbn)).mpr
  calc
    _ = 8*|t| *(inverseScale a*qmaFourAxisScale a)*(inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = _ := by ring

theorem radicand_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(radicand k a b t:ℝ)-(8/3)*|(t:ℝ)| *inverseScale a*inverseScale b| ≤
      (16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  simp only [radicand,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_abs]
  calc
    _ = |((8/3)*|(t:ℝ)|)*((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)| := by
      congr 1
      ring
    _ = ((8/3)*|(t:ℝ)|)*|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (8/3:ℝ)*|(t:ℝ)|)]
    _ ≤ ((8/3)*|(t:ℝ)|)*(2*(2:ℝ)⁻¹^k) :=
      mul_le_mul_of_nonneg_left (product_error k a b) (by positivity)
    _ = _ := by ring

theorem coupling_error (k l : ℕ) (a b : Fin 2) (t : ℚ) :
    |(coupling k l a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      (2:ℝ)⁻¹^l+Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k) := by
  have hr := RationalSquareRoot.value_error l (radicand_nonneg k a b t)
  have hs := RationalSquareRoot.sqrt_perturbation
    (show (0:ℝ) ≤ radicand k a b t by exact_mod_cast radicand_nonneg k a b t)
    (show 0 ≤ (8/3)*|(t:ℝ)| *inverseScale a*inverseScale b from
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (inverseScale_bounds a).1)
        (inverseScale_bounds b).1)
  rw [coupling_eq]
  exact (abs_sub_le _ _ _).trans (add_le_add hr (hs.trans (Real.sqrt_le_sqrt (radicand_error k a b t))))

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAxisSampleAccuracy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear precision schedule for the literal four-spin coupling sampler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample

theorem calibrated_error (a b : Fin 2) (k : ℕ) (t : ℚ) :
    |(calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      2*(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
  have h := coupling_error (2*k+6) k a b t
  have he : (2:ℝ)⁻¹^(2*k+6) = ((2:ℝ)⁻¹^k)^2/64 := by
    rw [show 2*k+6=k*2+6 by omega,pow_add,pow_mul]
    norm_num
    ring
  have heps : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have hs : Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^(2*k+6)) ≤
      (1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he,mul_pow]
    have hb : |(t:ℝ)|/12 ≤ (1+|(t:ℝ)|)^2 := by nlinarith [abs_nonneg (t:ℝ),sq_nonneg |(t:ℝ)|]
    calc
      _ = (|(t:ℝ)|/12)*((2:ℝ)⁻¹^k)^2 := by ring
      _ ≤ (1+|(t:ℝ)|)^2*((2:ℝ)⁻¹^k)^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  change |(coupling (2*k+6) k a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤ _
  apply h.trans
  have hp := mul_nonneg (abs_nonneg (t:ℝ)) heps
  linarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBlockBudget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rationally evaluable budget suffices for every physical simulator coefficient. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaXZBlockBudget_bound (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    qmaXZBlockBudget t J ≤ qmaXZPolynomialBudget J := by
  let U := qmaXZInputSize J
  have hU : 0 ≤ U := by dsimp [U,qmaXZInputSize]; positivity
  have hs : (∑ e, |J e|) ≤ U := by
    dsimp [U,qmaXZInputSize]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hp : (∑ e : QMAXZPairIndex t, (1+|J e.val|)) ≤ U := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    have hc := Fintype.card_subtype_le (fun e => (t e).IsPair)
    change Fintype.card (QMAXZPairIndex t) ≤ Fintype.card κ at hc
    exact add_le_add (by exact_mod_cast hc) (qmaSum_subtype_abs_le (fun e => (t e).IsPair) J)
  have hf := (qmaSum_subtype_abs_le (fun e => (t e).IsField) J).trans hs
  have hc := (qmaXZFamilyConstant_bound t J).trans
    (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hpair0 : 0 ≤ ∑ e : QMAXZPairIndex t, (1+|J e.val|) := by positivity
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ) ≤ 7056) hpair0)
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 7056)) 2
  change 1+7056*(∑ e : QMAXZPairIndex t, (1+|J e.val|))+
      (1228800*(∑ e : QMAXZPairIndex t, (1+|J e.val|))+
        7*(∑ e : QMAXZFieldIndex t, |J e.val|)+|qmaXZFamilyConstant t J|)+
      (7056*(∑ e : QMAXZPairIndex t, (1+|J e.val|)))^2 ≤
    1+2000000*U+(7056*U)^2
  nlinarith

variable {τ : Type*} [Fintype τ]

omit [Fintype τ] in
theorem qmaXZBlock_polynomial_accuracy (t : κ → QMAXZTerm n) (J : κ → ℝ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaXZBlockSource (9*(qmaXZPolynomialBudget J)^3*N) t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 1/(N:ℝ) := by
  have h := qmaFourTensorFull_accuracy_of_budget
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e f hef => qmaXZPairData_distinct t hprivate e f hef)
    (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (qmaXZFamilyConstant t J) (qmaXZPolynomialBudget J)
    (qmaXZBlockBudget_bound t J) N hN
  rw [qmaXZFamily_target,
    ← qmaBlockSourceFull_reindex _ _ _ _ _ _ (fun e => (qmaXZPairData t e).distinct),
    MediatorGraph.normalizedBottom_reindex] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoefficientHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rational-register bounds for the actual fixed-arity Pauli
trace.  These supply an explicit precision budget before scalar sampling. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar
open scoped BigOperators Classical

theorem height_finiteSum {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteSum f) ≤ ∑ a, height (f a) := by
  calc
    _ ≤ ∑ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteSum,enumerate,List.map_map,List.map_ofFn,List.sum_ofFn,
        Function.comp_apply] using
        height_sum ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.sum_comp (fun a => height (f a))

theorem height_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteProduct f) ≤ ∏ a, height (f a) := by
  calc
    _ ≤ ∏ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteProduct,enumerate,List.map_map,List.map_ofFn,List.prod_ofFn,
        Function.comp_apply] using
        height_product ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.prod_comp (fun a => height (f a))

theorem height_pauli (μ : Fin 4) (a b : Fin 2) : height (pauli μ a b) ≤ 1 := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,height,realHeight,rat,realRat,neg,realNeg,imaginary]

theorem height_word {ι : Type} [Fintype ι]
    (w : ι → Fin 4) (s t : ι → Fin 2) : height (word w s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  exact Finset.prod_le_one (fun _ _ => height_nonnegative _)
    (fun _ _ => height_pauli _ _ _)

theorem height_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    height (coefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  have hcell (s t : ι → Fin 2) : height (mul (A s t) (word w t s)) ≤ C := by
    calc
      _ ≤ height (A s t)*height (word w t s) := height_mul _ _
      _ ≤ height (A s t)*1 :=
        mul_le_mul_of_nonneg_left (height_word _ _ _) (height_nonnegative _)
      _ ≤ C := by simpa using hA s t
  have hsum : height (finiteSum (fun s : ι → Fin 2 =>
      finiteSum (fun t : ι → Fin 2 => mul (A s t) (word w t s)))) ≤
      ∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C := by
    apply (height_finiteSum _).trans
    apply Finset.sum_le_sum
    intro s _
    exact (height_finiteSum _).trans (Finset.sum_le_sum (fun t _ => hcell s t))
  have hp : 0 < (2:ℚ)^Fintype.card ι := pow_pos (by norm_num) _
  calc
    _ ≤ height (rat ((2:ℚ)^Fintype.card ι)⁻¹)*
        height (finiteSum (fun s => finiteSum (fun t => mul (A s t) (word w t s)))) :=
      height_mul _ _
    _ ≤ ((2:ℚ)^Fintype.card ι)⁻¹*(∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C) := by
      rw [height_rat,abs_of_pos (inv_pos.mpr hp)]
      exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
      field_simp

theorem realHeight_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (realCoefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  apply le_trans (le_add_of_nonneg_right (realHeight_nonnegative (coefficient A w).2))
  exact height_coefficient A w C hA

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCountertermSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterms use only rational arithmetic and the fixed inverse-scale sample. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

theorem factor_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingFactor a b t = |t| *inverseScale a*inverseScale b := by
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ = qmaFourCouplingFactor a b t*(inverseScale a*qmaFourAxisScale a)*
        (inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = (qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b)*inverseScale a*inverseScale b := by ring
    _ = _ := by rw [he]

theorem counterA_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterA a b t = |t| *inverseScale b*qmaFourAxisShift b (qmaFourCouplingSign t) := by
  rw [qmaFourCounterA,factor_eq]
  calc
    _ = |t| *inverseScale b*(inverseScale a*qmaFourAxisScale a)*qmaFourAxisShift b (qmaFourCouplingSign t) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

theorem counterB_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCounterB a b t = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true := by
  rw [qmaFourCounterB,factor_eq]
  calc
    _ = |t| *inverseScale a*qmaFourAxisSign (qmaFourCouplingSign t)*qmaFourAxisShift a true*
        (inverseScale b*qmaFourAxisScale b) := by ring
    _ = _ := by rw [inverseScale_mul]; ring

theorem shift_cast (a : Fin 2) (p : Bool) : (shift a p:ℝ) = qmaFourAxisShift a p := by
  unfold shift qmaFourAxisShift
  split_ifs <;> norm_num

theorem polarity_cast (t : ℚ) : (polarity t:ℝ) = qmaFourAxisSign (qmaFourCouplingSign (t:ℝ)) := by
  by_cases ht : t ≤ 0
  · have htR : (t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]
  · have htR : ¬(t:ℝ) ≤ 0 := by exact_mod_cast ht
    simp [polarity,qmaFourAxisSign,qmaFourCouplingSign,ht,htR]

theorem sign_cast (t : ℚ) : decide (t ≤ 0) = qmaFourCouplingSign (t:ℝ) := by
  unfold qmaFourCouplingSign
  congr 1
  exact propext (by exact_mod_cast (Iff.rfl : t ≤ 0 ↔ t ≤ 0))

theorem factor_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ)| ≤ 2*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [factor_eq]
  simp only [factor,Rat.cast_mul,Rat.cast_abs]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by rw [abs_mul,abs_abs]
    _ ≤ |(t:ℝ)| *(2*(2:ℝ)⁻¹^k) := mul_le_mul_of_nonneg_left (product_error k a b) (abs_nonneg _)
    _ = _ := by ring

theorem counterA_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)-qmaFourCounterA a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterA_eq]
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k b:ℝ)-inverseScale b)*qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k b:ℝ)-inverseScale b| *|qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| := by
      rw [abs_mul,abs_mul,abs_abs]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k b) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)-qmaFourCounterB a b (t:ℝ)| ≤ 400*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  rw [counterB_eq]
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast]
  calc
    _ = abs (|(t:ℝ)| *((value k a:ℝ)-inverseScale a)*qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))*
        qmaFourAxisShift a true) := by
      congr 1
      ring
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisSign (qmaFourCouplingSign (t:ℝ))| *
        |qmaFourAxisShift a true| := by
      rw [abs_mul,abs_mul,abs_mul,abs_abs]
    _ = |(t:ℝ)| *|(value k a:ℝ)-inverseScale a| *|qmaFourAxisShift a true| := by
      rw [qmaFourAxisSign_abs,mul_one]
    _ ≤ (|(t:ℝ)| *(2:ℝ)⁻¹^k)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_error k a) (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFieldSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational evaluation of each internal physical field coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open Matrix

theorem inverseScale_field : 64*inverseScale 0 = 1/(2*Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num only [inverseScale,ite_true]
  field_simp
  nlinarith

theorem fieldX_error (k : ℕ) (t : ℚ) :
    |(fieldX k t:ℝ)-(t:ℝ)/(2*Real.sqrt 3)| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have he : (t:ℝ)/(2*Real.sqrt 3) = 64*(t:ℝ)*inverseScale 0 := by
    rw [mul_comm 64 (t:ℝ),mul_assoc,inverseScale_field]
    ring
  rw [he]
  simp only [fieldX,Rat.cast_mul,Rat.cast_ofNat]
  calc
    _ = 64*|(t:ℝ)| *|(value k 0:ℝ)-inverseScale 0| := by
      rw [show 64*(t:ℝ)*(value k 0:ℝ)-64*(t:ℝ)*inverseScale 0 =
        (64*(t:ℝ))*((value k 0:ℝ)-inverseScale 0) by ring,abs_mul,abs_mul]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (value_error k 0) (by positivity)

theorem fieldValue_error (k : ℕ) (a : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a t e:ℝ)-qmaFieldEdgeWeight a (t:ℝ) e| ≤ 64*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  by_cases ha : a = 0
  · fin_cases e
    · simpa [fieldValue,qmaFieldEdgeWeight,ha] using fieldX_error k t
    · simpa [fieldValue,qmaFieldEdgeWeight,ha,neg_div,neg_add_eq_sub,abs_sub_comm] using fieldX_error k t
    · simp [fieldValue,qmaFieldEdgeWeight,ha]
  · fin_cases e <;> simp [fieldValue,qmaFieldEdgeWeight,ha,Rat.cast_div]

theorem fieldWeight_lipschitz (a : Fin 2) (x y : ℝ) (e : Fin 3) :
    |qmaFieldEdgeWeight a x e-qmaFieldEdgeWeight a y e| ≤ |x-y| := by
  have he : qmaFieldEdgeWeight a (x-y) e = qmaFieldEdgeWeight a x e-qmaFieldEdgeWeight a y e := by
    fin_cases a <;> fin_cases e <;> norm_num [qmaFieldEdgeWeight] <;> ring
  rw [← he]
  exact qmaFieldEdgeWeight_bound a (x-y) e

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOffsetSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error bounds for the sampled counterterm fields and their scalar shifts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem counterA_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterA k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterA,Rat.cast_mul,Rat.cast_abs,shift_cast,sign_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k b).1]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k b).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound b _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterB_abs (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(counterB k a b t:ℝ)| ≤ 400*|(t:ℝ)| := by
  simp only [counterB,Rat.cast_mul,Rat.cast_abs,shift_cast,polarity_cast,abs_mul,abs_abs,
    abs_of_nonneg (value_bounds k a).1,qmaFourAxisSign_abs,mul_one]
  calc
    _ ≤ (|(t:ℝ)| *1)*400 := mul_le_mul
      (mul_le_mul_of_nonneg_left (value_bounds k a).2 (abs_nonneg _))
      (qmaFourAxisShift_abs_bound a true) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem counterFieldA_error (k : ℕ) (a b : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k a (counterA k a b t) e:ℝ)-qmaFieldEdgeWeight a (qmaFourCounterA a b (t:ℝ)) e| ≤
      26000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have hfield := fieldValue_error k a (counterA k a b t) e
  have hcoef := counterA_abs k a b t
  have hsample := counterA_error k a b t
  have hweight := (fieldWeight_lipschitz a (counterA k a b t:ℝ) (qmaFourCounterA a b (t:ℝ)) e).trans hsample
  apply ((abs_sub_le _ _ _).trans (add_le_add hfield hweight)).trans
  have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (2:ℝ)⁻¹^k)
  nlinarith

theorem counterFieldB_error (k : ℕ) (a b : Fin 2) (t : ℚ) (e : Fin 3) :
    |(fieldValue k b (counterB k a b t) e:ℝ)-qmaFieldEdgeWeight b (qmaFourCounterB a b (t:ℝ)) e| ≤
      26000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have hfield := fieldValue_error k b (counterB k a b t) e
  have hcoef := counterB_abs k a b t
  have hsample := counterB_error k a b t
  have hweight := (fieldWeight_lipschitz b (counterB k a b t:ℝ) (qmaFourCounterB a b (t:ℝ)) e).trans hsample
  apply ((abs_sub_le _ _ _).trans (add_le_add hfield hweight)).trans
  have hm := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (2:ℝ)⁻¹^k)
  nlinarith

theorem shiftValue_error (a : Fin 2) (q : ℚ) (x : ℝ) :
    |(shiftValue a q:ℝ)-qmaFourAxisFieldShift a x| ≤ |(q:ℝ)-x| := by
  by_cases ha : a = 0
  · simp [shiftValue,qmaFourAxisFieldShift,ha]
  · simp only [shiftValue,qmaFourAxisFieldShift,ha,ite_false, if_false,Rat.cast_div,Rat.cast_ofNat]
    rw [← sub_div,abs_div]
    norm_num

theorem offset_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ)| ≤
      320800*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  have ha := (shiftValue_error a (counterA k a b t) (qmaFourCounterA a b (t:ℝ))).trans
    (counterA_error k a b t)
  have hb := (shiftValue_error b (counterB k a b t) (qmaFourCounterB a b (t:ℝ))).trans
    (counterB_error k a b t)
  have hc : |((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ))| ≤ 320000*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((2*|(t:ℝ)| *(2:ℝ)⁻¹^k)*400)*400 := mul_le_mul
        (mul_le_mul (factor_error k a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (by positivity)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : (offset k a b t:ℝ)-qmaFourEnergyOffset a b (t:ℝ) =
      ((shiftValue a (counterA k a b t):ℝ)-qmaFourAxisFieldShift a (qmaFourCounterA a b (t:ℝ)))+
      ((shiftValue b (counterB k a b t):ℝ)-qmaFourAxisFieldShift b (qmaFourCounterB a b (t:ℝ)))-
      ((factor k a b t:ℝ)-qmaFourCouplingFactor a b (t:ℝ))*qmaFourAxisShift a true*
        qmaFourAxisShift b (qmaFourCouplingSign (t:ℝ)) := by
    simp only [offset,qmaFourEnergyOffset,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,shift_cast,sign_cast]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  calc
    _ ≤ (400*|(t:ℝ)| *(2:ℝ)⁻¹^k+400*|(t:ℝ)| *(2:ℝ)⁻¹^k)+320000*|(t:ℝ)| *(2:ℝ)⁻¹^k :=
      add_le_add (add_le_add ha hb) hc
    _ = _ := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumExchangeSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified rational values for every edge of the actual physical exchange family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped Classical BigOperators

theorem stencil_cast (a : Fin 2) (s : Bool) (p : Fin 4) :
    (stencil a s p:ℝ) = qmaFourAxisWeights a s p := by
  fin_cases a <;> cases s <;> fin_cases p <;>
    norm_num [stencil,qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights]

theorem crossValue_error (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) :
    |(crossValue k r a b t p q:ℝ)-(r:ℝ)*qmaFourCouplingSize a b (t:ℝ)*
      (qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q)| ≤
        1568*|(r:ℝ)| *(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
  have hw : |qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q| ≤ 784 := by
    rw [abs_mul]
    exact (mul_le_mul (qmaFourAxisWeights_pointwise a true p)
      (qmaFourAxisWeights_pointwise b (qmaFourCouplingSign (t:ℝ)) q)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simp only [crossValue,Rat.cast_mul,stencil_cast,sign_cast]
  calc
    _ = |(r:ℝ)| *|(calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)| *
        |qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q| := by
      rw [show (r:ℝ)*(calibrated a b (k,t):ℝ)*(qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q)-
          (r:ℝ)*qmaFourCouplingSize a b (t:ℝ)*(qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q) =
        ((r:ℝ)*((calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)))*
          (qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q) by ring,
        abs_mul,abs_mul]
    _ ≤ (|(r:ℝ)| *(2*(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k))*784 := mul_le_mul
      (mul_le_mul_of_nonneg_left (calibrated_error a b k t) (abs_nonneg _)) hw
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

variable {n : ℕ} {κ τ : Type*}

theorem weightValue_error (k : ℕ) (r : ℚ) (a b : κ → Fin 2) (t : κ → ℚ)
    (axis : τ → Fin 2) (weight : τ → ℚ) (B : ℝ) (hB : 0 ≤ B)
    (ht : ∀ e, |(t e:ℝ)| ≤ B) (hw : ∀ e, |(weight e:ℝ)| ≤ B)
    (x : QMAFourExchangeIndex n κ τ) :
    |(weightValue k r a b t axis weight x:ℝ)-
      qmaFourExchangeWeight (r:ℝ) a b (fun e => (t e:ℝ)) axis (fun e => (weight e:ℝ)) x| ≤
        weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k := by
  have heps : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have hcross : 0 ≤ 1568*|(r:ℝ)| *(1+B)*(2:ℝ)⁻¹^k := by positivity
  cases x with
  | inl x =>
    simp only [weightValue,qmaFourExchangeWeight,Rat.cast_pow,sub_self,abs_zero,weightErrorBudget]
    positivity
  | inr x =>
    cases x with
    | inl x =>
      simp only [weightValue,qmaFourExchangeWeight]
      have h := crossValue_error k r (a x.1) (b x.1) (t x.1) x.2.1 x.2.2
      have hm := mul_le_mul_of_nonneg_right (ht x.1)
        (by positivity : 0 ≤ 1568*|(r:ℝ)| *(2:ℝ)⁻¹^k)
      unfold weightErrorBudget
      nlinarith
    | inr x =>
      cases x with
      | inl x =>
        simp only [weightValue,qmaFourExchangeWeight]
        split_ifs
        · have h := counterFieldA_error k (a x.1) (b x.1) (t x.1) x.2.2
          have hm := mul_le_mul_of_nonneg_right (ht x.1) heps
          unfold weightErrorBudget
          nlinarith
        · have h := counterFieldB_error k (a x.1) (b x.1) (t x.1) x.2.2
          have hm := mul_le_mul_of_nonneg_right (ht x.1) heps
          unfold weightErrorBudget
          nlinarith
      | inr x =>
        simp only [weightValue,qmaFourExchangeWeight]
        have h := fieldValue_error k (axis x.1) (weight x.1) x.2
        have hm := mul_le_mul_of_nonneg_right (hw x.1) heps
        unfold weightErrorBudget
        nlinarith

variable [Fintype κ] [Fintype τ]

theorem weightValue_ground_error (k : ℕ) (r : ℚ) (left right : κ → Fin n)
    (hne : ∀ e, left e ≠ right e) (a b : κ → Fin 2) (t : κ → ℚ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℚ)
    (s : ℚ) (c B D : ℝ) (hB : 0 ≤ B)
    (ht : ∀ e, |(t e:ℝ)| ≤ B) (hw : ∀ e, |(weight e:ℝ)| ≤ B)
    (hs : |(s:ℝ)-qmaFourExchangeScalar n (r:ℝ) axis (fun e => (weight e:ℝ)) c| ≤ D*(2:ℝ)⁻¹^k) :
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix (qmaFourExchangeLeft left right site)
        (qmaFourExchangeRight left right site) (fun x => (weightValue k r a b t axis weight x:ℝ)) (s:ℝ))-
      MediatorGraph.normalizedBottom (qmaBlockSourceFull (r:ℝ) left right a b (fun e => (t e:ℝ))
        site axis (fun e => (weight e:ℝ)) c)| ≤
      (3*(Fintype.card (QMAFourExchangeIndex n κ τ):ℝ)*weightErrorBudget (r:ℝ) B+D)*(2:ℝ)⁻¹^k := by
  rw [qmaBlockSourceFull_exchange]
  apply (qmaExchangeMatrix_ground_error _ _ (qmaFourExchange_distinct left right site hne) _ _ _ _).trans
  have hsum : (∑ x : QMAFourExchangeIndex n κ τ,
      |(weightValue k r a b t axis weight x:ℝ)-
        qmaFourExchangeWeight (r:ℝ) a b (fun e => (t e:ℝ)) axis (fun e => (weight e:ℝ)) x|) ≤
      (Fintype.card (QMAFourExchangeIndex n κ τ):ℝ)*weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k := by
    calc
      _ ≤ ∑ _x : QMAFourExchangeIndex n κ τ, weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k :=
        Finset.sum_le_sum (fun x _ => weightValue_error k r a b t axis weight B hB ht hw x)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  nlinarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZScalarSample
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed scalar correction for the complete private-pair X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem shiftValue_cast (a : Fin 2) (q : ℚ) :
    (shiftValue a q:ℝ) = qmaFourAxisFieldShift a (q:ℝ) := by
  unfold shiftValue qmaFourAxisFieldShift
  split_ifs <;> norm_num

theorem scalarValue_sub (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    (scalarValue k r t J:ℝ)-qmaFourExchangeScalar n (r:ℝ)
      (fun e => (qmaXZFieldData t e).axis) (fun e => (J e.val:ℝ))
      (qmaXZFamilyConstant t (fun e => (J e:ℝ))) =
    ∑ e : QMAXZPairIndex t,
      (qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val:ℝ)-
        (offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val):ℝ)) := by
  simp only [scalarValue,qmaFourExchangeScalar,qmaXZFamilyConstant,qmaFourTensorFieldShift,
    Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,
    Rat.cast_sum,shiftValue_cast,Finset.sum_sub_distrib]
  ring

theorem scalarValue_error (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    |(scalarValue k r t J:ℝ)-qmaFourExchangeScalar n (r:ℝ)
      (fun e => (qmaXZFieldData t e).axis) (fun e => (J e.val:ℝ))
      (qmaXZFamilyConstant t (fun e => (J e:ℝ)))| ≤
        (320800*(∑ e, |(J e:ℝ)|))*(2:ℝ)⁻¹^k := by
  rw [scalarValue_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e : QMAXZPairIndex t, 320800*|(J e.val:ℝ)| *(2:ℝ)⁻¹^k := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_sub_comm]
      exact offset_error k _ _ _
    _ = (320800*(∑ e : QMAXZPairIndex t, |(J e.val:ℝ)|))*(2:ℝ)⁻¹^k := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (qmaSum_subtype_abs_le (fun e => (t e).IsPair) (fun e => (J e:ℝ)))
        (by norm_num)) (by positivity)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampled rational exchange Hamiltonian approximates the entire logical X/Z family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem matrixValue_error (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    |MediatorGraph.normalizedBottom (matrixValue k r t J)-
      MediatorGraph.normalizedBottom (qmaXZBlockSource (r:ℝ) t (fun e => (J e:ℝ)))| ≤
        matrixErrorBudget r t J*(2:ℝ)⁻¹^k := by
  have hB : 0 ≤ qmaXZInputSize (fun e => (J e:ℝ)) := by unfold qmaXZInputSize; positivity
  have hJ (e : κ) : |(J e:ℝ)| ≤ qmaXZInputSize (fun e => (J e:ℝ)) := by
    apply (Finset.single_le_sum (fun f _ => abs_nonneg (J f:ℝ)) (Finset.mem_univ e)).trans
    unfold qmaXZInputSize
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact weightValue_ground_error k r
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val) (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (scalarValue k r t J) (qmaXZFamilyConstant t (fun e => (J e:ℝ)))
    (qmaXZInputSize (fun e => (J e:ℝ))) (320800*(∑ e, |(J e:ℝ)|)) hB
    (fun e => hJ e.val) (fun e => hJ e.val) (scalarValue_error k r t J)

theorem rationalBudget_cast (J : κ → ℚ) :
    (rationalBudget J:ℝ) = qmaXZPolynomialBudget (fun e => (J e:ℝ)) := by
  simp only [rationalBudget,rationalInputSize,qmaXZPolynomialBudget,qmaXZInputSize,
    Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_sum,Rat.cast_abs,Rat.cast_one]

theorem matrixValue_accuracy (k N : ℕ) (hN : 0 < N) (t : κ → QMAXZTerm n) (J : κ → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (matrixValue k (rationalPenalty N J) t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤
        matrixErrorBudget (rationalPenalty N J) t J*(2:ℝ)⁻¹^k+1/(N:ℝ) := by
  have hsample := matrixValue_error k (rationalPenalty N J) t J
  have hphys := qmaXZBlock_polynomial_accuracy t (fun e => (J e:ℝ)) hprivate N hN
  have hcast : (rationalPenalty N J:ℝ) = 9*(qmaXZPolynomialBudget (fun e => (J e:ℝ)))^3*N := by
    simp only [rationalPenalty,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,rationalBudget_cast]
  rw [← hcast] at hphys
  simpa only [Complex.ofReal_ratCast] using (abs_sub_le _ _ _).trans (add_le_add hsample hphys)

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSamplePrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic precision, computed from binary numerators, suffices for the physical error budget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

theorem rational_le_numerator (q : ℚ) : (q:ℝ) ≤ (q.num.natAbs:ℝ) := by
  have hden : (1:ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q:ℝ) = (q.num:ℝ)/(q.den:ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  have habs : |(q.num:ℝ)| = (q.num.natAbs:ℝ) := by rw [Nat.cast_natAbs,Int.cast_abs]
  calc
    _ ≤ |(q:ℝ)| := le_abs_self _
    _ = |(q.num:ℝ)|/(q.den:ℝ) := by
      rw [he,abs_div,abs_of_nonneg (show (0:ℝ) ≤ q.den by exact_mod_cast Nat.zero_le q.den)]
    _ ≤ |(q.num:ℝ)| := div_le_self (abs_nonneg _) hden
    _ = _ := habs

theorem precision_error (q : ℚ) (N : ℕ) (hN : 0 < N) :
    (q:ℝ)*(2:ℝ)⁻¹^(precision q N) ≤ 1/(N:ℝ) := by
  have ha : (q.num.natAbs:ℝ) ≤ (2:ℝ)^q.num.natAbs.size := by
    exact_mod_cast (Nat.lt_size_self q.num.natAbs).le
  have hb : (N:ℝ) ≤ (2:ℝ)^N.size := by exact_mod_cast (Nat.lt_size_self N).le
  have hprod : (q:ℝ)*(N:ℝ) ≤ (2:ℝ)^(precision q N) := by
    rw [precision,pow_add]
    exact mul_le_mul ((rational_le_numerator q).trans ha) hb (Nat.cast_nonneg _) (by positivity)
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hpow : (0:ℝ) < 2^(precision q N) := by positivity
  have hdiv := (div_le_one hpow).mpr hprod
  apply (le_div_iff₀ hNp).mpr
  convert hdiv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv,inv_pow]
  ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumComputedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computable binary-precision choice closes the full rational four-spin error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem rationalErrorBudget_cast (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    (rationalErrorBudget r t J:ℝ) = matrixErrorBudget r t J := by
  simp only [rationalErrorBudget,matrixErrorBudget,weightErrorBudget,rationalInputSize,qmaXZInputSize,
    Rat.cast_add,Rat.cast_mul,Rat.cast_abs,Rat.cast_sum,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFixedPauliProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal polynomial evaluator for every coefficient of a fixed
local core.  Six is the largest arity used by the history construction;
the finite loops below are part of the fixed program, not the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar ExactQuantumFactoring.BitStackProgram
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumFixedPauli.finDecision
theorem coefficient_matrixData (n : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar) (w : Fin n → Fin 4) :
    realValue (realCoefficient (fun s t => entry (matrixData A) s t) w) =
      (qmaPauliCoefficient (fun s t => value (A s t)) w).re := by
  have he : (fun s t => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  rw [he]
  exact realCoefficient_eq A w

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational-register tables for every actual ordered history term.
Only the propagation core is multiplied, so its summation has at most
32 states regardless of the number of spectator qubits. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem denote_diagonal {α : Type} [DecidableEq α] (f : α → ℚ) :
    denote (diagonal f) = Matrix.diagonal (fun s => (f s:ℂ)) := by
  ext s t
  by_cases h : s = t <;> simp [denote,QuantumAlgebraicHistory.diagonal,h]

theorem denote_distributed (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c) :
    denote (distributed c τ a) = qmaDistributedTermMatrix c τ a := by
  rcases a with i | (b | (i | (u | t)))
  · ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,qmaClockFaultTerm,
      qmaPairDiagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · fin_cases b
    · change denote (QuantumAlgebraicHistory.diagonal
        (fun s : QMACircuitQubit c → Fin 2 => if s (Sum.inl 0) = 1 then 0 else 1)) =
        qmaClockLeftTerm c
      rw [denote_diagonal]
      ext s r
      simp only [qmaClockLeftTerm,qmaBitDiagonal,Matrix.diagonal_apply]
      split_ifs <;> norm_num
    · change denote (QuantumAlgebraicHistory.diagonal
        (fun s : QMACircuitQubit c → Fin 2 =>
          if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)) =
        qmaClockRightTerm c
      rw [denote_diagonal]
      ext s r
      simp only [qmaClockRightTerm,qmaBitDiagonal,Matrix.diagonal_apply]
      split_ifs <;> norm_num
  · ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,
      qmaDistributedInputTerm,Matrix.diagonal_apply]
    split_ifs <;> simp
  · cases u
    ext s r
    simp only [distributed,denote,QuantumAlgebraicHistory.diagonal,qmaDistributedTermMatrix,qmaOutputTerm,
      qmaPairDiagonal,Matrix.diagonal_apply]
    split_ifs <;> simp
  · change (fun s r => value (mul _ (lift _ _ s r))) = _
    simp only [value_mul,value_rat]
    have hl := denote_lift (qmaPropagationSites c t) (propagationCore c t)
    rw [denote_propagationCore] at hl
    have hc := (qmaLocalPropagationGram_local c t).core_lift
    rw [hc] at hl
    ext s r
    have he := congrFun (congrFun hl s) r
    dsimp only [denote] at he
    rw [he]
    simp only [qmaDistributedTermMatrix,Matrix.smul_apply,smul_eq_mul]
    push_cast
    rfl

theorem value_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    value (localY n i s t) = sourceLocalPauli n i 1 s t := by
  rw [localY,value_finiteProduct]
  unfold sourceLocalPauli sourceTensor
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = i
  · simp only [h,ite_true, if_true,value_pauli]
    rfl
  · simp only [h,ite_false, if_false,value_identity]

theorem denote_rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) :
    denote (rebit n i A) = qmaDistributedRebitOnQubits n i (denote A) := by
  rw [qmaDistributedRebitOnQubits_eq]
  ext s t
  simp only [denote,rebit,value_add,value_mul,value_identity,value_realPart,value_imagPart,
    value_neg,value_imaginary,value_localY,qmaJoinMatrix,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.submatrix_apply]
  rfl

theorem value_pairY (n : ℕ) (i j : Fin n) (hne : i ≠ j) (s t : SourceSpinBasis n) :
    value (pairY n i j s t) = (sourceLocalPauli n i 1*sourceLocalPauli n j 1) s t := by
  rw [sourceLocalPauli_product_entry n i j hne]
  simp only [pairY,value_mul,value_pauli]
  have he (a b : Fin 2) : qmaPauli 2 a b = ContinuumCoulomb.pauli 1 a b := rfl
  rw [he,he]
  by_cases h : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [ite_eq_left h,sourceSpectatorDelta_eq_one n i j s t h]
    simp
  · rw [ite_eq_right h,sourceSpectatorDelta_eq_zero n i j s t h]
    simp

theorem denote_referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n) :
    denote (referenceEdge (ι := ι) n i) = qmaReferenceEdgeOnQubits (ι := ι) n i := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have he := congrArg Fin.val h
    simp at he
  ext s t
  simp only [denote,referenceEdge,value_mul,value_rat,value_sub,value_identity,
    value_pairY _ _ _ hne,qmaReferenceEdgeOnQubits,qmaJoinMatrix,qmaReferenceYEdge,
    Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply]
  norm_num
  rfl

theorem denote_orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    denote (orderedTerm c hT a) = (qmaOrderedHistoryModel c hT).matrix a := by
  cases a with
  | inl i =>
    rw [orderedTerm,denote_rebit,denote_distributed]
    rfl
  | inr i =>
    rw [orderedTerm,denote_referenceEdge]
    rfl

theorem denote_orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    denote (orderedCore c hT a) = qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
      ((qmaOrderedHistoryModel c hT).matrix a) := by
  ext s t
  exact congrFun (congrFun (denote_orderedTerm c hT a) _) _

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryHeight
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual rational-register history entries.
The only matrix multiplication takes place on the five-site propagation
core, with at most32 intermediate configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem height_identity {α : Type} [DecidableEq α] (s t : α) :
    height (identity s t) ≤ 1 := by
  by_cases h : s = t <;> simp [identity,h]

theorem height_hadamard (s t : Fin 2) : height (hadamard s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [hadamard,mul,realMul,realSub,realAdd,realNeg,sqrtHalf,
      rat,realRat,height,realHeight]

theorem height_phaseT (s t : Fin 2) : height (phaseT s t) ≤ 2 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [phaseT,mul,realMul,realSub,realAdd,realNeg,QuantumAlgebraicScalar.add,sqrtHalf,
      rat,realRat,imaginary,height,realHeight]

private theorem height_single_product (n : ℕ) (i : Fin n)
    (A : Fin 2 → Fin 2 → Scalar) (hA : ∀ s t, height (A s t) ≤ 2)
    (s t : SourceSpinBasis n) :
    height (finiteProduct (fun k => if k = i then A (s k) (t k)
      else identity (s k) (t k))) ≤ 2 := by
  apply (height_finiteProduct _).trans
  calc
    _ ≤ ∏ k : Fin n, if k = i then (2:ℚ) else 1 := by
      apply Finset.prod_le_prod (fun _ _ => height_nonnegative _)
      intro k _
      by_cases h : k = i
      · simpa only [h,ite_true, if_true] using hA (s k) (t k)
      · simpa only [h,ite_false, if_false] using height_identity (s k) (t k)
    _ = 2 := by simp

theorem height_gate (work : ℕ) (g : QMAGate) (s t : SourceSpinBasis (work+1)) :
    height (gate work g s t) ≤ 2 := by
  cases g with
  | hadamard i => exact height_single_product _ _ _ height_hadamard s t
  | phaseT i => exact height_single_product _ _ _ height_phaseT s t
  | controlledNot i j =>
    dsimp only [gate]
    split_ifs <;> norm_num

theorem height_delta (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMACircuitQubit c → Fin 2) : height (delta c t s r) ≤ 3 := by
  dsimp only [delta]
  split_ifs
  · apply (height_sub _ _).trans
    have hm := height_mul
      (identity (s ∘ Sum.inl) (r ∘ Sum.inl))
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    have hi := height_identity s (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) r)
    have hj := height_identity (s ∘ Sum.inl) (r ∘ Sum.inl)
    have hg := height_gate c.work (c.gates.getD t.val (.hadamard 0))
      (s ∘ Sum.inr) (r ∘ Sum.inr)
    have hn := height_nonnegative
      (gate c.work (c.gates.getD t.val (.hadamard 0)) (s ∘ Sum.inr) (r ∘ Sum.inr))
    nlinarith
  · norm_num

theorem propagation_configurations (c : QMACircuit) (t : Fin c.gates.length) :
    Fintype.card (QMASupportBasis (qmaPropagationSites c t)) ≤ 32 := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (qmaPropagationSites_card c t)
  simpa only [QMASupportBasis,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    show (2:ℕ)^5 = 32 by norm_num] using h

theorem height_propagationCore (c : QMACircuit) (t : Fin c.gates.length)
    (s r : QMASupportBasis (qmaPropagationSites c t)) :
    height (propagationCore c t s r) ≤ 288 := by
  have hentry (u : QMASupportBasis (qmaPropagationSites c t)) :
      height (mul (adjoint (deltaCore c t) s u) (deltaCore c t u r)) ≤ 9 := by
    apply (height_mul _ _).trans
    simp only [adjoint,height_conj,deltaCore]
    calc
      _ ≤ (3:ℚ)*3 := mul_le_mul (height_delta c t _ _) (height_delta c t _ _)
        (height_nonnegative _) (by norm_num)
      _ = 9 := by norm_num
  have hsum := (height_finiteSum (fun u =>
    mul (adjoint (deltaCore c t) s u) (deltaCore c t u r))).trans
      (Finset.sum_le_sum (fun u _ => hentry u))
  have hcard : (Fintype.card (QMASupportBasis (qmaPropagationSites c t)):ℚ) ≤ 32 :=
    Nat.cast_le.mpr (propagation_configurations c t)
  change height (finiteSum _) ≤ 288
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  linarith

theorem height_lift {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (s t : ι → Fin 2) :
    height (lift S A s t) ≤ height (A (fun i => s i.val) (fun i => t i.val)) := by
  apply (height_mul _ _).trans
  simpa using mul_le_mul_of_nonneg_left
    (height_identity (fun i : {i // i ∉ S} => s i.val) (fun i => t i.val))
    (height_nonnegative (A (fun i => s i.val) (fun i => t i.val)))

theorem historyHeight_nonnegative (c : QMACircuit) : 0 ≤ historyHeight c := by
  unfold historyHeight
  positivity

theorem height_distributed (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (a : QMACircuitTerm c)
    (s r : QMACircuitQubit c → Fin 2) :
    height (distributed c τ a s r) ≤ historyHeight c := by
  have h14 : (14:ℚ) ≤ historyHeight c := by
    unfold historyHeight
    have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    linarith
  rcases a with i | (b | (i | (u | t)))
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · by_cases hb : b = 0
    · simp only [distributed,hb,ite_true, if_true,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
    · simp only [distributed,hb,ite_false, if_false,QuantumAlgebraicHistory.diagonal]
      split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · dsimp only [distributed,QuantumAlgebraicHistory.diagonal]
    split_ifs <;> norm_num <;> linarith
  · apply (height_mul _ _).trans
    have hl := (height_lift _ (propagationCore c t) s r).trans
      (height_propagationCore c t _ _)
    have hw : 0 ≤ ((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
    rw [height_rat,abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left hl hw).trans
    unfold historyHeight
    linarith

theorem height_localY (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    height (localY n i s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  apply Finset.prod_le_one (fun _ _ => height_nonnegative _)
  intro k _
  by_cases h : k = i
  · simpa only [h,ite_true, if_true] using height_pauli 2 (s k) (t k)
  · simpa only [h,ite_false, if_false] using height_identity (s k) (t k)

theorem height_rebit {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (s t : Fin n ⊕ ι → Fin 2) :
    height (rebit n i A s t) ≤ 2*height (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_localY n i (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hR := height_realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hJ := height_imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))
  have hYR := height_mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
    (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hIR := height_mul (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))
  have hN := height_mul (neg imaginary)
    (mul (localY n i (s ∘ Sum.inl) (t ∘ Sum.inl))
      (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))))
  simp only [height_neg,height_imaginary,one_mul] at hN
  apply (height_add _ _).trans
  nlinarith [height_nonnegative (realPart (A (s ∘ Sum.inr) (t ∘ Sum.inr))),
    height_nonnegative (imagPart (A (s ∘ Sum.inr) (t ∘ Sum.inr)))]

theorem height_pairY (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) :
    height (pairY n i j s t) ≤ 1 := by
  have hp := (height_mul (QuantumFixedPauli.pauli 2 (s i) (t i)) (QuantumFixedPauli.pauli 2 (s j) (t j))).trans
    (mul_le_mul (height_pauli 2 (s i) (t i)) (height_pauli 2 (s j) (t j))
      (height_nonnegative _) (by norm_num))
  have hδ : height (rat (if ∀ k, k ≠ i → k ≠ j → s k = t k then 1 else 0)) ≤ 1 := by
    split_ifs <;> norm_num
  apply (height_mul _ _).trans
  simpa using mul_le_mul hp hδ (height_nonnegative _) (by norm_num)

theorem height_referenceEdge {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (s t : Fin (n+1) ⊕ ι → Fin 2) :
    height (referenceEdge n i s t) ≤ 1 := by
  have hI := height_identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hY := height_pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)
  have hS := height_sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
    (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl))
  have hhalf := height_mul (rat (1/2))
    (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
      (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))
  norm_num only [height_rat,abs_of_pos (by norm_num : (0:ℚ) < 1/2)] at hhalf
  have hB : height (mul (rat (1/2))
      (sub (identity (s ∘ Sum.inl) (t ∘ Sum.inl))
        (pairY (n+1) i.castSucc i.succ (s ∘ Sum.inl) (t ∘ Sum.inl)))) ≤ 1 := by
    linarith
  apply (height_mul _ _).trans
  simpa using mul_le_mul hB (height_identity (s ∘ Sum.inr) (t ∘ Sum.inr))
    (height_nonnegative _) (by norm_num)

theorem height_orderedTerm (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c → Fin 2) :
    height (orderedTerm c hT a s t) ≤ 2*historyHeight c := by
  cases a with
  | inl i =>
    exact (height_rebit _ _ _ s t).trans
      (mul_le_mul_of_nonneg_left (height_distributed c _ _ _ _) (by norm_num))
  | inr i =>
    apply (height_referenceEdge _ _ s t).trans
    have h : (14:ℚ) ≤ historyHeight c := by
      unfold historyHeight
      have hn : 0 ≤ 288*((14*(c.work+1)+8)*c.gates.length:ℚ) := by positivity
      linarith
    linarith

theorem height_orderedCore (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : QMASupportBasis ((qmaOrderedHistoryModel c hT).sites a)) :
    height (orderedCore c hT a s t) ≤ 2*historyHeight c :=
  height_orderedTerm c hT a _ _

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPauliRounding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding a finite Pauli family controls its actual full-space ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem qmaPauliFamily_norm (w : κ → ι → Fin 4) (J : κ → ℝ) :
    ‖spinMatrixOperator (qmaPauliFamily w J)‖ ≤ ∑ e, |J e| := by
  rw [qmaPauliFamily,spinMatrixOperator_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (spinMatrixOperator_unitary_norm _ (qmaPauliWord_gram _)) (abs_nonneg _)).trans_eq (mul_one _)

omit [DecidableEq ι] in
theorem qmaPauliFamily_sub (w : κ → ι → Fin 4) (J K : κ → ℝ) :
    qmaPauliFamily w J-qmaPauliFamily w K = qmaPauliFamily w (fun e => J e-K e) := by
  simp only [qmaPauliFamily,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem qmaPauliFamily_ground_error (w : κ → ι → Fin 4) (J K : κ → ℝ) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w K)| ≤ ∑ e, |J e-K e| := by
  apply qmaNormalizedBottom_norm_error _ _
    (EuclideanSpace.single (fun _ => (0:Fin 2)) 1) (by simp [PiLp.norm_single])
  rw [qmaPauliFamily_sub]
  exact qmaPauliFamily_norm w _

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit unary precision controls the total error of all actual
ordered-history coefficients.  The precision is polynomial in the circuit
size and the requested inverse error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators Classical

theorem coefficientBudget_cast (c : QMACircuit) :
    (coefficientBudget c:ℚ) = 128*historyHeight c := by
  simp only [coefficientBudget,historyHeight,Nat.cast_mul,Nat.cast_add,
    Nat.cast_one,Nat.cast_ofNat]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZTerm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic X/Z term classification from a list of at most two sites.
The order of pair endpoints is the supplied order, with no finite-set choice. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZTerm
open scoped Classical

theorem axis_spec (a : Fin 4) (h0 : a ≠ 0) (h2 : a ≠ 2) :
    qmaXZLabel (axis a) = a := by
  fin_cases a <;> simp_all [axis,qmaXZLabel]

private theorem outside {n : ℕ} (w : Fin n → Fin 4) (xs : List (Fin n))
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (i : Fin n) (hi : i ∉ xs) : w i = 0 := by
  by_contra h
  have hm := hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hi (List.mem_toFinset.mp hm)

theorem field_word {n : ℕ} (w : Fin n → Fin 4) (i k : Fin n)
    (hy : w i ≠ 2) : (field w i).word k = if k = i then w i else 0 := by
  by_cases hz : w i = 0
  · simp [field,hz,QMAXZTerm.word]
  · simp only [field,hz,ite_false, if_false,QMAXZTerm.word,axis_spec _ hz hy]

theorem word_eq {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4)
    (hlen : xs.length ≤ 2) (hx : xs.Nodup)
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (hy : ∀ i, w i ≠ 2) :
    (ofSites xs w).word = w := by
  cases xs with
  | nil =>
    funext k
    exact (outside w [] hs k (by simp)).symm
  | cons i xs =>
    cases xs with
    | nil =>
      funext k
      rw [ofSites,field_word w i k (hy i)]
      by_cases hk : k = i
      · simp [hk]
      · simpa [hk] using (outside w [i] hs k (by simp [hk])).symm
    | cons j xs =>
      cases xs with
      | cons l xs => simp at hlen
      | nil =>
        have hij : i ≠ j := by simpa using hx
        rw [ofSites,dite_eq_right hij]
        split_ifs with hi hj
        · funext k
          rw [field_word w j k (hy j)]
          by_cases hkj : k = j
          · simp [hkj]
          · by_cases hki : k = i
            · simp [hki,hi,hij]
            · simpa [hkj] using (outside w [i,j] hs k (by simp [hki,hkj])).symm
        · funext k
          rw [field_word w i k (hy i)]
          by_cases hki : k = i
          · simp [hki]
          · by_cases hkj : k = j
            · simp [hkj,hj,Ne.symm hij]
            · simpa [hki] using (outside w [i,j] hs k (by simp [hki,hkj])).symm
        · funext k
          simp only [QMAXZTerm.word,axis_spec _ hi (hy i),axis_spec _ hj (hy j)]
          by_cases hki : k = i
          · simp [hki]
          · by_cases hkj : k = j
            · simp [hkj,Ne.symm hij]
            · simpa [hki,hkj] using (outside w [i,j] hs k (by simp [hki,hkj])).symm

theorem matrix_eq {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4)
    (hlen : xs.length ≤ 2) (hx : xs.Nodup)
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (hy : ∀ i, w i ≠ 2) :
    (ofSites xs w).matrix = qmaPauliWord w := by
  rw [← QMAXZTerm.word_matrix,word_eq xs w hlen hx hs hy]

end ContinuumCoulomb.QuantumOrderedXZTerm

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal short support lists for the time-ordered history compiler.
The list order, duplicate removal, and local-coordinate equivalence are
explicit; no arbitrary finite-type enumeration enters the input algorithm. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (i : Fin (sites c hT a).length) :
    (supportEquiv c hT a i).val = (sites c hT a).get i := rfl

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSplit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic balanced support factors.  The actual compiler carries
ordered lists of sites and splits them with take/drop; no chosen finite
subset is needed by either subdivision stage. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSplit
open Matrix
open scoped BigOperators Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem union (xs : List ι) (d : ℕ) : left xs d ∪ right xs d = xs.toFinset := by
  rw [left,right,← List.toFinset_append,List.take_append_drop]

omit [Fintype ι] in
theorem disjoint (xs : List ι) (hx : xs.Nodup) (d : ℕ) :
    Disjoint (left xs d) (right xs d) := by
  apply List.disjoint_toFinset_iff_disjoint.mpr
  apply List.disjoint_of_nodup_append
  simpa only [List.take_append_drop] using hx

omit [Fintype ι] in
theorem left_card (xs : List ι) (d : ℕ) : (left xs d).card ≤ d := by
  exact (List.toFinset_card_le _).trans (by simp)

omit [Fintype ι] in
theorem right_card (xs : List ι) (d : ℕ) (hx : xs.length ≤ 2*d) :
    (right xs d).card ≤ d := by
  apply (List.toFinset_card_le _).trans
  rw [List.length_drop]
  omega

theorem first_support (xs : List ι) (d : ℕ) (w : ι → Fin 4) :
    (qmaPauliSupport (firstWord xs d w)).card ≤ d :=
  (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (left_card xs d)

theorem second_support (xs : List ι) (d : ℕ) (w : ι → Fin 4)
    (hx : xs.length ≤ 2*d) : (qmaPauliSupport (secondWord xs d w)).card ≤ d :=
  (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (right_card xs d hx)

theorem factor (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4)
    (hw : qmaPauliSupport w ⊆ xs.toFinset) :
    qmaPauliWord (firstWord xs d w)*qmaPauliWord (secondWord xs d w) = qmaPauliWord w := by
  apply qmaPauliRestrict_factor _ _ _ (disjoint xs hx d)
  rwa [union]

theorem commute (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4) :
    qmaPauliWord (firstWord xs d w)*qmaPauliWord (secondWord xs d w) =
      qmaPauliWord (secondWord xs d w)*qmaPauliWord (firstWord xs d w) :=
  qmaPauliRestrict_commute _ _ _ (disjoint xs hx d)

theorem same_parity (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4)
    (hw : qmaPauliSupport w ⊆ xs.toFinset) (he : Even (qmaPauliYCount w)) :
    decide (Odd (qmaPauliYCount (firstWord xs d w))) =
      decide (Odd (qmaPauliYCount (secondWord xs d w))) := by
  apply qmaPauliRestrict_same_parity _ _ _ (disjoint xs hx d) _ he
  rwa [union]

end ContinuumCoulomb.QuantumOrderedSplit

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPolarizedSubdivision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal four-word subdivision for even-Y interactions.  The mediator
letter is Y precisely when each input factor has odd Y parity.  All output
coefficients are rational when the input coefficient and scale are rational. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem single_flip (m : κ → Bool) (e : κ) :
    qmaPauliWord (qmaSinglePauliWord e (axis (m e))) = qmaPolarizedFlip m e := by
  cases hm : m e
  · simpa only [axis,hm,Bool.false_eq_true,ite_false, if_false,qmaPolarizedFlip_eq] using
      qmaSinglePauliWord_X e
  · have hY (u v : Fin 2) : qmaPauli 2 u v =
        if u = Equiv.swap (0:Fin 2) 1 v then
          (if v = 1 then -Complex.I else Complex.I) else 0 := by
      fin_cases u <;> fin_cases v <;>
        simp [qmaPauli,pauliY,Equiv.swap_apply_def, Fin.ext_iff] <;> norm_num
    ext s t
    simp only [axis,hm,ite_true, if_true,qmaSinglePauliWord_apply,hY,qmaPolarizedFlip]
    by_cases h : s = qmaBitFlip e t
    · subst s
      have he : qmaBitFlip e t e = Equiv.swap (0:Fin 2) 1 (t e) := by simp [qmaBitFlip]
      rw [ite_eq_left he,ite_eq_left rfl]
      have hp : (∏ k ∈ Finset.univ.erase e,
          if qmaBitFlip e t k = t k then (1:ℂ) else 0) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp [qmaBitFlip,(Finset.mem_erase.mp hk).1]
      rw [hp,mul_one]
    · rw [ite_eq_right h]
      obtain ⟨k,hk⟩ := Function.ne_iff.mp h
      by_cases hke : k = e
      · subst k
        have he : s e ≠ Equiv.swap (0:Fin 2) 1 (t e) := by simpa [qmaBitFlip] using hk
        rw [ite_eq_right he,zero_mul]
      · have he : s k ≠ t k := by simpa [qmaBitFlip,hke] using hk
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hke,Finset.mem_univ _⟩)
          (ite_eq_right he),mul_zero]

theorem weight_cast (R j : ℚ) (k : Fin 4) :
    (weight R j k : ℝ) = qmaXZSubdivisionWeight (R:ℝ) (j:ℝ) k := by
  fin_cases k <;> simp [weight,qmaXZSubdivisionWeight]

omit [DecidableEq ι] [DecidableEq κ] in
theorem yCount_join (a : ι → Fin 4) (b : κ → Fin 4) :
    qmaPauliYCount (Sum.elim a b) = qmaPauliYCount a+qmaPauliYCount b := by
  simp only [qmaPauliYCount,Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

theorem yCount_single (e : κ) (μ : Fin 4) :
    qmaPauliYCount (qmaSinglePauliWord e μ) = if μ = 2 then 1 else 0 := by
  have hset : Finset.univ.filter (fun i => qmaSinglePauliWord e μ i = 2) =
      if μ = 2 then {e} else ∅ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hm : μ = 2 <;> by_cases hi : i = e <;>
      simp [qmaSinglePauliWord,hi,hm]
  rw [qmaPauliYCount,hset]
  split_ifs <;> simp

omit [DecidableEq ι] in
private theorem parity_padding (v : ι → Fin 4) :
    Even (qmaPauliYCount v+if axis (decide (Odd (qmaPauliYCount v))) = 2 then 1 else 0) := by
  by_cases h : Odd (qmaPauliYCount v)
  · simp [axis,h]
  · simpa [axis,h] using (Nat.even_or_odd (qmaPauliYCount v)).resolve_right h

omit [DecidableEq ι] in
theorem even (a b : ι → Fin 4) (e : κ) (m : κ → Bool)
    (ha : m e = decide (Odd (qmaPauliYCount a)))
    (hb : m e = decide (Odd (qmaPauliYCount b))) (k : Fin 4) :
    Even (qmaPauliYCount (word a b e m k)) := by
  fin_cases k
  · simp [word,qmaPauliYCount]
  · change Even (qmaPauliYCount (Sum.elim (fun _ : ι => 0) (qmaSinglePauliWord e 3)))
    rw [yCount_join,yCount_single]
    simp [qmaPauliYCount]
  · change Even (qmaPauliYCount (Sum.elim a (qmaSinglePauliWord e (axis (m e)))))
    rw [yCount_join,yCount_single,ha]
    exact parity_padding a
  · change Even (qmaPauliYCount (Sum.elim b (qmaSinglePauliWord e (axis (m e)))))
    rw [yCount_join,yCount_single,hb]
    exact parity_padding b

end ContinuumCoulomb.QuantumPolarizedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSubdivision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit simultaneous subdivision of an ordered rational Pauli
family.  This is the actual four-word Hamiltonian, with a rational scale
and a full-space ground-energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem budget_cast (J : κ → ℚ) :
    (budget J:ℝ) = qmaThirdBudget 0 (fun e => (J e:ℝ)) := by
  simp [budget,qmaThirdBudget,qmaThirdWeight]

omit [DecidableEq κ] in
theorem scale_cast (J : κ → ℚ) (N : ℕ) :
    (scale J N:ℝ) = 8*(qmaThirdBudget 0 (fun e => (J e:ℝ)))^4*N := by
  simp [scale,budget_cast]

theorem output_even (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (hxs : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) :
    Even (qmaPauliYCount (outputWord xs d w p)) := by
  exact QuantumPolarizedSubdivision.even
    (QuantumOrderedSplit.firstWord (xs p.1) d (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) d (w p.1)) p.1 (phase xs d w) rfl
    (QuantumOrderedSplit.same_parity (xs p.1) (hxs p.1) d (w p.1)
      (hcover p.1) (he p.1)) p.2

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTriple
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A deterministic three-site partition for the third-order gadget.
For three sites the last factor is the first available non-Y letter;
shorter lists give an empty last factor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type}

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem partition_cover (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3) :
    (partition xs w).1.toFinset ∪ (partition xs w).2.toFinset = xs.toFinset := by
  rw [← List.toFinset_append]
  ext i
  simp only [List.mem_toFinset]
  exact (partition_spec xs w hlen).1.mem_iff

omit [Fintype ι] in
theorem partition_disjoint (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) :
    Disjoint (partition xs w).1.toFinset (partition xs w).2.toFinset :=
  List.disjoint_toFinset_iff_disjoint.mpr
    (List.disjoint_of_nodup_append (partition_nodup xs w hlen hx))

private theorem not_three_y (a b c : ι) (w : ι → Fin 4)
    (hx : [a,b,c].Nodup) (hcover : qmaPauliSupport w ⊆ [a,b,c].toFinset)
    (he : Even (qmaPauliYCount w)) : ¬(w a = 2 ∧ w b = 2 ∧ w c = 2) := by
  rintro ⟨ha,hb,hc⟩
  have hs : Finset.univ.filter (fun i => w i = 2) = [a,b,c].toFinset := by
    ext i
    constructor
    · intro hi
      have hy := (Finset.mem_filter.mp hi).2
      exact hcover (by simp [qmaPauliSupport,hy])
    · intro hi
      have hi' : i = a ∨ i = b ∨ i = c := by simpa using hi
      rcases hi' with rfl | rfl | rfl <;> simp [ha,hb,hc]
  have hcount : qmaPauliYCount w = 3 := by
    rw [qmaPauliYCount,hs,List.toFinset_card_of_nodup hx]
    rfl
  rw [hcount] at he
  norm_num at he

theorem real_part (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : ∀ i ∈ (partition xs w).2, w i ≠ 2 := by
  cases xs with
  | nil => simp [partition]
  | cons a xs =>
    cases xs with
    | nil => simp [partition]
    | cons b xs =>
      cases xs with
      | nil => simp [partition]
      | cons c xs =>
        cases xs with
        | nil =>
          by_cases ha : w a = 2
          · by_cases hb : w b = 2
            · have hc : w c ≠ 2 := fun hc => not_three_y a b c w hx hcover he ⟨ha,hb,hc⟩
              simp [partition,ha,hb,hc]
            · simp [partition,ha,hb]
          · simp [partition,ha]
        | cons d xs => simp at hlen; omega

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTripleFactors
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Pauli factors from the ordered three-site partition.  The first
two factors have matching Y parity and the last is real. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem third_yCount (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : qmaPauliYCount (third xs w) = 0 := by
  apply qmaPauliYCount_zero
  intro i
  by_cases hi : i ∈ (partition xs w).2.toFinset
  · simpa only [third,qmaPauliRestrict,hi,ite_true, if_true] using
      real_part xs w hlen hx hcover he i (List.mem_toFinset.mp hi)
  · simp [third,qmaPauliRestrict,hi]

theorem pair_even (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : Even (qmaPauliYCount (pairWord xs w)) := by
  have hs := qmaPauliYCount_split (partition xs w).1.toFinset
    (partition xs w).2.toFinset w (partition_disjoint xs w hlen hx)
    (by rw [partition_cover xs w hlen]; exact hcover)
  change qmaPauliYCount (pairWord xs w)+qmaPauliYCount (third xs w) = qmaPauliYCount w at hs
  rw [third_yCount xs w hlen hx hcover he,add_zero] at hs
  rwa [hs]

theorem factors (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (qmaPauliSupport (first xs w)).card ≤ 1 ∧
    (qmaPauliSupport (second xs w)).card ≤ 1 ∧
    (qmaPauliSupport (third xs w)).card ≤ 1 ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w) = qmaPauliWord (pairWord xs w) ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w)*qmaPauliWord (third xs w) = qmaPauliWord w ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w) =
      qmaPauliWord (second xs w)*qmaPauliWord (first xs w) ∧
    qmaPauliWord (first xs w)*qmaPauliWord (third xs w) =
      qmaPauliWord (third xs w)*qmaPauliWord (first xs w) ∧
    qmaPauliWord (second xs w)*qmaPauliWord (third xs w) =
      qmaPauliWord (third xs w)*qmaPauliWord (second xs w) ∧
    decide (Odd (qmaPauliYCount (first xs w))) =
      decide (Odd (qmaPauliYCount (second xs w))) ∧
    Even (qmaPauliYCount (third xs w)) := by
  let P := (partition xs w).1.toFinset
  let C := (partition xs w).2.toFinset
  let L := QuantumOrderedSplit.left (partition xs w).1 1
  let T := QuantumOrderedSplit.right (partition xs w).1 1
  have hplen := (partition_spec xs w hlen).2.1
  have hclen := (partition_spec xs w hlen).2.2
  have hPC : Disjoint P C := partition_disjoint xs w hlen hx
  have hwhole : P ∪ C = xs.toFinset := partition_cover xs w hlen
  have hLT : Disjoint L T := QuantumOrderedSplit.disjoint _ (pair_nodup xs w hlen hx) 1
  have hunion : L ∪ T = P := QuantumOrderedSplit.union _ 1
  have hLP : L ⊆ P := by rw [← hunion]; exact Finset.subset_union_left
  have hTP : T ⊆ P := by rw [← hunion]; exact Finset.subset_union_right
  have hvcover : qmaPauliSupport (pairWord xs w) ⊆ L ∪ T := by
    rw [hunion]
    exact qmaPauliRestrict_support _ _
  have hc0 := third_yCount xs w hlen hx hcover he
  have hv : Even (qmaPauliYCount (pairWord xs w)) := by
    have hs := qmaPauliYCount_split P C w hPC (by rw [hwhole]; exact hcover)
    change qmaPauliYCount (pairWord xs w)+qmaPauliYCount (third xs w) = qmaPauliYCount w at hs
    rw [hc0,add_zero] at hs
    rwa [hs]
  have hab : qmaPauliWord (first xs w)*qmaPauliWord (second xs w) =
      qmaPauliWord (pairWord xs w) := by
    have h := qmaPauliRestrict_factor L T (pairWord xs w) hLT hvcover
    change qmaPauliWord (qmaPauliRestrict L (qmaPauliRestrict P w)) *
      qmaPauliWord (qmaPauliRestrict T (qmaPauliRestrict P w)) = qmaPauliWord (pairWord xs w) at h
    rw [qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] at h
    exact h
  refine ⟨QuantumOrderedSplit.first_support _ 1 w,
    QuantumOrderedSplit.second_support _ 1 w hplen,
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans
      ((List.toFinset_card_le _).trans hclen),hab,?_,?_,?_,?_,?_,?_⟩
  · rw [hab]
    exact qmaPauliRestrict_factor P C w hPC (by rw [hwhole]; exact hcover)
  · exact qmaPauliRestrict_commute L T w hLT
  · exact qmaPauliRestrict_commute L C w (hPC.mono_left hLP)
  · exact qmaPauliRestrict_commute T C w (hPC.mono_left hTP)
  · have h := qmaPauliRestrict_same_parity L T (pairWord xs w) hLT hvcover hv
    change decide (Odd (qmaPauliYCount (qmaPauliRestrict L (qmaPauliRestrict P w)))) =
      decide (Odd (qmaPauliYCount (qmaPauliRestrict T (qmaPauliRestrict P w)))) at h
    rw [qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] at h
    exact h
  · rw [hc0]
    norm_num

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPolarizedThird
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Seven literal rational Pauli words for the real-preserving third-order
gadget.  The two possibly imaginary factors use the same mediator phase. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolarizedThird
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sum_eq (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool) (R j : ℚ)
    (hab : qmaPauliWord a*qmaPauliWord b = qmaPauliWord v) :
    (∑ k, (weight R j k : ℂ) • qmaPauliWord (word a b c v e m k)) =
      ∑ k, qmaThirdPhasedLocalPiece (qmaPauliWord a) (qmaPauliWord b)
        (qmaPauliWord c) e (R:ℝ) (j:ℝ) m k := by
  have hI : qmaJoinMatrix (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
      (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) = 1 := by
    simp [qmaJoinMatrix,Matrix.submatrix_one_equiv]
  simp only [word,weight,qmaThirdPhasedLocalPiece_eq,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    qmaPauliWord_zero,← qmaPauliWord_join,QuantumPolarizedSubdivision.single_flip,
    qmaJoinOccupation_expand,hI,hab]
  have hr (r : ℝ) (M : Matrix (ι ⊕ κ → Fin 2) (ι ⊕ κ → Fin 2) ℂ) :
      r • M = (r:ℂ) • M := rfl
  simp only [hr]
  push_cast
  module

omit [DecidableEq ι] in
theorem even (a b c v : ι → Fin 4) (e : κ) (m : κ → Bool)
    (ha : m e = decide (Odd (qmaPauliYCount a)))
    (hb : m e = decide (Odd (qmaPauliYCount b)))
    (hc : Even (qmaPauliYCount c)) (hv : Even (qmaPauliYCount v)) (k : Fin 7) :
    Even (qmaPauliYCount (word a b c v e m k)) := by
  have hsub := QuantumPolarizedSubdivision.even a b e m ha hb
  have hz : qmaPauliYCount (fun _ : κ => (0:Fin 4)) = 0 := by simp [qmaPauliYCount]
  fin_cases k
  · simp [word,qmaPauliYCount]
  · exact hsub 1
  · change Even (qmaPauliYCount (Sum.elim v (fun _ : κ => 0)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,hz,add_zero] using hv
  · change Even (qmaPauliYCount (Sum.elim c (fun _ : κ => 0)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,hz,add_zero] using hc
  · change Even (qmaPauliYCount (Sum.elim c (qmaSinglePauliWord e 3)))
    simpa only [QuantumPolarizedSubdivision.yCount_join,
      QuantumPolarizedSubdivision.yCount_single,show (3:Fin 4) ≠ 2 by decide,
      ite_false, if_false,add_zero] using hc
  · exact hsub 2
  · exact hsub 3

end ContinuumCoulomb.QuantumPolarizedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedThird
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal simultaneous rational three-to-two-local reduction, with
ordered factors and an ordinary full-Hilbert-space energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open Matrix QuantumOrderedTriple
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem output_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 7) :
    Even (qmaPauliYCount (outputWord xs w p)) := by
  obtain ⟨_,_,_,_,_,_,_,_,hpar,hc⟩ := factors (xs p.1) (w p.1) (hlen p.1)
    (hx p.1) (hcover p.1) (he p.1)
  exact QuantumPolarizedThird.even (first (xs p.1) (w p.1))
    (second (xs p.1) (w p.1)) (third (xs p.1) (w p.1))
    (pairWord (xs p.1) (w p.1)) p.1 (phase xs w) rfl hpar hc
    (pair_even _ _ (hlen p.1) (hx p.1) (hcover p.1) (he p.1)) p.2

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let A := fun e => qmaPauliWord (first (xs e) (w e))
  let B := fun e => qmaPauliWord (second (xs e) (w e))
  let C := fun e => qmaPauliWord (third (xs e) (w e))
  let m := phase xs w
  have hf (e : κ) := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  have hpair (e : κ) : A e*B e = qmaPauliWord (pairWord (xs e) (w e)) := (hf e).2.2.2.1
  have habc (e : κ) : A e*B e*C e = qmaPauliWord (w e) := (hf e).2.2.2.2.1
  have hab (e : κ) : A e*B e = B e*A e := (hf e).2.2.2.2.2.1
  have hac (e : κ) : A e*C e = C e*A e := (hf e).2.2.2.2.2.2.1
  have hbc (e : κ) : B e*C e = C e*B e := (hf e).2.2.2.2.2.2.2.1
  have hsum : qmaPauliFamily (outputWord xs w) (fun p => (outputCoefficient J N p:ℝ)) =
      (qmaThirdPhased 0 A B C (QuantumOrderedSubdivision.scale J N:ℝ)
        (fun e => (J e:ℝ)) m).submatrix
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) := by
    have hc (q : ℚ) : ((q:ℝ):ℂ) = (q:ℂ) := by norm_cast
    simp only [qmaPauliFamily,Fintype.sum_prod_type,outputWord,outputCoefficient,hc]
    simp_rw [QuantumPolarizedThird.sum_eq _ _ _ _ _ _ _ _ (hpair _)]
    rw [qmaThirdPhased_decomposition]
    simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum]
    rfl
  have htarget : qmaThirdSeriesTarget 0 A B C (fun e => ((J e:ℝ):ℂ)) =
      qmaPauliFamily w (fun e => (J e:ℝ)) := by
    simp only [qmaThirdSeriesTarget,zero_add,habc,qmaPauliFamily]
  rw [hsum,MediatorGraph.normalizedBottom_reindex,qmaThirdPhased_bottom,← htarget]
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaThirdGadget_polynomial_accuracy 0 A B C (fun e => (J e:ℝ))
    (by norm_num : (0:ℝ) ≤ 0) hNR Matrix.conjTranspose_zero (by simp)
    (fun _ => qmaPauliWord_hermitian _) (fun _ => qmaPauliWord_hermitian _)
    (fun _ => qmaPauliWord_hermitian _)
    (fun _ => qmaPauliWord_square _) (fun _ => qmaPauliWord_square _)
    (fun _ => qmaPauliWord_square _) hab hac hbc
    (EuclideanSpace.single (fun _ : ι => (0:Fin 2)) (1:ℂ)) (by simp [PiLp.norm_single])
  simpa only [QuantumOrderedSubdivision.scale_cast] using h

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSubdivisionSites
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered site lists for each of the four subdivision terms.
The two finite subdivision stages reuse these lists, rather than selecting
a new support from an existential locality certificate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open scoped Classical

variable {ι κ : Type}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem join_support_cover (xs : List ι) (a : ι → Fin 4)
    (ha : qmaPauliSupport a ⊆ xs.toFinset) (e : κ) (μ : Fin 4) :
    qmaPauliSupport (Sum.elim a (qmaSinglePauliWord e μ)) ⊆
      (appendMediator xs e).toFinset := by
  intro x hx
  cases x with
  | inl i =>
      have hi : i ∈ qmaPauliSupport a := by simpa [qmaPauliSupport] using hx
      have him := ha hi
      simpa [appendMediator] using him
  | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e μ) := by
        simpa [qmaPauliSupport] using hx
      have hje := qmaSinglePauliWord_support e μ hj
      have he : j = e := by simpa using hje
      simp [appendMediator,he]

theorem outputSites_cover (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs d w p) ⊆ (outputSites xs d p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,QuantumPolarizedSubdivision.word,qmaPauliSupport] at hx
    | inr j =>
        have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
          simpa [outputWord,QuantumPolarizedSubdivision.word,qmaPauliSupport] using hx
        have hje := qmaSinglePauliWord_support e 3 hj
        simpa [outputSites] using hje
  · exact join_support_cover ((xs e).take d)
      (QuantumOrderedSplit.firstWord (xs e) d (w e))
      (qmaPauliRestrict_support _ _) e _
  · exact join_support_cover ((xs e).drop d)
      (QuantumOrderedSplit.secondWord (xs e) d (w e))
      (qmaPauliRestrict_support _ _) e _

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedThirdSites
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ordered support lists for the seven emitted third-order terms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open QuantumOrderedTriple QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem lift_support_cover (xs : List ι) (w : ι → Fin 4)
    (h : qmaPauliSupport w ⊆ xs.toFinset) :
    qmaPauliSupport (Sum.elim w (fun _ : κ => 0)) ⊆ (xs.map Sum.inl).toFinset := by
  intro x hx
  cases x with
  | inl i =>
    have hi : i ∈ qmaPauliSupport w := by simpa [qmaPauliSupport] using hx
    simpa using h hi
  | inr j => simp [qmaPauliSupport] at hx

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) (p : κ × Fin 7) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs w p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,QuantumPolarizedThird.word,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,QuantumPolarizedThird.word,qmaPauliSupport] using hx
      have hje := qmaSinglePauliWord_support e 3 hj
      simpa [outputSites] using hje
  · exact lift_support_cover _ (pairWord (xs e) (w e)) (qmaPauliRestrict_support _ _)
  · exact lift_support_cover _ (third (xs e) (w e)) (qmaPauliRestrict_support _ _)
  · exact join_support_cover _ (third (xs e) (w e)) (qmaPauliRestrict_support _ _) e 3
  · exact join_support_cover _ (first (xs e) (w e)) (qmaPauliRestrict_support _ _) e _
  · exact join_support_cover _ (second (xs e) (w e)) (qmaPauliRestrict_support _ _) e _

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumXZSupportFactors
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! X/Z factorizations can be chosen inside the original Pauli support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaTwoPauliYY_support_eq (i j : ι) :
    qmaPauliSupport (qmaTwoPauliWord i j 2 2) = {i,j} := by
  ext k
  simp only [qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [qmaTwoPauliWord,hki,hkj]


end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedYYFactors
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal XZ/ZX factors for the only possible real two-site Y term. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem classify (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 2)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (∀ i, w i ≠ 2) ∨ ∃ a b, xs = [a,b] ∧ a ≠ b ∧ w = qmaTwoPauliWord a b 2 2 := by
  have hs : (qmaPauliSupport w).card ≤ 2 :=
    (Finset.card_le_card hcover).trans ((List.toFinset_card_le _).trans hlen)
  rcases qmaTwoLocalEvenY_cases w hs he with h | ⟨i,j,hij,rfl⟩
  · exact Or.inl h
  · right
    rw [qmaTwoPauliYY_support_eq] at hcover
    have htwo : 2 ≤ xs.length := calc
      2 = ({i,j} : Finset ι).card := by simp [hij]
      _ ≤ xs.toFinset.card := Finset.card_le_card hcover
      _ ≤ xs.length := List.toFinset_card_le _
    have hshape : ∃ a b, xs = [a,b] := by
      cases xs with
      | nil => simp at htwo
      | cons a ys =>
        cases ys with
        | nil => simp at htwo
        | cons b zs =>
          cases zs with
          | nil => exact ⟨a,b,rfl⟩
          | cons c zs => simp at hlen
    obtain ⟨a,b,rfl⟩ := hshape
    have hab : a ≠ b := by simpa using hx
    have heq : ({i,j} : Finset ι) = [a,b].toFinset :=
      Finset.eq_of_subset_of_card_le hcover (by simp [hij,hab])
    have ha : a = i ∨ a = j := by
      have : a ∈ ({i,j} : Finset ι) := by rw [heq]; simp
      simpa using this
    have hb : b = i ∨ b = j := by
      have : b ∈ ({i,j} : Finset ι) := by rw [heq]; simp
      simpa using this
    refine ⟨a,b,rfl,hab,?_⟩
    funext k
    by_cases hka : k = a
    · subst k
      rcases ha with rfl | rfl <;> simp [qmaTwoPauliWord]
    · by_cases hkb : k = b
      · subst k
        rcases hb with rfl | rfl <;> simp [qmaTwoPauliWord,hka]
      · have hki : k ≠ i := by
          intro hki
          have : k ∈ [a,b].toFinset := hcover (by simp [hki])
          simp [hka,hkb] at this
        have hkj : k ≠ j := by
          intro hkj
          have : k ∈ [a,b].toFinset := hcover (by simp [hkj])
          simp [hka,hkb] at this
        simp [qmaTwoPauliWord,hka,hkb,hki,hkj]

omit [Fintype ι] in
private theorem factor_noY (xs : List ι) (w : ι → Fin 4) (h : ∀ i, w i ≠ 2) :
    factor xs w = (w,fun _ => 0) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => simp [factor,h]
      | cons c xs => rfl

theorem factors (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 2)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (∀ i, (factor xs w).1 i ≠ 2) ∧ (∀ i, (factor xs w).2 i ≠ 2) ∧
    qmaPauliSupport (factor xs w).1 ⊆ xs.toFinset ∧
    qmaPauliSupport (factor xs w).2 ⊆ xs.toFinset ∧
    qmaPauliWord (factor xs w).1*qmaPauliWord (factor xs w).2 = qmaPauliWord w ∧
    qmaPauliWord (factor xs w).1*qmaPauliWord (factor xs w).2 =
      qmaPauliWord (factor xs w).2*qmaPauliWord (factor xs w).1 := by
  rcases classify xs w hlen hx hcover he with h | ⟨a,b,rfl,hab,rfl⟩
  · rw [factor_noY xs w h]
    refine ⟨h,by simp,hcover,by simp [qmaPauliSupport],?_,?_⟩
    · simp only [qmaPauliWord_zero,Matrix.mul_one]
    · simp only [qmaPauliWord_zero,Matrix.mul_one,Matrix.one_mul]
  · simp only [factor,qmaTwoPauliWord,ite_true, if_true]
    change (∀ i, qmaTwoPauliWord a b 1 3 i ≠ 2) ∧
      (∀ i, qmaTwoPauliWord a b 3 1 i ≠ 2) ∧ _
    refine ⟨?_,?_,?_,?_,qmaYY_factor a b hab,qmaYY_factor_commute a b hab⟩
    · intro i; simp only [qmaTwoPauliWord]; split_ifs <;> decide
    · intro i; simp only [qmaTwoPauliWord]; split_ifs <;> decide
    · simpa using qmaTwoPauliWord_support a b 1 3
    · simpa using qmaTwoPauliWord_support a b 3 1

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedYYReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational YY-to-XZ subdivision, retaining ordered source sites. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 := by
  obtain ⟨ha,hb,_⟩ := factors (xs p.1) (w p.1) (hlen p.1)
    (hx p.1) (hcover p.1) (he p.1)
  exact qmaXZSubdivision_noY _ _ _ ha hb p.2 i

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs p).toFinset := by
  rcases p with ⟨e,k⟩
  obtain ⟨_,_,ha,hb,_⟩ := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] using hx
      simpa [outputSites] using qmaSinglePauliWord_support e 3 hj
  · exact join_support_cover (xs e) _ ha e 1
  · exact join_support_cover (xs e) _ hb e 1

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let a := fun e => (factor (xs e) (w e)).1
  let b := fun e => (factor (xs e) (w e)).2
  have hf (e : κ) := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  have hfactor (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    (hf e).2.2.2.2.1
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) := (hf e).2.2.2.2.2
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaXZSubdivision_accuracy a b (fun e => (J e:ℝ)) hcomm hNR
  simp only [qmaPauliFamily,outputWord,outputCoefficient,
    QuantumOrderedSubdivision.outputCoefficient,QuantumPolarizedSubdivision.weight_cast,
    QuantumOrderedSubdivision.scale_cast]
  simpa only [hfactor,a,b] using h

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedPrivate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal private-pair subdivision of an ordered X/Z family.  The
source site's list order determines both factors and every output site. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedPrivate
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hy : ∀ e i, w e i ≠ 2) (p : κ × Fin 4) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 :=
  qmaXZSubdivision_noY _ _ _ (qmaPauliRestrict_noY _ _ (hy p.1))
    (qmaPauliRestrict_noY _ _ (hy p.1)) _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : κ × Fin 4) : (outputSites xs p).Nodup :=
  QuantumOrderedSubdivision.outputSites_nodup xs 1 hx p

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_length (xs : κ → List ι) (hx : ∀ e, (xs e).length ≤ 2)
    (p : κ × Fin 4) : (outputSites xs p).length ≤ 2 :=
  QuantumOrderedSubdivision.outputSites_length xs 1 hx p

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] using hx
      simpa [outputSites,QuantumOrderedSubdivision.outputSites] using
        qmaSinglePauliWord_support e 3 hj
  · exact join_support_cover ((xs e).take 1)
      (QuantumOrderedSplit.firstWord (xs e) 1 (w e))
      (qmaPauliRestrict_support _ _) e 1
  · exact join_support_cover ((xs e).drop 1)
      (QuantumOrderedSplit.secondWord (xs e) 1 (w e))
      (qmaPauliRestrict_support _ _) e 1

theorem output_private (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (p q : κ × Fin 4)
    (hp : (qmaPauliSupport (outputWord xs w p)).card = 2)
    (hpq : qmaPauliSupport (outputWord xs w p) = qmaPauliSupport (outputWord xs w q)) :
    p = q := by
  have hd (e : κ) : Disjoint
      (qmaPauliSupport (QuantumOrderedSplit.firstWord (xs e) 1 (w e)))
      (qmaPauliSupport (QuantumOrderedSplit.secondWord (xs e) 1 (w e))) :=
    (QuantumOrderedSplit.disjoint (xs e) (hx e) 1).mono
      (qmaPauliRestrict_support _ _) (qmaPauliRestrict_support _ _)
  obtain ⟨he,hk⟩ := qmaXZSubdivision_private_pair
    (fun e => QuantumOrderedSplit.firstWord (xs e) 1 (w e))
    (fun e => QuantumOrderedSplit.secondWord (xs e) 1 (w e)) hd p.1 q.1 p.2 q.2 hp hpq
  exact Prod.ext he hk

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let a := fun e => QuantumOrderedSplit.firstWord (xs e) 1 (w e)
  let b := fun e => QuantumOrderedSplit.secondWord (xs e) 1 (w e)
  have hfactor (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    QuantumOrderedSplit.factor (xs e) (hx e) 1 (w e) (hcover e)
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) :=
    QuantumOrderedSplit.commute (xs e) (hx e) 1 (w e)
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaXZSubdivision_accuracy a b (fun e => (J e:ℝ)) hcomm hNR
  simp only [qmaPauliFamily,outputWord,outputCoefficient,
    QuantumOrderedSubdivision.outputCoefficient,QuantumPolarizedSubdivision.weight_cast,
    QuantumOrderedSubdivision.scale_cast]
  simpa only [hfactor,a,b] using h

end ContinuumCoulomb.QuantumOrderedPrivate

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedThirdXZ
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered third-order gadget preserves X/Z-only input words. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open QuantumOrderedTriple
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hy : ∀ e i, w e i ≠ 2) (p : κ × Fin 7) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 := by
  have ha : ∀ i, first (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hb : ∀ i, second (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hc : ∀ i, third (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hv : ∀ i, pairWord (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hm : phase xs w p.1 = false := by
    simp [phase,qmaPauliYCount_zero _ ha]
  rcases p with ⟨e,k⟩
  fin_cases k <;> cases i <;>
    simp [outputWord,QuantumPolarizedThird.word,QuantumPolarizedSubdivision.axis,
      hm,qmaSinglePauliWord,ha,hb,hc,hv] <;> split_ifs <;> decide

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTwoStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal rational six-to-four-to-three-local compiler.  Every
intermediate word retains its ordered site list, and the estimate compares
the ordinary full Hilbert-space ground energies. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTwoStage
open QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem support_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (p : (κ × Fin 4) × Fin 4) : qmaPauliSupport (word xs w p) ⊆ (sites xs p).toFinset :=
  outputSites_cover _ _ _ p

theorem even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : (κ × Fin 4) × Fin 4) :
    Even (qmaPauliYCount (word xs w p)) :=
  output_even _ _ _ (outputSites_nodup xs 3 hx) (outputSites_cover xs 3 w)
    (output_even xs 3 w hx hcover he) p

end ContinuumCoulomb.QuantumOrderedTwoStage

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZPipeline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One literal rational six-local to two-local X/Z family.  The intermediate
types retain the original term index and the bounded gadget-word index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem threeSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (threeWord xs w p) ⊆ (threeSites xs p).toFinset :=
  QuantumOrderedTwoStage.support_cover xs w

theorem three_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (threeWord xs w p)) :=
  QuantumOrderedTwoStage.even xs w hx hcover he

theorem twoSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (twoWord xs w p) ⊆ (twoSites xs w p).toFinset :=
  QuantumOrderedThird.outputSites_cover _ _

theorem two_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (twoWord xs w p)) :=
  QuantumOrderedThird.output_even _ _ (threeSites_length xs hlen)
    (threeSites_nodup xs hx) (threeSites_cover xs w) (three_even xs w hx hcover he)

theorem xzThreeSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, qmaPauliSupport (xzThreeWord xs w p) ⊆ (xzThreeSites xs w p).toFinset :=
  QuantumOrderedYY.outputSites_cover _ _ (twoSites_length xs w hlen)
    (twoSites_nodup xs w hlen hx) (twoSites_cover xs w) (two_even xs w hlen hx hcover he)

theorem xzThree_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) : ∀ p i, xzThreeWord xs w p i ≠ 2 :=
  QuantumOrderedYY.output_noY _ _ (twoSites_length xs w hlen)
    (twoSites_nodup xs w hlen hx) (twoSites_cover xs w) (two_even xs w hlen hx hcover he)

theorem sites_nodup (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup) :
    ∀ p, (sites xs w p).Nodup :=
  QuantumOrderedThird.outputSites_nodup _ _ (xzThreeSites_length xs w hlen)
    (xzThreeSites_nodup xs w hlen hx)

theorem sites_length (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) : ∀ p, (sites xs w p).length ≤ 2 :=
  QuantumOrderedThird.outputSites_length _ _ (xzThreeSites_length xs w hlen)

theorem sites_cover (xs : κ → List ι) (w : κ → ι → Fin 4) :
    ∀ p, qmaPauliSupport (word xs w p) ⊆ (sites xs w p).toFinset := by
  intro p i hi
  have h := QuantumOrderedThird.outputSites_cover (xzThreeSites xs w) (xzThreeWord xs w) p hi
  have hm : i ∈ sites xs w p := by simpa only [sites, List.mem_toFinset] using h
  exact List.mem_toFinset.mpr hm

theorem noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) : ∀ p i, word xs w p i ≠ 2 :=
  QuantumOrderedThird.output_noY _ _ (xzThree_noY xs w hlen hx hcover he)

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleAssembly
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact termwise assembly of the computed physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

theorem fieldBonds_matrix {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) :
    ((fieldBonds k i a J).map typedBondMatrix).sum =
      ∑ e : Fin 3, (fieldValue k a J e:ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (i,0)) (finProdFinEquiv (i,qmaFieldEdgeRight e)) := by
  simp only [fieldBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]

theorem crossBonds_matrix {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    ((crossBonds k r i j a b J).map typedBondMatrix).sum =
      ∑ p : Fin 4, ∑ q : Fin 4, (crossValue k r a b J p q:ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q)) := by
  simp only [crossBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]
  calc
    _ = ∑ pq : Fin 4 × Fin 4, (crossValue k r a b J pq.1 pq.2:ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,pq.1)) (finProdFinEquiv (j,pq.2)) :=
      Fintype.sum_equiv (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm _ _ (by intro e; rfl)
    _ = _ := Fintype.sum_prod_type _

theorem penaltyBonds_matrix (n : ℕ) (r : ℚ) :
    ((penaltyBonds n r).map typedBondMatrix).sum =
      ∑ i : Fin n, ∑ e : Fin 6, ((r^2:ℚ):ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (i,qmaFourEdgeLeft e)) (finProdFinEquiv (i,qmaFourEdgeRight e)) := by
  simp only [penaltyBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]
  calc
    _ = ∑ ik : Fin n × Fin 6, ((r^2:ℚ):ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (ik.1,qmaFourEdgeLeft ik.2)) (finProdFinEquiv (ik.1,qmaFourEdgeRight ik.2)) :=
      Fintype.sum_equiv (finProdFinEquiv : Fin n × Fin 6 ≃ Fin (n*6)).symm _ _ (by intro e; rfl)
    _ = _ := Fintype.sum_prod_type _

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem sum_term_partition {M : Type*} [AddCommMonoid M]
    (t : κ → QMAXZTerm n) (f : κ → M) :
    (∑ e, f e) = (∑ e : QMAXZScalarIndex t, f e.val)+
      (∑ e : QMAXZPairIndex t, f e.val)+(∑ e : QMAXZFieldIndex t, f e.val) := by
  rw [qmaSum_subtype_ite (fun e => (t e).IsScalar),
    qmaSum_subtype_ite (fun e => (t e).IsPair),qmaSum_subtype_ite (fun e => (t e).IsField),
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases t e <;> simp [QMAXZTerm.IsScalar,QMAXZTerm.IsPair,QMAXZTerm.IsField]

theorem termScalar_sum (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    r^2*(n*6)+∑ e, termScalar k (t e) (J e) = scalarValue k r t J := by
  have hs (e : QMAXZScalarIndex t) : termScalar k (t e.val) (J e.val) = J e.val := by
    have h := e.property
    cases ht : t e.val <;> simp_all [QMAXZTerm.IsScalar,termScalar]
  have hp (e : QMAXZPairIndex t) : termScalar k (t e.val) (J e.val) =
      -offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val) := by
    have aux (u : QMAXZTerm n) (hu : u.IsPair) (q : ℚ) : termScalar k u q =
        -offset k (u.asPair hu).axisLeft (u.asPair hu).axisRight q := by
      cases u <;> first | exact hu.elim | rfl
    exact aux (t e.val) e.property (J e.val)
  have hf (e : QMAXZFieldIndex t) : termScalar k (t e.val) (J e.val) =
      -shiftValue (qmaXZFieldData t e).axis (J e.val) := by
    have aux (u : QMAXZTerm n) (hu : u.IsField) (q : ℚ) : termScalar k u q =
        -shiftValue (u.asField hu).axis q := by
      cases u <;> first | exact hu.elim | rfl
    exact aux (t e.val) e.property (J e.val)
  rw [sum_term_partition t (fun e => termScalar k (t e) (J e))]
  simp only [hs,hp,hf,Finset.sum_neg_distrib,scalarValue]
  ring

theorem termBonds_pair (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsPair) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum = pairBondMatrix k r (u.asPair hu) J := by
  cases u with
  | scalar => exact hu.elim
  | field => exact hu.elim
  | pair i j hij a b =>
    simp only [termBonds,List.map_append,List.sum_append,crossBonds_matrix,
      pairBondMatrix,QMAXZTerm.asPair]

theorem termBonds_field (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsField) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum =
      ((fieldBonds k (u.asField hu).site (u.asField hu).axis J).map typedBondMatrix).sum := by
  cases u <;> first | exact hu.elim | rfl

theorem termBonds_scalar (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsScalar) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum = 0 := by
  cases u <;> first | exact hu.elim | rfl

theorem matrixValue_assembly (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    matrixValue k r t J = ((penaltyBonds n r).map typedBondMatrix).sum+
      (∑ e, ((termBonds k r (t e) (J e)).map typedBondMatrix).sum)+
      (scalarValue k r t J:ℂ) • 1 := by
  rw [sum_term_partition t (fun e => ((termBonds k r (t e) (J e)).map typedBondMatrix).sum)]
  have hs : (∑ e : QMAXZScalarIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact termBonds_scalar k r _ e.property _
  have hp : (∑ e : QMAXZPairIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) =
      ∑ e : QMAXZPairIndex t, pairBondMatrix k r (qmaXZPairData t e) (J e.val) := by
    apply Finset.sum_congr rfl
    intro e _
    exact termBonds_pair k r _ e.property _
  have hf : (∑ e : QMAXZFieldIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) =
      ∑ e : QMAXZFieldIndex t,
        ((fieldBonds k (qmaXZFieldData t e).site (qmaXZFieldData t e).axis (J e.val)).map typedBondMatrix).sum := by
    apply Finset.sum_congr rfl
    intro e _
    exact termBonds_field k r _ e.property _
  rw [hs,hp,hf,zero_add,penaltyBonds_matrix]
  simp only [matrixValue,qmaExchangeMatrix,QMAFourExchangeIndex,Fintype.sum_sum_type,
    Fintype.sum_prod_type,qmaFourExchangeLeft,qmaFourExchangeRight,weightValue,
    pairBondMatrix,fieldBonds_matrix,Fin.sum_univ_two,ite_true, if_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false, if_false,Complex.ofReal_ratCast,
    Finset.sum_add_distrib]
  abel

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal raw edge instructions encode the proved physical matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem scalar_pack {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) :
    scalar ((k,r),pack t J) = termScalar k t J := by
  cases t <;> simp [scalar,pack,axis_pack,termScalar]

theorem family_matrix {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    ((family k r t J).map typedBondMatrix).sum+
      (r^2*(n*6)+∑ e, termScalar k (t e) (J e):ℚ) •
        (1 : Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ) = matrixValue k r t J := by
  rw [termScalar_sum]
  rw [matrixValue_assembly]
  simp only [family,List.map_append,List.sum_append,List.map_flatten,List.map_ofFn,
    List.sum_flatten,List.sum_ofFn,Function.comp_apply]
  rfl

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSampleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computable budget uses only the qubit count, term count and coefficient mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem rationalErrorBudget_le (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    rationalErrorBudget r t J ≤ universalErrorBudget n (Fintype.card κ) r (∑ e, |J e|) := by
  have hc : (Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)):ℚ) ≤
      6*n+25*Fintype.card κ := by exact_mod_cast qmaXZBlock_exchange_count t
  have hU : (0:ℚ) ≤ Fintype.card κ+∑ e, |J e| := by positivity
  unfold rationalErrorBudget universalErrorBudget rationalInputSize
  gcongr

theorem boundedMatrix_accuracy (N : ℕ) (hN : 0 < N) (t : κ → QMAXZTerm n) (J : κ → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (boundedMatrix N t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  have h := matrixValue_accuracy (boundedPrecision N t J) N hN t J hprivate
  have he := precision_error
    (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|)) N hN
  have hb : matrixErrorBudget (rationalPenalty N J) t J ≤
      (universalErrorBudget n (Fintype.card κ) (rationalPenalty N J) (∑ e, |J e|):ℝ) := by
    rw [← rationalErrorBudget_cast]
    exact_mod_cast rationalErrorBudget_le (rationalPenalty N J) t J
  have he' := (mul_le_mul_of_nonneg_right hb
    (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹^(boundedPrecision N t J))).trans he
  apply h.trans
  calc
    _ ≤ 1/(N:ℝ)+1/(N:ℝ) := add_le_add he' le_rfl
    _ = 2/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawFamilyCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact correspondence between the emitted raw family and its certified finite Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

theorem fullScalar_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    fullScalar (n,(k,r),packed t J) = scalarValue k r t J := by
  simp only [fullScalar,termScalarList,packed,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,scalar_pack,termScalar_sum]

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRawCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw four-spin compiler with its full-space spectral guarantee. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open Matrix
open scoped BigOperators Classical

theorem pack_weight {n : ℕ} (t : QMAXZTerm n) (J : ℚ) : (pack t J).2.2.2 = J := by
  cases t <;> rfl

theorem mass_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    mass (packed t J) = ∑ e, |J e| := by
  simp only [mass,packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,pack_weight]

theorem size_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    size (packed t J) = rationalInputSize J := by
  simp only [size,packed,List.length_ofFn]
  rw [← packed,mass_packed]
  simp only [rationalInputSize,Fintype.card_fin]

theorem budget_packed {n m : ℕ} (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    budget (packed t J) = rationalBudget J := by
  simp only [budget,size_packed,rationalBudget]

theorem scale_packed {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    scale N (packed t J) = rationalPenalty N J := by
  simp only [scale,budget_packed,rationalPenalty]

theorem bits_packed {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    bits (n,N,packed t J) = boundedPrecision N t J := by
  change QuantumAxisSample.precision
    (universalErrorBudget n (packed t J).length (scale N (packed t J)) (mass (packed t J))) N = _
  rw [scale_packed,mass_packed]
  simp only [packed,List.length_ofFn,boundedPrecision,Fintype.card_fin]

theorem rawBondMatrix_erase {n : ℕ} (b : TypedBond n) :
    rawBondMatrix n (erase b) = typedBondMatrix b := by
  simp only [rawBondMatrix,erase,b.1.isLt,b.2.1.isLt,↓reduceDIte,typedBondMatrix]

theorem fullMatrix_packed {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawMatrix (n*4) (fullBonds (n,(k,r),packed t J),fullScalar (n,(k,r),packed t J)) =
      matrixValue k r t J := by
  rw [rawMatrix,fullBonds_packed,fullScalar_packed,List.map_map]
  simp only [Function.comp_def,rawBondMatrix_erase]
  rw [← family_matrix]
  rw [termScalar_sum]

theorem compile_matrix {n m : ℕ} (N : ℕ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    rawMatrix (n*4) (compile (n,N,packed t J)) = boundedMatrix N t J := by
  unfold compile scheduled
  rw [bits_packed,scale_packed,fullMatrix_packed]
  rfl

theorem compile_accuracy {n m : ℕ} (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f) :
    |MediatorGraph.normalizedBottom (rawMatrix (n*4) (compile (n,N,packed t J)))-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  rw [compile_matrix]
  exact boundedMatrix_accuracy N hN t J hprivate

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing literal rational four-spin compiler applied to the actual
ordered X/Z words. Its input list preserves term and endpoint order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawBlock
open scoped BigOperators Classical

theorem private_terms {n m : ℕ} (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hs : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset) (hy : ∀ e i, w e i ≠ 2)
    (hp : ∀ e f, (qmaPauliSupport (w e)).card = 2 →
      qmaPauliSupport (w e) = qmaPauliSupport (w f) → e = f) :
    ∀ e f, (qmaPauliSupport (terms xs w e).word).card = 2 →
      qmaPauliSupport (terms xs w e).word = qmaPauliSupport (terms xs w f).word → e = f := by
  intro e f he hef
  have ht (i : Fin m) : (terms xs w i).word = w i :=
    QuantumOrderedXZTerm.word_eq (xs i) (w i) (hlen i) (hx i) (hs i) (hy i)
  rw [ht e] at he
  rw [ht e,ht f] at hef
  exact hp e f he hef

theorem output_accuracy {n m : ℕ} (N : ℕ) (hN : 0 < N)
    (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hs : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset) (hy : ∀ e i, w e i ≠ 2)
    (hp : ∀ e f, (qmaPauliSupport (w e)).card = 2 →
      qmaPauliSupport (w e) = qmaPauliSupport (w f) → e = f) :
    |MediatorGraph.normalizedBottom (QuantumRawExchange.rawMatrix (n*4) (output N xs w J))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 2/(N:ℝ) := by
  have h := QuantumRawExchange.compile_accuracy N hN (terms xs w) J
    (private_terms xs w hlen hx hs hy hp)
  have ht (e : Fin m) : (terms xs w e).matrix = qmaPauliWord (w e) :=
    QuantumOrderedXZTerm.matrix_eq (xs e) (w e) (hlen e) (hx e) (hs e) (hy e)
  have hc (q : ℚ) : ((q:ℝ):ℂ) = (q:ℂ) := by norm_cast
  simpa only [output,qmaPauliFamily,hc,ht] using h

end ContinuumCoulomb.QuantumOrderedRawBlock

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialReindex
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite qubit relabeling preserves the spatial data and the exact Hamiltonian spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]

omit [DecidableEq Q] [DecidableEq R] in
theorem qmaPauliWord_relabel (e : Q ≃ R) (w : Q → Fin 4) :
    qmaPauliWord (w ∘ e.symm) =
      (qmaPauliWord w).submatrix (qmaQubitBasisEquiv e) (qmaQubitBasisEquiv e) := by
  ext s t
  change (∏ r, qmaPauli (w (e.symm r)) (s r) (t r)) =
    ∏ q, qmaPauli (w q) (s (e q)) (t (e q))
  exact Fintype.prod_equiv e.symm _ _ (by intro r; simp)

omit [DecidableEq Q] [DecidableEq R] in
theorem qmaPauliSupport_relabel (e : Q ≃ R) (w : Q → Fin 4) :
    qmaPauliSupport (w ∘ e.symm) = (qmaPauliSupport w).map e.toEmbedding := by
  ext r
  simp only [Finset.mem_map_equiv,qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of the actual ordered sparse labels into the literal raw
X/Z instructions, including the explicit finite relabeling of their energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped BigOperators Classical

variable {ι κ : Type} {n m : ℕ}

variable [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem numbered_sites_length (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (i : Fin m) :
    (numberedSites q e xs i).length=(xs (e i)).length := List.length_map _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem numbered_sites_nodup (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (hx : ∀ a, (xs a).Nodup) (i : Fin m) :
    (numberedSites q e xs i).Nodup := (hx (e i)).map q.symm.injective

omit [DecidableEq ι] [Fintype κ] in
theorem numbered_support (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4) (i : Fin m) :
    qmaPauliSupport (numberedWord q e w i)=
      (qmaPauliSupport (w (e i))).map q.symm.toEmbedding :=
  qmaPauliSupport_relabel q.symm (w (e i))

omit [Fintype κ] in
theorem numbered_cover (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hs : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset) (i : Fin m) :
    qmaPauliSupport (numberedWord q e w i) ⊆ (numberedSites q e xs i).toFinset := by
  rw [numbered_support]
  intro j hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hj
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨a,List.mem_toFinset.mp (hs (e i) ha),rfl⟩)

omit [DecidableEq ι] [Fintype κ] in
theorem numbered_private (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4)
    (hp : ∀ a b, (qmaPauliSupport (w a)).card=2 →
      qmaPauliSupport (w a)=qmaPauliSupport (w b) → a=b)
    (i j : Fin m) (hi : (qmaPauliSupport (numberedWord q e w i)).card=2)
    (hij : qmaPauliSupport (numberedWord q e w i)=
      qmaPauliSupport (numberedWord q e w j)) : i=j := by
  apply e.injective
  apply hp (e i) (e j)
  · simpa only [numbered_support,Finset.card_map] using hi
  · rw [numbered_support,numbered_support] at hij
    exact (Finset.map_injective q.symm.toEmbedding) hij

theorem numbered_energy (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (w : κ → ι → Fin 4) (J : κ → ℝ) :
    MediatorGraph.normalizedBottom (qmaPauliFamily (numberedWord q e w) (fun i => J (e i))) =
      MediatorGraph.normalizedBottom (qmaPauliFamily w J) := by
  have hw (i : Fin m) : qmaPauliWord (numberedWord q e w i) =
      (qmaPauliWord (w (e i))).submatrix
        (qmaQubitBasisEquiv q.symm) (qmaQubitBasisEquiv q.symm) :=
    qmaPauliWord_relabel q.symm (w (e i))
  have hm : qmaPauliFamily (numberedWord q e w) (fun i => J (e i)) =
      (qmaPauliFamily w J).submatrix
        (qmaQubitBasisEquiv q.symm) (qmaQubitBasisEquiv q.symm) := by
    ext s t
    simp only [qmaPauliFamily,Matrix.sum_apply,Matrix.smul_apply,
      Matrix.submatrix_apply,hw,smul_eq_mul]
    exact e.sum_comp (fun a => (J a:ℂ)*
      qmaPauliWord (w a) (qmaQubitBasisEquiv q.symm s) (qmaQubitBasisEquiv q.symm t))
  rw [hm]
  exact MediatorGraph.normalizedBottom_reindex (qmaQubitBasisEquiv q.symm) _

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedXZEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space error of the literal six-to-four-to-three-to-two-to-XZ compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem bottomDifference_instances {α β : Type}
    (F G : Fintype α) (d e : DecidableEq α)
    (P Q : Fintype β) (a b : DecidableEq β)
    (H : Matrix α α ℂ) (K : Matrix β β ℂ) (r : ℝ)
    (h : |@MediatorGraph.normalizedBottom α F d H -
      @MediatorGraph.normalizedBottom β P a K| ≤ r) :
    |@MediatorGraph.normalizedBottom α G e H -
      @MediatorGraph.normalizedBottom β Q b K| ≤ r := by
  cases Subsingleton.elim F G
  cases Subsingleton.elim d e
  cases Subsingleton.elim P Q
  cases Subsingleton.elim a b
  exact h

theorem xzThree_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) :
    ∀ p, Even (qmaPauliYCount (xzThreeWord xs w p)) := by
  intro p
  rw [qmaPauliYCount_zero _ (xzThree_noY xs w hlen hx hcover he p)]
  exact ⟨0, rfl⟩

theorem twoEnergy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |twoEnergy xs w J N-threeEnergy xs w J N| ≤ 1/(N:ℝ) :=
  QuantumOrderedThird.output_accuracy (threeSites xs) (threeWord xs w)
    (threeCoefficient J N) (threeSites_length xs hlen) (threeSites_nodup xs hx)
    (threeSites_cover xs w) (three_even xs w hx hcover he) N hN

theorem xzThreeEnergy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |xzThreeEnergy xs w J N-twoEnergy xs w J N| ≤ 1/(N:ℝ) := by
  simpa only [xzThreeEnergy,twoEnergy,xzThreeWord,xzThreeCoefficient] using
    (QuantumOrderedYY.output_accuracy (twoSites xs w) (twoWord xs w)
      (twoCoefficient J N) (twoSites_length xs w hlen) (twoSites_nodup xs w hlen hx)
      (twoSites_cover xs w) (two_even xs w hlen hx hcover he) N hN)

theorem energy_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |energy xs w J N-xzThreeEnergy xs w J N| ≤ 1/(N:ℝ) := by
  have h := QuantumOrderedThird.output_accuracy (xzThreeSites xs w) (xzThreeWord xs w)
      (xzThreeCoefficient J N) (xzThreeSites_length xs w hlen)
      (xzThreeSites_nodup xs w hlen hx) (xzThreeSites_cover xs w hlen hx hcover he)
      (xzThree_even xs w hlen hx hcover he) N hN
  unfold energy xzThreeEnergy word coefficient
  exact bottomDifference_instances _ _ _ _ _ _ _ _ _ _ _ h

theorem accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 6) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |energy xs w J N-MediatorGraph.normalizedBottom
      (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 5/(N:ℝ) := by
  let E₀ : ℝ := MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))
  let E₁ : ℝ := threeEnergy xs w J N
  let E₂ : ℝ := twoEnergy xs w J N
  let E₃ : ℝ := xzThreeEnergy xs w J N
  have h₁ : |E₁-E₀| ≤ 2/(N:ℝ) :=
    threeEnergy_error xs w J hx hcover N hN
  have h₂ : |E₂-E₁| ≤ 1/(N:ℝ) :=
    twoEnergy_error xs w J hlen hx hcover he N hN
  have h₃ : |E₃-E₂| ≤ 1/(N:ℝ) :=
    xzThreeEnergy_error xs w J hlen hx hcover he N hN
  have h₄ : |energy xs w J N-E₃| ≤ 1/(N:ℝ) :=
    energy_error xs w J hlen hx hcover he N hN
  calc
    _ ≤ |energy xs w J N-E₃|+|E₃-E₀| := abs_sub_le _ _ _
    _ ≤ |energy xs w J N-E₃|+(|E₃-E₂|+|E₂-E₀|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ |energy xs w J N-E₃|+(|E₃-E₂|+(|E₂-E₁|+|E₁-E₀|)) :=
      add_le_add le_rfl (add_le_add le_rfl (abs_sub_le _ _ _))
    _ ≤ 1/(N:ℝ)+(1/(N:ℝ)+(1/(N:ℝ)+2/(N:ℝ))) :=
      add_le_add h₄ (add_le_add h₃ (add_le_add h₂ h₁))
    _ = 5/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space energy guarantee for the emitted raw exchange list, with
the five early reductions, private-pair subdivision, and four-spin error
all accounted for. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

theorem compiled_final_error (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (hcover : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset)
    (he : ∀ a, Even (qmaPauliYCount (w a))) (N : ℕ) (hN : 0 < N) :
    |outputEnergy (N,n,table e (index q) xs w J)-finalEnergy xs w J N| ≤ 2/(N:ℝ) := by
  let qf := qubits6 q e
  let ef := terms6 e
  have hlenF : ∀ p, (finalSites xs w p).length ≤ 2 :=
    QuantumOrderedPrivate.outputSites_length _ (QuantumOrderedXZ.sites_length xs w hlen)
  have hxF : ∀ p, (finalSites xs w p).Nodup :=
    QuantumOrderedPrivate.outputSites_nodup _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
  have hsF : ∀ p, qmaPauliSupport (finalWord xs w p) ⊆ (finalSites xs w p).toFinset :=
    QuantumOrderedPrivate.outputSites_cover _ _
  have hyF : ∀ p i, finalWord xs w p i ≠ 2 :=
    QuantumOrderedPrivate.output_noY _ _ (QuantumOrderedXZ.noY xs w hlen hx hcover he)
  have hpF : ∀ p r, (qmaPauliSupport (finalWord xs w p)).card=2 →
      qmaPauliSupport (finalWord xs w p)=qmaPauliSupport (finalWord xs w r) → p=r :=
    QuantumOrderedPrivate.output_private _ _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
  have hr := QuantumOrderedRawBlock.output_accuracy N hN
    (numberedSites qf ef (finalSites xs w)) (numberedWord qf ef (finalWord xs w))
    (fun i => finalCoefficient J N (ef i))
    (fun i => (numbered_sites_length qf ef _ i).trans_le (hlenF (ef i)))
    (numbered_sites_nodup qf ef _ hxF) (numbered_cover qf ef _ _ hsF)
    (fun i j => hyF (ef i) (qf j)) (numbered_private qf ef _ hpF)
  have hn : qubitCount (N,n,table e (index q) xs w J)=finalCount n m*4 := by
    rw [qubitCount_table,finalCount_eq]
    omega
  unfold outputEnergy
  rw [hn,output_table q e xs w J hlen hx N]
  unfold finalEnergy
  rw [← numbered_energy qf ef (finalWord xs w) (fun p => (finalCoefficient J N p:ℝ))]
  exact hr

theorem final_xz_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (N : ℕ) (hN : 0 < N) :
    |finalEnergy xs w J N-QuantumOrderedXZ.energy xs w J N| ≤ 1/(N:ℝ) :=
  QuantumOrderedPrivate.output_accuracy _ _ _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
    (QuantumOrderedXZ.sites_cover xs w) N (by omega)

theorem output_accuracy (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (hcover : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset)
    (he : ∀ a, Even (qmaPauliYCount (w a))) (N : ℕ) (hN : 0 < N) :
    |outputEnergy (N,n,table e (index q) xs w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun a => (J a:ℝ)))| ≤ 8/(N:ℝ) := by
  have h₁ := compiled_final_error q e xs w J hlen hx hcover he N hN
  have h₂ := final_xz_error xs w J hlen hx N hN
  have h₃ := QuantumOrderedXZ.accuracy xs w J hlen hx hcover he N (by omega)
  exact (abs_sub_le _ (finalEnergy xs w J N) _).trans
    ((add_le_add h₁ ((abs_sub_le _ (QuantumOrderedXZ.energy xs w J N) _).trans
      (add_le_add h₂ h₃))).trans_eq (by ring))

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal support-list order indexes the small matrix table.  Its
Pauli coefficients agree with the actual ordered-history coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem pauliWord_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (w : β → Fin 4)
    (s t : α → Fin 2) :
    qmaPauliWord (fun a => w (e a)) s t =
      qmaPauliWord w (fun b => s (e.symm b)) (fun b => t (e.symm b)) := by
  unfold qmaPauliWord
  simpa only [e.symm_apply_apply] using e.prod_comp
    (fun b => qmaPauli (w b) (s (e.symm b)) (t (e.symm b)))

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedPauli
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-width Pauli tables.  Padding a local word duplicates its coefficient
by a known factor; replacing odd-Y zero terms by the identity keeps every
emitted word real without a dependent filtered index type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedPauli
open scoped BigOperators Classical

theorem sum_restrict {A : Type} [AddCommMonoid A] (n m : ℕ)
    (f : (Fin n → Fin 4) → A) :
    (∑ w : Fin (n+m) → Fin 4, f (restrictWord n m w)) =
      4^m • ∑ v : Fin n → Fin 4, f v := by
  calc
    _ = ∑ p : (Fin n → Fin 4) × (Fin m → Fin 4), f p.1 :=
      (splitWords n m).sum_comp (fun p => f p.1)
    _ = _ := by simp [Fintype.sum_prod_type,Finset.sum_nsmul]

theorem normalized_sum_restrict {A : Type} [AddCommMonoid A] [Module ℂ A]
    (n m : ℕ) (f : (Fin n → Fin 4) → A) :
    (∑ w : Fin (n+m) → Fin 4, ((4:ℂ)^m)⁻¹ • f (restrictWord n m w)) =
      ∑ v : Fin n → Fin 4, f v := by
  rw [← Finset.smul_sum, sum_restrict, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem evenWord_even (w : ι → Fin 4) : Even (qmaPauliYCount (evenWord w)) := by
  unfold evenWord
  split_ifs with h
  · exact h
  · simp [qmaPauliYCount]

theorem even_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : ι → Fin 4, (evenCoefficient A w:ℂ) • qmaPauliWord (evenWord w)) = A := by
  calc
    _ = ∑ w : ι → Fin 4, ((qmaPauliCoefficient A w).re:ℂ) • qmaPauliWord w := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases he : Even (qmaPauliYCount w)
      · simp only [evenCoefficient,evenWord,he,ite_true, if_true]
      · have ho := (Nat.even_or_odd (qmaPauliYCount w)).resolve_left he
        have hz := qmaPauliCoefficient_odd_zero A hH hR w ho
        simp only [evenCoefficient,evenWord,he,ite_false, if_false,hz,Complex.zero_re,
          Complex.ofReal_zero,zero_smul]
    _ = A := qmaPauli_real_expansion A hH

theorem paddedWord_even (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Even (qmaPauliYCount (paddedWord n m w)) := evenWord_even _

theorem padded_expansion (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (paddedCoefficient n m A w:ℂ) • qmaPauliWord (paddedWord n m w)) = A := by
  let f : (Fin n → Fin 4) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    fun v => (evenCoefficient A v:ℂ) • qmaPauliWord (evenWord v)
  have hf : (∑ w : Fin (n+m) → Fin 4, ((4:ℂ)^m)⁻¹ • f (restrictWord n m w)) =
      ∑ v : Fin n → Fin 4, f v := normalized_sum_restrict n m f
  calc
    _ = ∑ w : Fin (n+m) → Fin 4,
        ((4:ℂ)^m)⁻¹ • f (restrictWord n m w) := by
      apply Finset.sum_congr rfl
      intro w _
      dsimp only [paddedCoefficient,paddedWord,f]
      rw [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]
    _ = ∑ v : Fin n → Fin 4, f v := hf
    _ = A := even_expansion A hH hR

end ContinuumCoulomb.QuantumPaddedPauli

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-space meaning of a fixed-width local coefficient table.
The coordinate map is the order of the literal support list; padding only
duplicates local words and never introduces spectator configurations. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLocal
open scoped BigOperators Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem word_support {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) : qmaPauliSupport (word S e m w) ⊆ S :=
  qmaPauliExtend_support _ _

theorem yCount_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (v : β → Fin 4) :
    qmaPauliYCount (fun i => v (e i)) = qmaPauliYCount v := by
  unfold qmaPauliYCount
  refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
  · intro i hi
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.apply_symm_apply] using hj

theorem word_even {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) : Even (qmaPauliYCount (word S e m w)) := by
  rw [word,qmaPauliExtend_yCount,yCount_reindex e.symm]
  exact QuantumPaddedPauli.paddedWord_even n m w

omit [Fintype ι] in
theorem local_word {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (v : Fin n → Fin 4) :
    qmaPauliWord (fun i => v (e.symm i)) = reindex S e (qmaPauliWord v) := by
  ext s t
  simpa only [reindex,Equiv.symm_symm] using
    QuantumAlgebraicHistory.pauliWord_reindex e.symm v s t

omit [Fintype ι] in
theorem local_expansion {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (QuantumPaddedPauli.paddedCoefficient n m A w:ℂ) •
        qmaPauliWord (fun i => QuantumPaddedPauli.paddedWord n m w (e.symm i))) =
      reindex S e A := by
  simp only [local_word]
  ext s t
  have h := congrFun (congrFun (QuantumPaddedPauli.padded_expansion n m A hH hR)
    (fun i => s (e i))) (fun i => t (e i))
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,reindex] using h

theorem full_expansion {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (QuantumPaddedPauli.paddedCoefficient n m A w:ℂ) • qmaPauliWord (word S e m w)) =
      qmaLocalLift S (reindex S e A) := by
  simp only [word,qmaPauliExtend_lift,← qmaLocalLift_smul,← qmaLocalLift_sum]
  rw [local_expansion S e m A hH hR]

end ContinuumCoulomb.QuantumPaddedLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal 4096-word family for each actual ordered history term.  The
term type is a product, so its emitted order requires no filtered finite type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicHistory
open scoped BigOperators Classical

theorem tableMatrix_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    tableMatrix c hT a =
      (qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
        ((qmaOrderedHistoryModel c hT).matrix a)).submatrix
        (fun s i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i))
        (fun s i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) := by
  ext s t
  exact congrFun (congrFun (denote_orderedCore c hT a) _) _

theorem tableMatrix_hermitian (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (tableMatrix c hT a).IsHermitian := by
  rw [tableMatrix_eq]
  exact (qmaLocalCore_hermitian _ _ ((qmaOrderedHistoryModel c hT).hermitian a)).submatrix _

theorem tableMatrix_real (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (s t) :
    (tableMatrix c hT a s t).im = 0 := by
  rw [tableMatrix_eq]
  exact qmaLocalCore_real _ _ ((qmaOrderedHistoryModel c hT).real a) _ _

theorem term_sum (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (∑ w : Fin 6 → Fin 4, (coefficient c hT (a,w):ℂ) •
      qmaPauliWord (word c hT (a,w))) = (qmaOrderedHistoryModel c hT).matrix a := by
  let n := (QuantumOrderedSupport.sites c hT a).length
  let S : Finset (QuantumOrderedSupport.Qubit c) := (qmaOrderedHistoryModel c hT).sites a
  let e : Fin n ≃ {i // i ∈ S} := QuantumOrderedSupport.supportEquiv c hT a
  let A := tableMatrix c hT a
  let f : (Fin (n+(6-n)) → Fin 4) →
      Matrix (QuantumOrderedSupport.Qubit c → Fin 2) (QuantumOrderedSupport.Qubit c → Fin 2) ℂ :=
    fun v => (QuantumPaddedPauli.paddedCoefficient n (6-n) A v:ℂ) •
      qmaPauliWord (QuantumPaddedLocal.word S e (6-n) v)
  have hsum := (widthIndex n (QuantumOrderedSupport.sites_length c hT a)).sum_comp f
  have hfull := QuantumPaddedLocal.full_expansion S e (6-n) A
    (tableMatrix_hermitian c hT a) (tableMatrix_real c hT a)
  have he : QuantumPaddedLocal.reindex S e A =
        qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
          ((qmaOrderedHistoryModel c hT).matrix a) := by
    dsimp only [A]
    rw [tableMatrix_eq]
    ext s t
    simp only [QuantumPaddedLocal.reindex,Matrix.submatrix_apply,
      e]
    apply congrArg₂ _
    · funext i
      exact congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).apply_symm_apply i)
    · funext i
      exact congrArg t ((QuantumOrderedSupport.supportEquiv c hT a).apply_symm_apply i)
  have hend : qmaLocalLift S (QuantumPaddedLocal.reindex S e A) =
      (qmaOrderedHistoryModel c hT).matrix a := by
    rw [he]
    exact ((qmaOrderedHistoryModel c hT).localOn a).core_lift
  exact hsum.trans (hfull.trans hend)

theorem family_sum (c : QMACircuit) (hT : 0 < c.gates.length) :
    qmaPauliFamily (word c hT) (coefficient c hT) =
      ∑ a, (qmaOrderedHistoryModel c hT).matrix a := by
  rw [qmaPauliFamily,Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun a _ => term_sum c hT a)

theorem term_count (c : QMACircuit) :
    Fintype.card (Term c) = 4096*(4*c.gates.length+2*c.work+9) := by
  simp only [Term,QMAReferenceTerm,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_fun,qmaHistoryReferenceWork]
  ring

theorem support (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    qmaPauliSupport (word c hT p) ⊆ (qmaOrderedHistoryModel c hT).sites p.1 :=
  QuantumPaddedLocal.word_support _ _ _ _

theorem even (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    Even (qmaPauliYCount (word c hT p)) :=
  QuantumPaddedLocal.word_even _ _ _ _

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedSourceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

theorem qubits_index (c : QMACircuit) :
    QuantumOrderedLabelTable.index (qubits c)=QuantumOrderedSupport.siteNumber c := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · change qmaHistoryReferenceWork c+1+((c.gates.length+2)+i.val) =
      qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val
    omega

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelData
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history word is obtained by zipping its literal
site-number list with a fixed local pattern. No spectator basis occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem local_word_at {n : ℕ} (S : Finset ι) (e : Fin n ≃ {i // i ∈ S})
    (m : ℕ) (w : Fin (n+m) → Fin 4) (i : Fin n) :
    QuantumPaddedLocal.word S e m w (e i).val=QuantumPaddedPauli.paddedWord n m w i := by
  simp only [QuantumPaddedLocal.word,qmaPauliExtend,dite_eq_left (e i).property]
  apply congrArg (QuantumPaddedPauli.paddedWord n m w)
  apply e.injective
  rw [Equiv.apply_symm_apply]

private theorem map_get_zip {α β γ : Type} (xs : List α) (g : α → β)
    (f : Fin xs.length → γ) :
    (List.ofFn (fun i => (g (xs.get i),f i)))= (xs.map g).zip (List.ofFn f) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem source_tag (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT p.1) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT p.1).zip
        (localLabels (QuantumOrderedSupport.sites c hT p.1).length
          (6-(QuantumOrderedSupport.sites c hT p.1).length)
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)) := by
  let xs := QuantumOrderedSupport.sites c hT p.1
  let e := QuantumOrderedSupport.supportEquiv c hT p.1
  let v : QuantumOrderedSupport.Qubit c → Fin 4 := word c hT p
  let w := widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2
  have hw (i : Fin xs.length) :
      v (xs.get i)=
        QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i := by
    have hi := QuantumOrderedSupport.supportEquiv_apply c hT p.1 i
    change (e i).val=xs.get i at hi
    rw [← hi]
    exact local_word_at _ e _ w i
  change xs.map (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val)) = _
  calc
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),(v (xs.get i)).val)) :=
      (List.ofFn_getElem_eq_map xs
        (fun i => (QuantumOrderedSupport.siteNumber c i,(v i).val))).symm
    _ = List.ofFn (fun i : Fin xs.length =>
        (QuantumOrderedSupport.siteNumber c (xs.get i),
          (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)) := by
      apply congrArg List.ofFn
      funext i
      rw [hw]
    _ = _ := map_get_zip xs (QuantumOrderedSupport.siteNumber c)
      (fun i => (QuantumPaddedPauli.paddedWord xs.length (6-xs.length) w i).val)

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-width algebraic coefficient tables, with exact normalization of
the padded words. Each local arity at most six uses a fixed finite program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedTable
open QuantumAlgebraicScalar QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedTable.finDecision
private theorem coefficient_decision {ι : Type} [Fintype ι]
    (d e : DecidableEq ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (w : ι → Fin 4) (r : ℝ) :
    r * (@qmaPauliCoefficient ι _ d A w).re =
      r * (@qmaPauliCoefficient ι _ e A w).re := by
  cases Subsingleton.elim d e
  rfl

theorem coefficient_value (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar)
    (w : Fin (n+m) → Fin 4) :
    realValue (coefficient n m (matrixData A) w) =
      QuantumPaddedPauli.paddedCoefficient n m (fun s t => value (A s t)) w := by
  let v := QuantumPaddedPauli.restrictWord n m w
  by_cases h : Even (qmaPauliYCount v)
  · simp only [coefficient,show Even (qmaPauliYCount
        (QuantumPaddedPauli.restrictWord n m w)) from h,ite_true, if_true,
        realValue_mul,realValue_rat,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]
    rw [QuantumFixedPauli.coefficient_matrixData]
    simp only [QuantumPaddedPauli.paddedCoefficient,QuantumPaddedPauli.evenCoefficient,
      show Even (qmaPauliYCount (QuantumPaddedPauli.restrictWord n m w)) from h,ite_true, if_true]
    simp only [div_eq_mul_inv,mul_comm]
    exact coefficient_decision _ _ _ _ _
  · simp only [coefficient,show ¬Even (qmaPauliYCount
        (QuantumPaddedPauli.restrictWord n m w)) from h,ite_false, if_false,realValue_rat,
        Rat.cast_zero,QuantumPaddedPauli.paddedCoefficient,
        QuantumPaddedPauli.evenCoefficient,zero_div]

end ContinuumCoulomb.QuantumPaddedTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedSampling
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal padded history table has the same polynomial scalar budget
as the supported expansion, and its rational samples approximate the actual
full-space history energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped BigOperators Classical

section ScalarTable

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedHistory.finDecision
private theorem padded_height (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar)
    (w : Fin (n+m) → Fin 4) (C : ℚ) (hC : 0 ≤ C)
    (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (QuantumPaddedTable.coefficient n m (matrixData A) w) ≤ 2^n*C := by
  let v := QuantumPaddedPauli.restrictWord n m w
  have hE : (fun s t : Fin n → Fin 2 => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  have hV : realHeight (realCoefficient A v) ≤ (2:ℚ)^n*C := by
    simpa only [Fintype.card_fin] using realHeight_coefficient A v C hA
  unfold QuantumPaddedTable.coefficient
  change realHeight (if Even (qmaPauliYCount v) then
    realMul (realRat (((4:ℚ)^m)⁻¹))
      (realCoefficient (fun s t => entry (matrixData A) s t) v) else realRat 0) ≤ _
  rw [hE]
  split_ifs
  · have hr : |((4:ℚ)^m)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc
      _ ≤ realHeight (realRat (((4:ℚ)^m)⁻¹))*realHeight (realCoefficient A v) :=
        realHeight_mul _ _
      _ ≤ 1*realHeight (realCoefficient A v) := by
        rw [realHeight_rat]
        exact mul_le_mul_of_nonneg_right hr (realHeight_nonnegative _)
      _ ≤ (2:ℚ)^n*C := by simpa only [one_mul] using hV
  · simpa only [realHeight_rat,abs_zero] using mul_nonneg (pow_nonneg (by norm_num) n) hC

theorem scalar_value (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    realValue (scalar c hT p) = coefficient c hT p := by
  unfold scalar coefficient tableMatrix
  exact QuantumPaddedTable.coefficient_value _ _ (orderedTable c hT p.1) _

theorem scalar_height (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    realHeight (scalar c hT p) ≤ (coefficientBudget c:ℚ) := by
  have h := padded_height _ _ (orderedTable c hT p.1)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)
    (2*historyHeight c) (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    (fun s t => height_orderedCore c hT p.1 _ _)
  have hp : (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length ≤ 64 := by
    exact (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2)
      (QuantumOrderedSupport.sites_length c hT p.1)).trans_eq (by norm_num)
  change realHeight (scalar c hT p) ≤ _ at h
  calc
    _ ≤ (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length*(2*historyHeight c) := h
    _ ≤ 64*(2*historyHeight c) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    _ = (coefficientBudget c:ℚ) := by rw [coefficientBudget_cast]; ring

end ScalarTable

theorem sampled_error (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (word c hT)
        (fun p => (sampledWeight k c hT p:ℝ)))-(qmaOrderedHistoryModel c hT).energy| ≤
      (termBudget c:ℝ)*(coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k := by
  change |MediatorGraph.normalizedBottom _ -
    MediatorGraph.normalizedBottom (∑ a, (qmaOrderedHistoryModel c hT).matrix a)| ≤ _
  rw [← family_sum]
  have hround := qmaPauliFamily_ground_error (word c hT)
    (fun p => (sampledWeight k c hT p:ℝ)) (coefficient c hT)
  have hterm (p : Term c) :
      |(sampledWeight k c hT p:ℝ)-coefficient c hT p| ≤
        (coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k := by
    rw [← scalar_value]
    exact (sample_error_height k (scalar c hT p)).trans
      (mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (scalar_height c hT p)) (by positivity))
  apply hround.trans
  calc
    _ ≤ ∑ _p : Term c, (coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,term_count,termBudget,
        Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      ring

theorem sampled_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (word c hT)
        (fun p => (sampledWeight (samplePrecision c N) c hT p:ℝ)))-
      (qmaOrderedHistoryModel c hT).energy| ≤ 1/(N:ℝ) := by
  let k := samplePrecision c N
  let M := (termBudget c:ℝ)
  let B := (coefficientBudget c:ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (k:ℝ)+1 ≤ (2:ℝ)^k := by
    have hp : k+1 ≤ 2^k := Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := k))
    exact_mod_cast hp
  have hkp : (0:ℝ) < (k:ℝ)+1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num)
  have hk : (k:ℝ) = (M+1)*(B+1)*N := by
    simp only [k,samplePrecision,M,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ M*B*(2:ℝ)⁻¹^k := sampled_error k c hT
    _ = M*B/((2:ℝ)^k) := by rw [inv_pow]; rfl
    _ ≤ M*B/((k:ℝ)+1) := div_le_div_of_nonneg_left (mul_nonneg hM hB) hkp hpow
    _ ≤ 1/(N:ℝ) := by
      apply (div_le_div_iff₀ hkp hNR).mpr
      rw [hk]
      nlinarith

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity local history packets: sparse numeric labels and sampled
algebraic coefficients share exactly the same fixed Pauli-word order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem uniformPacket_eq (x : Input) (h : x.2.1.length ≤ 6) :
    uniformPacket x=packet x.2.1.length (6-x.2.1.length) x := by
  generalize hn : x.2.1.length=n at *
  interval_cases n <;> simp only [uniformPacket,hn] <;> norm_num

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelMeaning
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every emitted local packet entry is the actual padded history word
and its sampled coefficient, in the supplied support-list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.finDecision
private theorem labels_eq_zip (n m : ℕ) (w : Fin (n+m) → Fin 4)
    (xs : List ℕ) (hlen : xs.length=n) :
    labels n m w xs = xs.zip (localLabels n m w) := by
  apply List.ext_getElem
  · simp [labels,localLabels,hlen]
  · intro i hi hj
    have hi' : i < xs.length := by simpa only [labels,List.length_ofFn,← hlen] using hi
    simp only [labels,localLabels,List.getElem_ofFn,List.getElem_zip]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi',Option.getD_some]

theorem entry_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin ((QuantumOrderedSupport.sites c hT a).length+
      (6-(QuantumOrderedSupport.sites c hT a).length)) → Fin 4) :
    entry (QuantumOrderedSupport.sites c hT a).length
      (6-(QuantumOrderedSupport.sites c hT a).length) w
      (k,QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) =
    let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
    (QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p),sampledWeight k c hT p) := by
  let p : Term c := (a,(widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).symm w)
  have hw : widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2 = w :=
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT a)).apply_symm_apply w
  apply Prod.ext
  · change labels _ _ w (QuantumOrderedSupport.encodedSites c hT a) = _
    rw [labels_eq_zip _ _ w _ (by simp only [QuantumOrderedSupport.encodedSites,List.length_map])]
    have hs := source_tag c hT p
    change QuantumOrderedLabelData.tag (QuantumOrderedSupport.siteNumber c)
      (QuantumOrderedSupport.sites c hT a) (word c hT p) =
      (QuantumOrderedSupport.encodedSites c hT a).zip (localLabels _ _
        (widthIndex _ (QuantumOrderedSupport.sites_length c hT a) p.2)) at hs
    rw [hw] at hs
    exact hs.symm
  · change sample k (QuantumPaddedTable.coefficient _ _ _ w) = _
    unfold sampledWeight
    apply congrArg (sample k)
    unfold scalar
    rw [hw]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal concatenation of fixed-width history packets is an exact
enumeration of the actual padded history family.  The local pattern order is
allowed to depend on the support width; its explicit bijection is retained. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumAlgebraicScalar QuantumFixedPauli QuantumPaddedHistory
open scoped Classical

theorem packet_reindex (n : ℕ) (hn : n ≤ 6) (x : Input) :
    packet n (6-n) x = List.ofFn (fun j => entry n (6-n) (packetPatterns n hn j) x) := by
  simp only [packet,enumerate,List.map_ofFn,Function.comp_def]
  rw [List.ofFn_congr (pattern_card n hn)]
  rfl

attribute [local instance] OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.tableFinDecision
theorem sourceEntries_table (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    sourceEntries k c hT =
      QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
        (fun p => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT) := by
  unfold sourceEntries QuantumOrderedLabelTable.table sourceTerms
  simp only [Equiv.trans_apply]
  let entryAt (j : Fin (QuantumOrderedSourceIndex.referenceCount c) ×
      Fin QuantumOrderedSourceIndex.patternCount) :=
    let p := Equiv.prodShear (QuantumOrderedSourceIndex.reference c)
      (fun i => (packetPatterns _ (QuantumOrderedSupport.sites_length c hT
        (QuantumOrderedSourceIndex.reference c i))).trans
          (widthIndex _ (QuantumOrderedSupport.sites_length c hT
            (QuantumOrderedSourceIndex.reference c i))).symm) j
    (QuantumOrderedLabelData.tag
      (QuantumOrderedLabelTable.index (QuantumOrderedSourceIndex.qubits c))
      (QuantumOrderedSupport.sites c hT p.1) (sourceWord c hT p),sampledWeight k c hT p)
  change _ = List.ofFn (fun i => entryAt (finProdFinEquiv.symm i))
  rw [QuantumOrderedLabelTable.product_table entryAt]
  dsimp only [entryAt]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  let a := QuantumOrderedSourceIndex.reference c i
  have hn := QuantumOrderedSupport.sites_length c hT a
  rw [uniformPacket_eq _ (by
    simpa only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map] using hn)]
  rw [show (sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)).2.1.length =
    (QuantumOrderedSupport.sites c hT a).length by
      simp only [sourceInput,QuantumOrderedSupport.encodedSites,List.length_map,a]]
  change packet (QuantumOrderedSupport.sites c hT a).length
    (6-(QuantumOrderedSupport.sites c hT a).length) (sourceInput k c hT a) = _
  rw [packet_reindex _ hn]
  apply congrArg List.ofFn
  funext j
  have h := entry_source k c hT a (packetPatterns _ hn j)
  simpa only [sourceInput,sourceWord,Equiv.trans_apply,Equiv.prodShear_apply,
    Equiv.symm_apply_apply,
    QuantumOrderedSourceIndex.qubits_index] using h

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedLabelEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual padded history packets, followed by the literal local and
four-spin compiler, have total full-space error at most nine over N. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedLabelProgram
open QuantumPaddedHistory QuantumOrderedSourceIndex
open scoped Classical

theorem history_accuracy_oai (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom
        (QuantumRawExchange.rawMatrix (historyQubits c hT N) (historyOutput c hT N))-
      (qmaOrderedHistoryModel c hT).energy| ≤ 9/(N:ℝ) := by
  let k := QuantumAlgebraicHistory.samplePrecision c N
  have hc (p : Term c) : qmaPauliSupport (sourceWord c hT p) ⊆
      (QuantumOrderedSupport.sites c hT p.1).toFinset := by
    rw [QuantumOrderedSupport.sites_finset]
    exact support c hT p
  have h₁ := QuantumOrderedLabelCompile.output_accuracy (qubits c) (sourceTerms c hT)
    (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
    (sourceWord c hT) (sampledWeight k c hT)
    (fun p => QuantumOrderedSupport.sites_length c hT p.1)
    (fun p => QuantumOrderedSupport.sites_nodup c hT p.1) hc (even c hT) N hN
  have hi : historyInput c hT N =
      (N,qubitCount c,QuantumOrderedLabelTable.table (sourceTerms c hT)
        (QuantumOrderedLabelTable.index (qubits c))
        (fun p : Term c => QuantumOrderedSupport.sites c hT p.1)
        (sourceWord c hT) (sampledWeight k c hT)) := by
    unfold historyInput
    rw [sourceEntries_table]
  rw [← hi] at h₁
  have h₂ := sampled_accuracy c hT N hN
  exact (abs_sub_le _ _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.history_accuracy_oai := @OAI.ContinuumCoulomb.QuantumPaddedLabelProgram.history_accuracy_oai
