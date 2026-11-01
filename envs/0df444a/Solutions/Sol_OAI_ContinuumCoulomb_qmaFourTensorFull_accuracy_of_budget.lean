-- Prove2me | solution 1 for OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:11:03.325546+00:00
-- url     : https://prove2.me/submissions/c2a93a4a-7a8d-430f-ae5f-e4e0f2709e22

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
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourRawEncoding_action
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_eigen_row0
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_eigen_row1
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_eigen_row2
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_eigen_row3
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row0
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row1
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row2
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourSpinRawAction_orthogonal_row3
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensorFull_effective
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensorInverse_high
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensorPadded_symmetric
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensorPhysical_symmetric
import Theorems.Thm_OAI_ContinuumCoulomb_qmaFourTensor_padded_gap

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_Perturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second-order block estimates

The finite reductions use the bottom-energy estimate from the binary
manuscript's `lem:second-order` and the unit manuscript's `lem:perturbation`.
Explicit positivity and operator norm bounds give vector and variational
estimates for the penalty, inverse, coupling and high perturbation blocks.

Real inner products also express the real quadratic forms of complex spin
Hilbert spaces by restriction of scalars.
-/

noncomputable section

open scoped InnerProductSpace

namespace ContinuumCoulomb
namespace Perturbation

variable {L H : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℝ L]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The precise square-completion identity, before any estimates. -/
theorem penalty_square_identity (A T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x, A y⟫_ℝ = ⟪A x, y⟫_ℝ)
    (p : L) (q : H) {σ : ℝ} (hσ : σ ≠ 0) :
    σ * penaltyForm A q + 2 * ⟪q, B p⟫_ℝ =
      σ * penaltyForm A (q + σ⁻¹ • T (B p)) - σ⁻¹ * inverseForm T B p := by
  have hcross : ⟪T (B p), A q⟫_ℝ = ⟪q, B p⟫_ℝ := by
    rw [hAsymm, hAT, real_inner_comm]
  simp only [penaltyForm, inverseForm, map_add, map_smul, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hAT, hcross]
  rw [real_inner_comm (T (B p)) (B p)]
  field_simp
  ring

/-- The trial vector used in the second-order variational upper bound. -/
theorem blockEnergy_trial_identity (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x) (p : L) :
    blockEnergy A D B p (-(T (B p))) =
      -inverseForm T B p + ⟪-(T (B p)), D (-(T (B p)))⟫_ℝ := by
  simp only [blockEnergy, penaltyForm, inverseForm, map_neg, hAT,
    inner_neg_left, inner_neg_right]
  rw [real_inner_comm (T (B p)) (B p)]
  ring

theorem highPerturbation_abs_le (D : H →L[ℝ] H)
    {g ε : ℝ} (hD : ‖D‖ ≤ ε * g) (q : H) :
    |⟪q, D q⟫_ℝ| ≤ ε * g * ‖q‖ ^ 2 := by
  calc
    |⟪q, D q⟫_ℝ| ≤ ‖q‖ * ‖D q‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖q‖ * (ε * g * ‖q‖) := by
      exact mul_le_mul_of_nonneg_left
        ((D.le_opNorm q).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
        (norm_nonneg _)
    _ = ε * g * ‖q‖ ^ 2 := by ring

theorem effectiveForm_smul (C : L →L[ℝ] L) (T : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    effectiveForm C T B (r • p) = r ^ 2 * effectiveForm C T B p := by
  simp only [effectiveForm, inverseForm, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- Finite dimensionality supplies the effective ground vector; this
is not an additional simulation assumption. -/
theorem effectiveForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧
      ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hc : Continuous (effectiveForm C T B) :=
    (continuous_id.inner C.continuous).sub
      (B.continuous.inner (T.continuous.comp B.continuous))
  have hnonempty : (Metric.sphere (0 : L) 1).Nonempty := ⟨u, by simpa using hu⟩
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sphere (0 : L) 1).exists_isMinOn hnonempty hc.continuousOn
  refine ⟨p, by simpa using hp, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, effectiveForm, inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change effectiveForm C T B p ≤ effectiveForm C T B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [effectiveForm_smul] at h
  calc
    effectiveForm C T B p * ‖x‖ ^ 2 ≤
        (‖x‖⁻¹ ^ 2 * effectiveForm C T B x) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = effectiveForm C T B x := by field_simp

theorem effectiveBottom_eq (C : L →L[ℝ] L) (T : H →L[ℝ] H) (B : L →L[ℝ] H)
    (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x : L, effectiveForm C T B p * ‖x‖ ^ 2 ≤ effectiveForm C T B x) :
    effectiveBottom C T B = effectiveForm C T B p := by
  have hlower (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = effectiveForm C T B x) :
      effectiveForm C T B p ≤ e := by
    obtain ⟨x, hx, rfl⟩ := he
    simpa only [hx, one_pow, mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_, hlower⟩ ⟨p, hp, rfl⟩)
    (le_csInf ⟨_, p, hp, rfl⟩ hlower)

end Perturbation
end ContinuumCoulomb

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

theorem sourceLocalPauli_commute (n : ℕ) (i j : Fin n) (hij : i ≠ j) (μ ν : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n j ν =
      sourceLocalPauli n j ν * sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul, sourceTensor_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorGraph
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem matrixForm_smul (H : Matrix ι ι ℂ) (a : ℝ) (x : EuclideanSpace ℂ ι) :
    ⟪a • x, spinMatrixOperator H (a • x)⟫_ℝ = a ^ 2 * ⟪x, spinMatrixOperator H x⟫_ℝ := by
  change ⟪a • x, (spinMatrixOperator H).restrictScalars ℝ (a • x)⟫_ℝ = _
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  change a * (a * ⟪x, spinMatrixOperator H x⟫_ℝ) = _
  ring

theorem normalizedBottom_eq_rayleigh (H : Matrix ι ι ℂ) :
    normalizedBottom H = sInf {e | ∃ x : EuclideanSpace ℂ ι,
      0 < ‖x‖ ^ 2 ∧ e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2} := by
  unfold normalizedBottom
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by rw [hx]; norm_num, by rw [hx]; simp⟩
  · rintro ⟨x, hx, rfl⟩
    have hnx : ‖x‖ ≠ 0 := by intro h; simp [h] at hx
    refine ⟨(‖x‖⁻¹ : ℝ) • x, norm_smul_inv_norm (norm_ne_zero_iff.mp hnx), ?_⟩
    rw [matrixForm_smul]
    field_simp

end Reindex

end ContinuumCoulomb.MediatorGraph

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_ClockWeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-weight clock bounds retain a strict completeness/soundness margin. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem norm_add_sq_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SharpBlockPerturbation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A block estimate retaining the cancellation in the effective energy.
It is needed when the third-order gadget's coupling exceeds its low block. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace

variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sharp_lowBlockEnergy_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (_hη : 0 ≤ η) (hsmall : 2*(d+m) ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ effectiveForm C T B p)
    (p : L) (q : H) :
    -2*(d+m)*η^2*‖p‖^2 ≤ lowBlockEnergy C A D B p q-μ*(‖p‖^2+‖q‖^2) := by
  have hi := penalty_square_identity A T B hAT hAsymm p q (by norm_num : (1:ℝ) ≠ 0)
  simp only [one_mul,inv_one,one_smul] at hi
  have hnorm := norm_add_sq_two (q+T (B p)) (-(T (B p)))
  simp only [add_neg_cancel_right,norm_neg] at hnorm
  have ht := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [mul_pow] at ht
  have hq : ‖q‖^2 ≤ 2*‖q+T (B p)‖^2+2*η^2*‖p‖^2 := by linarith
  have hqp := mul_le_mul_of_nonneg_left hq (add_nonneg hd hm)
  have hg := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖q+T (B p)‖)
  have hmup := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖q‖)
  have hminp := hmin p
  have hdq := (abs_le.mp (hD q)).1
  have hgapq := hgap (q+T (B p))
  unfold effectiveForm at hminp
  unfold lowBlockEnergy blockEnergy
  nlinarith

theorem sharp_lowBlockRayleigh_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {d m η μ : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m) (_hη : 0 ≤ η)
    (hAT : ∀ x, A (T x) = x) (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : -m ≤ μ) (p : L) (hp : ‖p‖ = 1) (he : effectiveForm C T B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ+(d+m)*η^2 := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [hp,mul_one] at ht
  have hi := blockEnergy_trial_identity A T D B hAT p
  have hdq := (abs_le.mp (hD (-(T (B p))))).2
  simp only [norm_neg] at hdq
  have hmup := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖T (B p)‖)
  have herr := mul_le_mul_of_nonneg_left ht (add_nonneg hd hm)
  have hextra : 0 ≤ (d+m)*η^2*‖T (B p)‖^2 := by positivity
  unfold lowBlockRayleigh lowBlockEnergy
  rw [hp,norm_neg]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1^2+‖T (B p)‖^2)).mpr
  unfold effectiveForm at he
  nlinarith

end ContinuumCoulomb.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_OrthogonalBlockDecomposition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block coordinates on an orthogonal subspace and its actual complement.
The high space may retain an unused copy of the low coordinates, since the
physical vectors and trial vectors lie in the kernel of the restriction. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem orthogonalHighPart_kernel (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (x : H) : R (orthogonalHighPart E R x) = 0 := by
  simp [orthogonalHighPart,hRE]

theorem orthogonal_assemble (E : L →L[ℝ] H) (R : H →L[ℝ] L) (x : H) :
    E (R x)+orthogonalHighPart E R x = x := by
  unfold orthogonalHighPart
  abel

theorem orthogonalInclusion_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (p : L) :
    ‖E p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, hAdj,hRE,real_inner_self_eq_norm_sq]

theorem orthogonalParts_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (x : H) :
    ‖R x‖^2+‖orthogonalHighPart E R x‖^2 = ‖x‖^2 := by
  have h := norm_add_sq_real (E (R x)) (orthogonalHighPart E R x)
  rw [orthogonal_assemble,hAdj,orthogonalHighPart_kernel E R hRE,inner_zero_right,
    orthogonalInclusion_norm E R hRE hAdj] at h
  linarith

theorem orthogonalAssemble_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) : ‖E p+q‖^2 = ‖p‖^2+‖q‖^2 := by
  rw [norm_add_sq_real,hAdj,hq,inner_zero_right,orthogonalInclusion_norm E R hRE hAdj]
  ring

theorem orthogonalBlock_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) :
    ⟪E p+q,M (E p+q)⟫_ℝ = lowBlockEnergy C A D B p q := by
  have hEq : ⟪E p,M (E p)⟫_ℝ = ⟪p,C p⟫_ℝ := by
    rw [hLow,inner_add_right,hAdj,hRE,hAdj,hRB,inner_zero_right,add_zero]
  have hqE : ⟪q,E (C p)⟫_ℝ = 0 := by
    rw [real_inner_comm,hAdj,hq,inner_zero_right]
  have hqM : ⟪q,M (E p)⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hLow,inner_add_right,hqE,zero_add]
  have hMq : ⟪E p,M q⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hM,real_inner_comm,hqM]
  simp only [map_add,inner_add_left,inner_add_right,hEq,hqM,hMq,hHigh q hq]
  unfold lowBlockEnergy blockEnergy
  ring

theorem orthogonalBlock_full_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ) (x : H) :
    ⟪x,M x⟫_ℝ = lowBlockEnergy C A D B (R x) (orthogonalHighPart E R x) := by
  have h := orthogonalBlock_energy E R M A D C B hRE hAdj hM hLow hRB hHigh
    (R x) (orthogonalHighPart E R x) (orthogonalHighPart_kernel E R hRE x)
  rwa [orthogonal_assemble] at h

end ContinuumCoulomb.Perturbation

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

theorem qmaMatrixOperator_add (M N : Matrix α β ℂ) :
    qmaMatrixOperator (M+N) = qmaMatrixOperator M+qmaMatrixOperator N := by
  unfold qmaMatrixOperator
  rw [map_add,map_add]

theorem qmaMatrixOperator_smul (c : ℂ) (M : Matrix α β ℂ) :
    qmaMatrixOperator (c • M) = c • qmaMatrixOperator M := by
  unfold qmaMatrixOperator
  rw [map_smul,map_smul]

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

theorem qmaFourSpinRawAction_eigen (i : Fin 4) (μ : Fin 3) :
    qmaFourPenaltyRational*qmaFourSpinRawAction i μ = (4:ℚ) • qmaFourSpinRawAction i μ := by
  fin_cases i
  · exact qmaFourSpinRawAction_eigen_row0 μ
  · exact qmaFourSpinRawAction_eigen_row1 μ
  · exact qmaFourSpinRawAction_eigen_row2 μ
  · exact qmaFourSpinRawAction_eigen_row3 μ

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

theorem qmaFourSpin_excitation (i : Fin 4) (μ : Fin 3) :
    qmaFourPenalty*(qmaFourSpin i μ*qmaFourEncoding) =
      (4:ℂ) • (qmaFourSpin i μ*qmaFourEncoding) := by
  rw [qmaFourSpin_encoding,Matrix.mul_smul,← Matrix.mul_assoc,qmaFourPenalty,
    ← Matrix.map_mul,qmaFourSpinRawAction_eigen]
  have he : ((4:ℚ) • qmaFourSpinRawAction i μ).map (Rat.castHom ℂ) =
      (4:ℂ) • (qmaFourSpinRawAction i μ).map (Rat.castHom ℂ) := by
    ext s b
    simp
  rw [he,Matrix.smul_mul,smul_comm]

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
theorem qmaSiteMatrix_star (i : Q) (A : Matrix σ σ ℂ) :
    (qmaSiteMatrix i A).conjTranspose = qmaSiteMatrix i A.conjTranspose := by
  rw [qmaSiteMatrix,qmaTensorMatrix_star]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

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

theorem qmaFourTensorEncoding_projector (n : ℕ) :
    qmaFourTensorEncoding n*(qmaFourTensorEncoding n).conjTranspose = qmaFourTensorProjection n := by
  rw [qmaFourTensorEncoding,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simp only [qmaFourEncoding_projector,qmaFourTensorProjection]

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

theorem qmaFourTensorPairColumn_orthogonal (i j : Fin n) (p q : Fin 4) (μ : Fin 3) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorPairColumn i j p q μ = 0 := by
  rw [qmaFourTensorEncoding,qmaFourTensorPairColumn,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  apply qmaTensorMatrix_zero_at _ i
  simp only [ite_true, if_true,← Matrix.mul_assoc,qmaFourSpin_orthogonal]

theorem qmaFourTensorPairColumn_excitation (i j : Fin n) (hij : i ≠ j)
    (p q : Fin 4) (μ : Fin 3) :
    qmaFourTensorPenalty n*qmaFourTensorPairColumn i j p q μ =
      (8:ℂ) • qmaFourTensorPairColumn i j p q μ := by
  have h := qmaTensorPenalty_eigen qmaFourPenalty
    (fun k : Fin n => if k = i then qmaFourSpin p μ*qmaFourEncoding
      else if k = j then qmaFourSpin q μ*qmaFourEncoding else qmaFourEncoding)
    (fun k => (if k = i then (4:ℂ) else 0)+(if k = j then (4:ℂ) else 0)) (by
      intro k
      by_cases hki : k = i
      · subst k
        simp only [ite_true, if_true,hij,ite_false, if_false,add_zero]
        exact qmaFourSpin_excitation p μ
      · by_cases hkj : k = j
        · subst k
          simp only [hki,ite_true, if_true,ite_false, if_false,zero_add]
          exact qmaFourSpin_excitation q μ
        · simp only [hki,hkj,ite_false, if_false,zero_add,zero_smul,qmaFourPenalty_encoding])
  simpa only [qmaFourTensorPenalty,qmaFourTensorPairColumn,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,show (4:ℂ)+4 = 8 by norm_num] using h

theorem qmaFourTensorCross_orthogonal (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorCross i j p q*qmaFourTensorEncoding n) = 0 := by
  rw [qmaFourTensorCross_column i j hij,Matrix.mul_sum]
  simp only [qmaFourTensorPairColumn_orthogonal,Finset.sum_const_zero]

theorem qmaFourTensorCross_excitation (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    qmaFourTensorPenalty n*(qmaFourTensorCross i j p q*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorCross i j p q*qmaFourTensorEncoding n) := by
  rw [qmaFourTensorCross_column i j hij,Matrix.mul_sum]
  simp only [qmaFourTensorPairColumn_excitation i j hij,Finset.smul_sum]

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

theorem qmaFourCouplingSize_nonneg (a b : Fin 2) (j : ℝ) : 0 ≤ qmaFourCouplingSize a b j :=
  Real.sqrt_nonneg _

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

theorem qmaFourTensorWeighted_orthogonal (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_orthogonal i j hij,smul_zero,Finset.sum_const_zero]

theorem qmaFourTensorWeighted_excitation (i j : Fin n) (hij : i ≠ j) (a b : Fin 4 → ℝ) :
    qmaFourTensorPenalty n*(qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorWeighted i j a b*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorWeighted,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_sum,Matrix.mul_smul,
    qmaFourTensorCross_excitation i j hij]
  simp only [Finset.smul_sum,smul_comm (8:ℂ)]

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

theorem qmaFourCouplingSize_bound (a b : Fin 2) (j : ℝ) :
    qmaFourCouplingSize a b j ≤ 3*(1+|j|) := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hp : 1 ≤ qmaFourAxisScale a*qmaFourAxisScale b := by nlinarith
  have hr := qmaFourCouplingSize_nonneg a b j
  have he := qmaFourCouplingSize_square a b j
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (qmaFourCouplingSize a b j))
  have hsq : (qmaFourCouplingSize a b j)^2 ≤ (8/3)*|j| := by nlinarith
  have hj := abs_nonneg j
  nlinarith [sq_nonneg |j|]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorNorm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectator-independent bounds for the actual many-block physical couplings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourSpin_square (p : Fin 4) (μ : Fin 3) :
    qmaFourSpin p μ*qmaFourSpin p μ = 1 := by
  rw [qmaFourSpin_source]
  change (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm = 1
  rw [Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,sourceLocalPauli_sq,
    Matrix.submatrix_one_equiv]

theorem qmaFourTensorSpin_norm (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourSpin p μ))‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [qmaSiteMatrix_star,qmaFourSpin_star,qmaSiteMatrix_mul,qmaFourSpin_square,qmaSiteMatrix_one]

theorem qmaFourTensorCross_norm (i j : Fin n) (p q : Fin 4) :
    ‖spinMatrixOperator (qmaFourTensorCross i j p q)‖ ≤ 3 := by
  rw [qmaFourTensorCross,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator
        (qmaSiteMatrix i (qmaFourSpin p μ)*qmaSiteMatrix j (qmaFourSpin q μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      rw [spinMatrixOperator_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using (mul_le_mul (qmaFourTensorSpin_norm i p μ) (qmaFourTensorSpin_norm j q μ)
          (norm_nonneg _) zero_le_one))
    _ = 3 := by norm_num

theorem qmaFourTensorWeighted_norm (i j : Fin n) (a b : Fin 4 → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorWeighted i j a b)‖ ≤
      3*(∑ p, |a p|)*(∑ q, |b q|) := by
  rw [qmaFourTensorWeighted,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ p, ∑ q, 3*|a p| * |b q| := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      rw [spinMatrixOperator_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ (|a p| * |b q|)*3 := mul_le_mul_of_nonneg_left (qmaFourTensorCross_norm i j p q) (by positivity)
        _ = _ := by ring
    _ = (∑ p, 3*|a p|)*(∑ q, |b q|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ = _ := by rw [← Finset.mul_sum]

theorem qmaFourTensorAxisCross_norm (i j : Fin n) (a b : Fin 2) (p q : Bool) :
    ‖spinMatrixOperator (qmaFourTensorWeighted i j (qmaFourAxisWeights a p) (qmaFourAxisWeights b q))‖ ≤
      2352 := by
  apply (qmaFourTensorWeighted_norm _ _ _ _).trans
  have ha := qmaFourAxisWeights_abs_sum a p
  have hb := qmaFourAxisWeights_abs_sum b q
  have ha0 : 0 ≤ ∑ k, |qmaFourAxisWeights a p k| := by positivity
  have hb0 : 0 ≤ ∑ k, |qmaFourAxisWeights b q k| := by positivity
  nlinarith

theorem qmaFourTensorCoupling_norm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCoupling i j a b t)‖ ≤ 7056*(1+|t|) := by
  rw [qmaFourTensorCoupling,spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (qmaFourCouplingSize_nonneg a b t)]
  have hn := qmaFourTensorAxisCross_norm i j a b true (qmaFourCouplingSign t)
  have hs := qmaFourCouplingSize_bound a b t
  have hnon := qmaFourCouplingSize_nonneg a b t
  calc
    _ ≤ qmaFourCouplingSize a b t*2352 := mul_le_mul_of_nonneg_left hn hnon
    _ ≤ _ := by nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds and excitation identities for the whole physical edge family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaFourTensorCoupling_orthogonal (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*(qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.mul_smul,
    qmaFourTensorWeighted_orthogonal i j hij,smul_zero]

theorem qmaFourTensorCoupling_excitation (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    qmaFourTensorPenalty n*(qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.mul_smul,
    qmaFourTensorWeighted_excitation i j hij,smul_comm (8:ℂ)]

theorem qmaFourTensorFamily_orthogonal (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    (qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorCoupling_orthogonal _ _ (hneq _),Finset.sum_const_zero]

theorem qmaFourTensorFamily_excitation (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    qmaFourTensorPenalty n*(qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) =
      (8:ℂ) • (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n) := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul,Matrix.mul_sum,
    qmaFourTensorCoupling_excitation _ _ (hneq _),Finset.smul_sum]

theorem qmaFourTensorFamily_norm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖ ≤
      7056*(∑ e, (1+|t e|)) := by
  rw [qmaFourTensorFamilyCoupling,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorCoupling_norm _ _ _ _ _))

theorem qmaSiteMatrix_commute (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i A*qmaSiteMatrix j B = qmaSiteMatrix j B*qmaSiteMatrix i A := by
  simp only [qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp only [ite_true, if_true,hij,ite_false, if_false,Matrix.mul_one,Matrix.one_mul]
  · by_cases hj : k = j
    · subst k
      simp only [ite_true, if_true,Ne.symm hij,ite_false, if_false,Matrix.mul_one,Matrix.one_mul]
    · simp only [hi,hj,ite_false, if_false]

theorem qmaFourTensorCross_star (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (qmaFourTensorCross i j p q).conjTranspose = qmaFourTensorCross i j p q := by
  simp only [qmaFourTensorCross,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    qmaSiteMatrix_star,qmaFourSpin_star]
  apply Finset.sum_congr rfl
  intro μ _
  exact qmaSiteMatrix_commute j i (Ne.symm hij) _ _

theorem qmaFourTensorCoupling_star (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorCoupling i j a b t).conjTranspose = qmaFourTensorCoupling i j a b t := by
  simp only [qmaFourTensorCoupling,qmaFourTensorWeighted,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum,Complex.star_def,Complex.conj_ofReal,qmaFourTensorCross_star i j hij]

theorem qmaFourTensorFamily_star (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e) :
    (qmaFourTensorFamilyCoupling left right a b t).conjTranspose =
      qmaFourTensorFamilyCoupling left right a b t := by
  simp only [qmaFourTensorFamilyCoupling,Matrix.conjTranspose_sum,
    qmaFourTensorCoupling_star _ _ (hneq _)]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFields
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourSpin_commute (p q : Fin 4) (hpq : p ≠ q) (μ ν : Fin 3) :
    qmaFourSpin p μ*qmaFourSpin q ν = qmaFourSpin q ν*qmaFourSpin p μ := by
  simp only [qmaFourSpin_source]
  change (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 q ν).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm =
    (sourceLocalPauli 4 q ν).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm
  rw [Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,sourceLocalPauli_commute 4 p q hpq]

theorem qmaFourExchange_star (p q : Fin 4) (hpq : p ≠ q) :
    (qmaFourExchange p q).conjTranspose = qmaFourExchange p q := by
  simp only [qmaFourExchange_pauli p q hpq,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    qmaFourSpin_star,qmaFourSpin_commute q p (Ne.symm hpq)]

theorem qmaFourTensorExchange_norm (i : Fin n) (p q : Fin 4) (hpq : p ≠ q) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange p q))‖ ≤ 3 := by
  rw [qmaFourExchange_pauli p q hpq,qmaSiteMatrix_sum,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourSpin p μ*qmaFourSpin q μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      rw [← qmaSiteMatrix_mul,spinMatrixOperator_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using (mul_le_mul (qmaFourTensorSpin_norm i p μ) (qmaFourTensorSpin_norm i q μ)
          (norm_nonneg _) zero_le_one))
    _ = 3 := by norm_num

theorem qmaSiteMatrix_neg (i : Fin n) (A : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (-A) = -qmaSiteMatrix i A := by
  rw [← neg_one_smul ℂ A,qmaSiteMatrix_smul,neg_one_smul]

theorem qmaSiteMatrix_sub (i : Fin n) (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    qmaSiteMatrix i (A-B) = qmaSiteMatrix i A-qmaSiteMatrix i B := by
  simp only [sub_eq_add_neg,qmaSiteMatrix_add,qmaSiteMatrix_neg]

theorem qmaFourField_star (x z : ℝ) : (qmaFourField x z).conjTranspose = qmaFourField x z := by
  simp only [qmaFourField,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Complex.star_def,Complex.conj_ofReal,qmaFourExchange_star 0 3 (by decide),
    qmaFourExchange_star 0 2 (by decide),qmaFourExchange_star 0 1 (by decide)]

theorem qmaFourTensorField_norm (i : Fin n) (x z : ℝ) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourField x z))‖ ≤ 6*(|x|+|z|) := by
  have hs : 1 ≤ Real.sqrt 3 := by
    have h0 := Real.sqrt_nonneg 3
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    nlinarith
  have hx : |x/(2*Real.sqrt 3)| ≤ |x| := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt 3)]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt 3)).mpr
    nlinarith [abs_nonneg x]
  have hz : |z/2| ≤ |z| := by rw [abs_div]; norm_num
  rw [qmaFourField,qmaSiteMatrix_sub,qmaSiteMatrix_smul,qmaSiteMatrix_smul,
    qmaSiteMatrix_sub,spinMatrixOperator_sub,spinMatrixOperator_smul,spinMatrixOperator_smul]
  have hdiff : ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 3)-
      qmaSiteMatrix i (qmaFourExchange 0 2))‖ ≤ 6 := by
    rw [spinMatrixOperator_sub]
    exact (norm_sub_le _ _).trans ((add_le_add (qmaFourTensorExchange_norm i 0 3 (by decide))
      (qmaFourTensorExchange_norm i 0 2 (by decide))).trans_eq (by norm_num))
  have hlast := qmaFourTensorExchange_norm i 0 1 (by decide)
  calc
    _ ≤ ‖((x/(2*Real.sqrt 3):ℝ):ℂ) • spinMatrixOperator
          (qmaSiteMatrix i (qmaFourExchange 0 3)-qmaSiteMatrix i (qmaFourExchange 0 2))‖+
        ‖((z/2:ℝ):ℂ) • spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 1))‖ := norm_sub_le _ _
    _ = |x/(2*Real.sqrt 3)| * ‖spinMatrixOperator
          (qmaSiteMatrix i (qmaFourExchange 0 3)-qmaSiteMatrix i (qmaFourExchange 0 2))‖+
        |z/2| * ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourExchange 0 1))‖ := by
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |x| * 6+|z| * 3 := add_le_add (mul_le_mul hx hdiff (norm_nonneg _) (abs_nonneg x))
      (mul_le_mul hz hlast (norm_nonneg _) (abs_nonneg z))
    _ ≤ _ := by nlinarith [abs_nonneg z]

theorem qmaFourAxisField_star (a : Fin 2) (t : ℝ) :
    (qmaFourAxisField a t).conjTranspose = qmaFourAxisField a t := by
  unfold qmaFourAxisField
  split_ifs <;> exact qmaFourField_star _ _

theorem qmaFourTensorAxisField_norm (i : Fin n) (a : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourAxisField a t))‖ ≤ 6*|t| := by
  unfold qmaFourAxisField
  split_ifs
  · simpa only [abs_zero,add_zero] using qmaFourTensorField_norm i t 0
  · simpa only [abs_zero,zero_add] using qmaFourTensorField_norm i 0 t

theorem qmaFourTensorCounterterm_star (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    (qmaFourTensorCounterterm i j a b t).conjTranspose = qmaFourTensorCounterterm i j a b t := by
  simp only [qmaFourTensorCounterterm,Matrix.conjTranspose_add,qmaSiteMatrix_star,qmaFourAxisField_star]

theorem qmaFourTensorCounterterm_norm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCounterterm i j a b t)‖ ≤
      6*(|qmaFourCounterA a b t|+|qmaFourCounterB a b t|) := by
  rw [qmaFourTensorCounterterm,spinMatrixOperator_add]
  exact (norm_add_le _ _).trans ((add_le_add (qmaFourTensorAxisField_norm i a _)
    (qmaFourTensorAxisField_norm j b _)).trans_eq (by ring))

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

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaFourTensorCounterterm_linear_bound (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCounterterm i j a b t)‖ ≤ 1228800*|t| := by
  apply (qmaFourTensorCounterterm_norm i j a b t).trans
  have ha := qmaFourCounterA_bound a b t
  have hb := qmaFourCounterB_bound a b t
  linarith

theorem qmaFourTensorFamilyCounterterm_bound (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFamilyCounterterm left right a b t)‖ ≤
      1228800*(∑ e, |t e|) := by
  rw [qmaFourTensorFamilyCounterterm,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorCounterterm_linear_bound _ _ _ _ _))

theorem qmaFourTensorFamilyCounterterm_star (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) :
    (qmaFourTensorFamilyCounterterm left right a b t).conjTranspose =
      qmaFourTensorFamilyCounterterm left right a b t := by
  simp only [qmaFourTensorFamilyCounterterm,Matrix.conjTranspose_sum,qmaFourTensorCounterterm_star]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoerciveInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coercive inverse needed for the padded four-spin penalty. -/

noncomputable section
namespace ContinuumCoulomb
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem qmaCoerciveInverse_exists (A : E →L[ℝ] E) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ x, g*‖x‖^2 ≤ ⟪x,A x⟫_ℝ) :
    ∃ T : E →L[ℝ] E, (∀ x, A (T x) = x) ∧ (∀ x, T (A x) = x) ∧ ‖T‖ ≤ 1/g := by
  have hi : Function.Injective A := by
    intro x y hxy
    have hz : A (x-y) = 0 := by simp only [map_sub,hxy,sub_self]
    have hh := hgap (x-y)
    rw [hz,inner_zero_right] at hh
    have hn : ‖x-y‖ = 0 := by
      by_contra hn
      have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      exact (not_lt_of_ge hh) (mul_pos hg (sq_pos_of_pos hp))
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective A.toLinearMap
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  let T : E →L[ℝ] E := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hAT (x : E) : A (T x) = x := by
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  have hTA (x : E) : T (A x) = x := by
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  refine ⟨T,hAT,hTA,?_⟩
  apply T.opNorm_le_bound (by positivity)
  intro x
  have hh := hgap (T x)
  rw [hAT] at hh
  have hc := real_inner_le_norm (T x) x
  have hb : g*‖T x‖ ≤ ‖x‖ := by
    by_cases hz : ‖T x‖ = 0
    · rw [hz,mul_zero]
      exact norm_nonneg _
    · have hp : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  calc
    ‖T x‖ ≤ ‖x‖/g := (le_div_iff₀ hg).mpr (by nlinarith)
    _ = (1/g)*‖x‖ := by ring

omit [FiniteDimensional ℝ E] in
theorem qmaInverse_eigenvector (A T : E →L[ℝ] E) (hTA : ∀ x, T (A x) = x)
    (x : E) {c : ℝ} (hc : c ≠ 0) (hx : A x = c • x) : T x = c⁻¹ • x := by
  have h := hTA x
  rw [hx,map_smul] at h
  calc
    T x = c⁻¹ • (c • T x) := by rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
    _ = c⁻¹ • x := by rw [h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QubitMediatorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical energy equals the block energy on its genuine
vacuum/complement decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] in
theorem qmaMatrixOperator_real_symmetric (M : Matrix σ σ ℂ) (hM : M.conjTranspose = M)
    (x y : EuclideanSpace ℂ σ) :
    ⟪x,qmaMatrixOperator M y⟫_ℝ = ⟪qmaMatrixOperator M x,y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator M) x y
  rw [← qmaMatrixOperator_star,hM] at h
  exact congrArg Complex.re h

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

theorem qmaFourTensor_restrict_include (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorRestriction n (qmaFourTensorInclusion n p) = p := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = p
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorEncoding_gram,
    qmaMatrixOperator_square,spinMatrixOperator_one]
  rfl

theorem qmaFourTensor_inclusion_adjoint (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2))
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪qmaFourTensorInclusion n p,x⟫_ℝ = ⟪p,qmaFourTensorRestriction n x⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator (qmaFourTensorEncoding n)) p x
  rw [← qmaMatrixOperator_star] at h
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  exact congrArg Complex.re h.symm

theorem qmaFourTensor_highPart (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    Perturbation.orthogonalHighPart (qmaFourTensorInclusion n) (qmaFourTensorRestriction n) x =
      qmaFourTensorHigh n x := by
  unfold Perturbation.orthogonalHighPart qmaFourTensorHigh qmaFourTensorInclusion qmaFourTensorRestriction
  change x-qmaMatrixOperator _ (qmaMatrixOperator _ x) = qmaMatrixOperator _ x
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorEncoding_projector]
  simp only [qmaMatrixOperator_square,spinMatrixOperator_sub,spinMatrixOperator_one]
  rfl

theorem qmaFourTensorRestriction_high (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaFourTensorRestriction n (qmaFourTensorHigh n x) = 0 := by
  rw [← qmaFourTensor_highPart]
  exact Perturbation.orthogonalHighPart_kernel _ _ (qmaFourTensor_restrict_include n) x

theorem qmaFourTensor_projection_star (n : ℕ) :
    (qmaFourTensorProjection n).conjTranspose = qmaFourTensorProjection n := by
  rw [← qmaFourTensorEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem qmaFourTensor_inverse_exists (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16),
      (∀ x, qmaFourTensorPadded n r (T x) = x) ∧
      (∀ x, T (qmaFourTensorPadded n r x) = x) ∧ ‖T‖ ≤ 1/(4*r^2) :=
  qmaCoerciveInverse_exists _ (by positivity) (qmaFourTensor_padded_gap n r)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorInverse
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

theorem qmaFourTensorPadded_column
    (W : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ)
    (hW : (qmaFourTensorEncoding n).conjTranspose*W = 0)
    (hH : qmaFourTensorPenalty n*W = (8:ℂ) • W) :
    qmaFourTensorPaddedMatrix n*W = (8:ℂ) • W := by
  rw [qmaFourTensorPaddedMatrix,Matrix.add_mul,hH,Matrix.smul_mul,
    ← qmaFourTensorEncoding_projector,Matrix.mul_assoc,hW,Matrix.mul_zero,smul_zero,add_zero]

theorem qmaFourTensorInverse_column {r : ℝ} (hr : 0 < r)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x)
    (W : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ)
    (hW : (qmaFourTensorEncoding n).conjTranspose*W = 0)
    (hH : qmaFourTensorPenalty n*W = (8:ℂ) • W)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    T (qmaMatrixOperator W p) = (8*r^2)⁻¹ • qmaMatrixOperator W p := by
  apply qmaInverse_eigenvector _ _ hTA _ (by positivity)
  have he := congrArg (fun M => qmaMatrixOperator M p) (qmaFourTensorPadded_column W hW hH)
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at he
  change r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) (qmaMatrixOperator W p) = _
  simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply] at he
  rw [he]
  ext s
  simp only [PiLp.smul_apply,Complex.real_smul]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full physical quadratic form in its actual encoded and orthogonal coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_inclusion_norm (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖qmaFourTensorInclusion n p‖ = ‖p‖ :=
  Perturbation.orthogonalInclusion_norm _ _ (qmaFourTensor_restrict_include n)
    (qmaFourTensor_inclusion_adjoint n) p

theorem qmaFourTensor_norm_decomposition (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ‖qmaFourTensorRestriction n x‖^2+‖qmaFourTensorHigh n x‖^2 = ‖x‖^2 := by
  rw [← qmaFourTensor_highPart]
  exact Perturbation.orthogonalParts_norm _ _ (qmaFourTensor_restrict_include n)
    (qmaFourTensor_inclusion_adjoint n) x

theorem qmaFourTensorHigh_norm (n : ℕ) : ‖qmaFourTensorHigh n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := qmaFourTensor_norm_decomposition n x
  have h0 := norm_nonneg (qmaFourTensorHigh n x)
  have h1 := norm_nonneg x
  rw [one_mul]
  nlinarith [sq_nonneg ‖qmaFourTensorRestriction n x‖]

theorem qmaFourTensorHigh_fixed (x : EuclideanSpace ℂ (Fin n → Fin 16))
    (hx : qmaFourTensorRestriction n x = 0) : qmaFourTensorHigh n x = x := by
  rw [← qmaFourTensor_highPart]
  simp only [Perturbation.orthogonalHighPart,hx,map_zero,sub_zero]

theorem qmaFourTensorHigh_symmetric (x y : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorHigh n y⟫_ℝ = ⟪qmaFourTensorHigh n x,y⟫_ℝ := by
  apply qmaMatrixOperator_real_symmetric
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,qmaFourTensor_projection_star]

theorem qmaFourTensor_penalty_low (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaMatrixOperator (qmaFourTensorPenalty n) (qmaFourTensorInclusion n p) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorPenalty_encoding]
  ext s
  simp only [qmaMatrixOperator_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,PiLp.zero_apply]

theorem qmaFourTensor_padded_high (r : ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16))
    (hx : qmaFourTensorRestriction n x = 0) :
    qmaFourTensorPadded n r x = r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) x := by
  have hp : qmaMatrixOperator (qmaFourTensorProjection n) x = 0 := by
    rw [← qmaFourTensorEncoding_projector,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply]
    change qmaFourTensorInclusion n (qmaFourTensorRestriction n x) = 0
    rw [hx,map_zero]
  change r^2 • qmaMatrixOperator (_+_) x = _
  rw [qmaMatrixOperator_add,_root_.add_apply,qmaMatrixOperator_smul,
    _root_.smul_apply,hp,smul_zero,add_zero]

theorem qmaFourTensorPhysical_low (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorPhysical r K (qmaFourTensorInclusion n p) =
      qmaFourTensorInclusion n (qmaFourTensorLow K p)+qmaFourTensorOff K p := by
  change r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) (qmaFourTensorInclusion n p)+
    K (qmaFourTensorInclusion n p) = _
  rw [qmaFourTensor_penalty_low,smul_zero,zero_add]
  symm
  have h := Perturbation.orthogonal_assemble (qmaFourTensorInclusion n)
    (qmaFourTensorRestriction n) (K (qmaFourTensorInclusion n p))
  rw [qmaFourTensor_highPart] at h
  exact h

theorem qmaFourTensorPhysical_high (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) (hx : qmaFourTensorRestriction n x = 0) :
    ⟪x,qmaFourTensorPhysical r K x⟫_ℝ =
      Perturbation.penaltyForm (qmaFourTensorPadded n r) x+⟪x,qmaFourTensorHighPerturbation K x⟫_ℝ := by
  change ⟪x,r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) x+K x⟫_ℝ = _
  rw [inner_add_right,← qmaFourTensor_padded_high r x hx]
  congr 1
  change ⟪x,K x⟫_ℝ = ⟪x,qmaFourTensorHigh n (K (qmaFourTensorHigh n x))⟫_ℝ
  rw [qmaFourTensorHigh_fixed x hx,qmaFourTensorHigh_symmetric,qmaFourTensorHigh_fixed x hx]

theorem qmaFourTensorPhysical_energy (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hK : ∀ x y, ⟪x,K y⟫_ℝ = ⟪K x,y⟫_ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorPhysical r K x⟫_ℝ =
      Perturbation.lowBlockEnergy (qmaFourTensorLow K) (qmaFourTensorPadded n r)
        (qmaFourTensorHighPerturbation K) (qmaFourTensorOff K)
        (qmaFourTensorRestriction n x) (qmaFourTensorHigh n x) := by
  rw [← qmaFourTensor_highPart]
  apply Perturbation.orthogonalBlock_full_energy
    (qmaFourTensorInclusion n) (qmaFourTensorRestriction n)
  · exact qmaFourTensor_restrict_include n
  · exact qmaFourTensor_inclusion_adjoint n
  · exact qmaFourTensorPhysical_symmetric r K hK
  · exact qmaFourTensorPhysical_low r K
  · intro p
    exact qmaFourTensorRestriction_high n _
  · exact qmaFourTensorPhysical_high r K

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The counterterm's off-diagonal contribution to the second-order energy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem qmaInverse_symmetric (A T : H →L[ℝ] H)
    (hAT : ∀ x, A (T x) = x)
    (hA : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ) (x y : H) :
    ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ := by
  calc
    _ = ⟪A (T x),T y⟫_ℝ := by rw [hAT]
    _ = ⟪T x,A (T y)⟫_ℝ := (hA _ _).symm
    _ = _ := by rw [hAT]

theorem qmaSecondOrder_column_identity (T : H →L[ℝ] H) {r : ℝ} (hr : r ≠ 0)
    (hT : ∀ x y, ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ) (w z : H)
    (hw : T w = (8*r^2)⁻¹ • w) :
    ⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2 =
      (1/(4*r))*⟪w,z⟫_ℝ+⟪z,T z⟫_ℝ := by
  have hwz : ⟪w,T z⟫_ℝ = (8*r^2)⁻¹*⟪w,z⟫_ℝ := by
    rw [hT,hw,inner_smul_left]
    simp only [starRingEnd_apply,star_trivial]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_trivial,hwz,hw,real_inner_self_eq_norm_sq]
  simp only [real_inner_comm z w]
  field_simp
  ring

theorem qmaSecondOrder_column_error (T : H →L[ℝ] H) {r v c l : ℝ} (hr : 0 < r)
    (hv : 0 ≤ v) (_hc : 0 ≤ c) (hl : 0 ≤ l)
    (hT : ∀ x y, ⟪x,T y⟫_ℝ = ⟪T x,y⟫_ℝ) (hTn : ‖T‖ ≤ 1/(4*r^2))
    (w z : H) (hw : T w = (8*r^2)⁻¹ • w) (hwn : ‖w‖ ≤ v*l) (hzn : ‖z‖ ≤ c*l) :
    |⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2| ≤
      (v*c/(4*r)+c^2/(4*r^2))*l^2 := by
  have hwz : |⟪w,z⟫_ℝ| ≤ v*c*l^2 := by
    calc
      _ ≤ ‖w‖*‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ (v*l)*(c*l) := mul_le_mul hwn hzn (norm_nonneg _) (mul_nonneg hv hl)
      _ = _ := by ring
  have hz2 : ‖z‖^2 ≤ c^2*l^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg z) hzn 2
  have hzt : |⟪z,T z⟫_ℝ| ≤ c^2/(4*r^2)*l^2 := by
    calc
      _ ≤ ‖z‖*‖T z‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖z‖*(‖T‖*‖z‖) := mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg z)
      _ = ‖T‖*‖z‖^2 := by ring
      _ ≤ (1/(4*r^2))*(c^2*l^2) := mul_le_mul hTn hz2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  rw [qmaSecondOrder_column_identity T (ne_of_gt hr) hT w z hw]
  calc
    _ ≤ |(1/(4*r))*⟪w,z⟫_ℝ|+|⟪z,T z⟫_ℝ| := abs_add_le _ _
    _ = (1/(4*r))*|⟪w,z⟫_ℝ|+|⟪z,T z⟫_ℝ| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(4*r))]
    _ ≤ (1/(4*r))*(v*c*l^2)+c^2/(4*r^2)*l^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hwz (by positivity)) hzt
    _ = _ := by ring

theorem qmaSecondOrder_inverse_column_bound (T : H →L[ℝ] H) {r v c l : ℝ} (hr : 0 < r)
    (hTn : ‖T‖ ≤ 1/(4*r^2)) (w z : H) (hw : T w = (8*r^2)⁻¹ • w)
    (hwn : ‖w‖ ≤ v*l) (hzn : ‖z‖ ≤ c*l) :
    ‖T (r • w+z)‖ ≤ (v/(8*r)+c/(4*r^2))*l := by
  rw [map_add,map_smul,hw,smul_smul]
  have hs : r*(8*r^2)⁻¹ = 1/(8*r) := by field_simp
  rw [hs]
  calc
    _ ≤ ‖(1/(8*r)) • w‖+‖T z‖ := norm_add_le _ _
    _ = (1/(8*r))*‖w‖+‖T z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    _ ≤ (1/(8*r))*(v*l)+(1/(4*r^2))*(c*l) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hwn (by positivity))
      exact (T.le_opNorm z).trans
        (mul_le_mul hTn hzn (norm_nonneg _) (by positivity))
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorEffectiveError
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual effective form approximates the calibrated tensor matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_restrict_column (V : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorRestriction n (qmaMatrixOperator V (qmaFourTensorInclusion n p)) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ (qmaMatrixOperator _ p)) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,
    ← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,Matrix.mul_assoc,hV]
  ext s
  simp only [qmaMatrixOperator_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,PiLp.zero_apply]

theorem qmaFourTensorOff_split (r : ℝ) (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorOff (qmaFourTensorPerturbation r V C) p =
      r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
        qmaFourTensorHigh n (qmaMatrixOperator C (qmaFourTensorInclusion n p)) := by
  change qmaFourTensorHigh n (r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
    qmaMatrixOperator C (qmaFourTensorInclusion n p)) = _
  rw [map_add,map_smul,qmaFourTensorHigh_fixed _ (qmaFourTensor_restrict_column V hV p)]

theorem qmaQuadratic_operator_gram {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (W : Matrix σ τ ℂ) (p : EuclideanSpace ℂ τ) :
    qmaQuadratic (W.conjTranspose*W) (fun i => p i) = ‖qmaMatrixOperator W p‖^2 := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,
    ← qmaMatrixOperator_real_adjoint,real_inner_self_eq_norm_sq]

theorem qmaFourTensorEffectiveMatrix_form
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaQuadratic (qmaFourTensorEffectiveMatrix V C) (fun i => p i) =
      ⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-
        (1/8)*‖qmaMatrixOperator V (qmaFourTensorInclusion n p)‖^2 := by
  rw [qmaFourTensorEffectiveMatrix,qmaQuadratic_sub,
    show (1/8:ℂ) = ((1/8:ℝ):ℂ) from by norm_num,qmaQuadratic_smul,
    qmaQuadratic_sandwich,qmaQuadratic_operator_gram,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply]
  rfl

theorem qmaFourTensorLow_form (r : ℝ) (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ⟪p,qmaFourTensorLow (qmaFourTensorPerturbation r V C) p⟫_ℝ =
      ⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ := by
  change ⟪p,qmaFourTensorRestriction n (qmaFourTensorPerturbation r V C (qmaFourTensorInclusion n p))⟫_ℝ = _
  rw [← qmaFourTensor_inclusion_adjoint]
  change ⟪qmaFourTensorInclusion n p,r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
    qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ = _
  rw [inner_add_right,inner_smul_right,qmaFourTensor_inclusion_adjoint,
    qmaFourTensor_restrict_column V hV p,inner_zero_right,mul_zero,zero_add]

theorem qmaFourTensor_column_norm (M : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    {b : ℝ} (hb : ‖spinMatrixOperator M‖ ≤ b) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖qmaMatrixOperator M (qmaFourTensorInclusion n p)‖ ≤ b*‖p‖ := by
  apply ((qmaMatrixOperator M).le_opNorm _).trans
  rw [qmaMatrixOperator_square,qmaFourTensor_inclusion_norm]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg p)

theorem qmaFourTensorEffective_error (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x) (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x)
    (hTn : ‖T‖ ≤ 1/(4*r^2)) {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    |Perturbation.effectiveForm (qmaFourTensorLow (qmaFourTensorPerturbation r V C)) T
        (qmaFourTensorOff (qmaFourTensorPerturbation r V C)) p-
      qmaQuadratic (qmaFourTensorEffectiveMatrix V C) (fun i => p i)| ≤
      (v*c/(4*r)+c^2/(4*r^2))*‖p‖^2 := by
  let w := qmaMatrixOperator V (qmaFourTensorInclusion n p)
  let z := qmaFourTensorHigh n (qmaMatrixOperator C (qmaFourTensorInclusion n p))
  have hw : T w = (8*r^2)⁻¹ • w := by
    have h := qmaFourTensorInverse_column hr T hTA (V*qmaFourTensorEncoding n) hV hH p
    simpa only [qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,w,qmaFourTensorInclusion,
      ContinuousLinearMap.coe_restrictScalars'] using h
  have hwn : ‖w‖ ≤ v*‖p‖ := qmaFourTensor_column_norm V hVn p
  have hzn : ‖z‖ ≤ c*‖p‖ := by
    apply ((qmaFourTensorHigh n).le_opNorm _).trans
    exact (mul_le_mul (qmaFourTensorHigh_norm n) (qmaFourTensor_column_norm C hCn p)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h := qmaSecondOrder_column_error T hr hv hc (norm_nonneg p)
    (qmaInverse_symmetric _ T hAT (qmaFourTensorPadded_symmetric n r)) hTn w z hw hwn hzn
  rw [Perturbation.effectiveForm,Perturbation.inverseForm,qmaFourTensorLow_form r V C hV p,
    qmaFourTensorEffectiveMatrix_form,qmaFourTensorOff_split r V C hV p]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [show (⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-
      ⟪r • w+z,T (r • w+z)⟫_ℝ)-
      (⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-(1/8)*‖w‖^2) =
        -(⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2) by ring,abs_neg]

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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorGround
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full physical ground-energy comparison for the four-spin tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensorPhysicalMatrix_apply (r : ℝ)
    (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaMatrixOperator (qmaFourTensorPhysicalMatrix r U) x =
      qmaFourTensorPhysical r ((qmaMatrixOperator U).restrictScalars ℝ) x := by
  rw [qmaFourTensorPhysicalMatrix,qmaMatrixOperator_add,qmaMatrixOperator_smul,qmaFourTensorPhysical]
  ext s
  simp only [_root_.add_apply,_root_.smul_apply,PiLp.add_apply,PiLp.smul_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars',Complex.real_smul,Complex.ofReal_pow,
    smul_eq_mul]

theorem qmaFourTensorHighPerturbation_norm
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :
    ‖qmaFourTensorHighPerturbation K‖ ≤ ‖K‖ := by
  unfold qmaFourTensorHighPerturbation
  calc
    _ ≤ ‖qmaFourTensorHigh n‖*‖K.comp (qmaFourTensorHigh n)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(‖K‖*1) := mul_le_mul (qmaFourTensorHigh_norm n)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (qmaFourTensorHigh_norm n) (norm_nonneg K)))
      (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem qmaFourTensorGround_error (r : ℝ) (hr : 0 < r)
    (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) (hU : U.conjTranspose = U)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x)
    {d m η : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m) (hη : 0 ≤ η)
    (hsmall : 2*(d+m) ≤ 4*r^2) (hUn : ‖spinMatrixOperator U‖ ≤ d)
    (hTB : ∀ p, ‖T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ) p)‖ ≤ η*‖p‖)
    (hbound : ∀ p : EuclideanSpace ℂ (Fin n → Fin 2), ‖p‖ = 1 →
      |Perturbation.effectiveForm (qmaFourTensorLow ((qmaMatrixOperator U).restrictScalars ℝ))
        T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ)) p| ≤ m)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U)-
      Perturbation.effectiveBottom (qmaFourTensorLow ((qmaMatrixOperator U).restrictScalars ℝ))
        T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ))| ≤ 2*(d+m)*η^2 := by
  let K := (qmaMatrixOperator U).restrictScalars ℝ
  let C := qmaFourTensorLow K
  let B := qmaFourTensorOff K
  let D := qmaFourTensorHighPerturbation K
  let A := qmaFourTensorPadded n r
  have hK : ∀ x y, ⟪x,K y⟫_ℝ = ⟪K x,y⟫_ℝ := qmaMatrixOperator_real_symmetric U hU
  have hDnorm : ‖D‖ ≤ d := (qmaFourTensorHighPerturbation_norm K).trans (by
    simpa only [K,ContinuousLinearMap.norm_restrictScalars,qmaMatrixOperator_square] using hUn)
  have hD (q : EuclideanSpace ℂ (Fin n → Fin 16)) : |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2 := by
    simpa only [one_mul] using Perturbation.highPerturbation_abs_le D
      (g := d) (ε := 1) (by simpa only [one_mul] using hDnorm) q
  have hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ := qmaFourTensorPadded_symmetric n r
  have hgap : ∀ q, (4*r^2)*‖q‖^2 ≤ Perturbation.penaltyForm A q :=
    qmaFourTensor_padded_gap n r
  obtain ⟨p,hp,hmin⟩ := Perturbation.effectiveForm_minimizer C T B u hu
  rw [Perturbation.effectiveBottom_eq C T B p hp hmin]
  let μ := Perturbation.effectiveForm C T B p
  let ε := 2*(d+m)*η^2
  have hμ : |μ| ≤ m := hbound p hp
  have hl (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
      (μ-ε)*‖x‖^2 ≤ ⟪x,qmaFourTensorPhysical r K x⟫_ℝ := by
    rw [qmaFourTensorPhysical_energy r K hK]
    have h := Perturbation.sharp_lowBlockEnergy_lower C A T D B hd hm hη hsmall hAT hAsymm hgap
      hTB hD (abs_le.mp hμ).2 hmin (qmaFourTensorRestriction n x) (qmaFourTensorHigh n x)
    rw [qmaFourTensor_norm_decomposition] at h
    have hle : ‖qmaFourTensorRestriction n x‖^2 ≤ ‖x‖^2 := by
      have hn := qmaFourTensor_norm_decomposition n x
      nlinarith [sq_nonneg ‖qmaFourTensorHigh n x‖]
    have he : 0 ≤ ε := by dsimp [ε]; positivity
    nlinarith
  have hu0 : ‖qmaFourTensorInclusion n u‖ = 1 := (qmaFourTensor_inclusion_norm n u).trans hu
  have hlow : μ-ε ≤ MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U) := by
    apply le_qmaNormalizedBottom _ (qmaFourTensorInclusion n u) hu0
    intro x hx
    rw [qmaQuadratic_operator,qmaFourTensorPhysicalMatrix_apply]
    simpa only [hx,one_pow,mul_one] using hl x
  let q := -(T (B p))
  let x := qmaFourTensorInclusion n p+q
  have hq : qmaFourTensorRestriction n q = 0 := by
    change qmaFourTensorRestriction n (-(T (B p))) = 0
    rw [map_neg,qmaFourTensorInverse_high hr T hAT (B p) (qmaFourTensorRestriction_high n _),neg_zero]
  have hxn : ‖x‖^2 = ‖p‖^2+‖q‖^2 :=
    Perturbation.orthogonalAssemble_norm _ _ (qmaFourTensor_restrict_include n)
      (qmaFourTensor_inclusion_adjoint n) p q hq
  have hxpos : 0 < ‖x‖^2 := by rw [hxn,hp]; positivity
  have hxe : ⟪x,qmaFourTensorPhysical r K x⟫_ℝ = Perturbation.lowBlockEnergy C A D B p q :=
    Perturbation.orthogonalBlock_energy _ _ _ _ _ _ _ (qmaFourTensor_restrict_include n)
      (qmaFourTensor_inclusion_adjoint n) (qmaFourTensorPhysical_symmetric r K hK)
      (qmaFourTensorPhysical_low r K) (fun _ => qmaFourTensorRestriction_high n _)
      (qmaFourTensorPhysical_high r K) p q hq
  have htrial : ⟪x,qmaFourTensorPhysical r K x⟫_ℝ/‖x‖^2 ≤ μ+(d+m)*η^2 := by
    rw [hxe,hxn]
    exact Perturbation.sharp_lowBlockRayleigh_trial_upper C A T D B hd hm hη hAT hTB hD
      (abs_le.mp hμ).1 p hp rfl
  have hb : BddBelow {e | ∃ x : EuclideanSpace ℂ (Fin n → Fin 16), 0 < ‖x‖^2 ∧
      e = ⟪x,spinMatrixOperator (qmaFourTensorPhysicalMatrix r U) x⟫_ℝ/‖x‖^2} := by
    refine ⟨μ-ε,?_⟩
    rintro e ⟨y,hy,rfl⟩
    rw [← qmaMatrixOperator_square,qmaFourTensorPhysicalMatrix_apply]
    exact (le_div_iff₀ hy).mpr (hl y)
  have hup : MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U) ≤ μ+(d+m)*η^2 := by
    rw [MediatorGraph.normalizedBottom_eq_rayleigh]
    apply (csInf_le hb ⟨x,hxpos,rfl⟩).trans
    simpa only [← qmaMatrixOperator_square,qmaFourTensorPhysicalMatrix_apply] using htrial
  have heps : (d+m)*η^2 ≤ ε := by
    dsimp [ε]
    nlinarith [mul_nonneg (add_nonneg hd hm) (sq_nonneg η)]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit full-space comparison with the calibrated logical matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaEffectiveBottom_matrix_error
    (L : EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 2))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (B : EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (N : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) {δ : ℝ}
    (he : ∀ p : EuclideanSpace ℂ (Fin n → Fin 2), ‖p‖ = 1 →
      |Perturbation.effectiveForm L T B p-qmaQuadratic N (fun i => p i)| ≤ δ) :
    |Perturbation.effectiveBottom L T B-MediatorGraph.normalizedBottom N| ≤ δ := by
  obtain ⟨p,hp,hmin⟩ := Perturbation.effectiveForm_minimizer L T B u hu
  rw [Perturbation.effectiveBottom_eq L T B p hp hmin]
  have hlow := qmaNormalizedBottom_le N p hp
  have herror := abs_le.mp (he p hp)
  have hupp : Perturbation.effectiveForm L T B p-δ ≤ MediatorGraph.normalizedBottom N := by
    apply le_qmaNormalizedBottom N u hu
    intro x hx
    have hm := hmin x
    simp only [hx,one_pow,mul_one] at hm
    have herr := (abs_le.mp (he x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem qmaFourTensorPerturbation_operator (r : ℝ)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    (qmaMatrixOperator ((r:ℂ) • V+C)).restrictScalars ℝ = qmaFourTensorPerturbation r V C := by
  rw [qmaMatrixOperator_add,qmaMatrixOperator_smul]
  ext x s
  change (r:ℂ)*(qmaMatrixOperator V x) s+(qmaMatrixOperator C x) s =
    (r • qmaMatrixOperator V x+qmaMatrixOperator C x) s
  simp only [PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]

theorem qmaFourTensorOff_inverse_bound (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x) (hTn : ‖T‖ ≤ 1/(4*r^2))
    {v c : ℝ} (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖T (qmaFourTensorOff (qmaFourTensorPerturbation r V C) p)‖ ≤
      (v/(8*r)+c/(4*r^2))*‖p‖ := by
  rw [qmaFourTensorOff_split r V C hV p]
  apply qmaSecondOrder_inverse_column_bound T hr hTn
  · have h := qmaFourTensorInverse_column hr T hTA (V*qmaFourTensorEncoding n) hV hH p
    simpa only [qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,qmaFourTensorInclusion,
      ContinuousLinearMap.coe_restrictScalars'] using h
  · exact qmaFourTensor_column_norm V hVn p
  · apply ((qmaFourTensorHigh n).le_opNorm _).trans
    exact (mul_le_mul (qmaFourTensorHigh_norm n) (qmaFourTensor_column_norm C hCn p)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem qmaFourTensor_comparison (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1)
    (hsmall : 2*(r*v+c+‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖+
      (v*c/(4*r)+c^2/(4*r^2))) ≤ 4*r^2) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤
      2*(r*v+c+‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖+
        (v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2+
        (v*c/(4*r)+c^2/(4*r^2)) := by
  let δ := v*c/(4*r)+c^2/(4*r^2)
  let N := qmaFourTensorEffectiveMatrix V C
  let K := qmaFourTensorPerturbation r V C
  obtain ⟨T,hAT,hTA,hTn⟩ := qmaFourTensor_inverse_exists n hr
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have herror (p : EuclideanSpace ℂ (Fin n → Fin 2)) (hp : ‖p‖ = 1) :
      |Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p-
        qmaQuadratic N (fun i => p i)| ≤ δ := by
    simpa only [hp,one_pow,mul_one] using qmaFourTensorEffective_error r hr V C hV hH T hAT hTA hTn hv hc hVn hCn p
  have hbound (p : EuclideanSpace ℂ (Fin n → Fin 2)) (hp : ‖p‖ = 1) :
      |Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p| ≤
        ‖spinMatrixOperator N‖+δ := by
    have he := herror p hp
    have hn := qmaQuadratic_norm_bound N p
    simp only [hp,one_pow,mul_one] at hn
    have ht := abs_sub_le (Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p)
      (qmaQuadratic N (fun i => p i)) 0
    simp only [sub_zero] at ht
    linarith
  have hU : ((r:ℂ) • V+C).conjTranspose = (r:ℂ) • V+C := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hVs,hCs,Complex.star_def,Complex.conj_ofReal]
  have hUn : ‖spinMatrixOperator ((r:ℂ) • V+C)‖ ≤ r*v+c := by
    rw [spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact add_le_add (mul_le_mul_of_nonneg_left hVn hr.le) hCn
  have hground := qmaFourTensorGround_error r hr ((r:ℂ) • V+C) hU T hAT
    (show 0 ≤ r*v+c by positivity) (show 0 ≤ ‖spinMatrixOperator N‖+δ by positivity)
    (show 0 ≤ v/(8*r)+c/(4*r^2) by positivity)
    (by simpa only [add_assoc] using hsmall) hUn
    (by rw [qmaFourTensorPerturbation_operator]; exact qmaFourTensorOff_inverse_bound r hr V C hV hH T hTA hTn hVn hCn)
    (by rw [qmaFourTensorPerturbation_operator]; exact hbound) u hu
  rw [qmaFourTensorPerturbation_operator] at hground
  have heff := qmaEffectiveBottom_matrix_error (qmaFourTensorLow K) T (qmaFourTensorOff K) N u hu herror
  have h := (abs_sub_le
    (MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C)))
    (Perturbation.effectiveBottom (qmaFourTensorLow K) T (qmaFourTensorOff K))
    (MediatorGraph.normalizedBottom N)).trans (add_le_add hground heff)
  simpa only [N,δ,add_assoc] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorScale
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial penalty scale for the full four-spin comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaFourTensor_scale_bounds {b r v c e : ℝ} (hb : 1 ≤ b) (hr : 4*b ≤ r)
    (hv0 : 0 ≤ v) (hc0 : 0 ≤ c) (_he0 : 0 ≤ e) (hv : v ≤ b) (hc : c ≤ b) (he : e ≤ b) :
    2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2))) ≤ 4*r^2 ∧
      2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2+
        (v*c/(4*r)+c^2/(4*r^2)) ≤ 9*b^3/r := by
  have hb0 : 0 ≤ b := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hvc : v*c ≤ b^2 := (mul_le_mul hv hc hc0 hb0).trans_eq (by ring)
  have hc2 : c^2 ≤ b^2 := pow_le_pow_left₀ hc0 hc 2
  have hden : 4*r ≤ 4*r^2 := by nlinarith
  have hδ : v*c/(4*r)+c^2/(4*r^2) ≤ b^2/r := by
    calc
      _ ≤ b^2/(4*r)+b^2/(4*r^2) := add_le_add
        (div_le_div_of_nonneg_right hvc (by positivity))
        (div_le_div_of_nonneg_right hc2 (by positivity))
      _ ≤ b^2/(4*r)+b^2/(4*r) := add_le_add le_rfl
        (div_le_div_of_nonneg_left (sq_nonneg b) (by positivity : 0 < 4*r) hden)
      _ = (b^2/r)/2 := by field_simp; ring
      _ ≤ b^2/r := by nlinarith [div_nonneg (sq_nonneg b) hr0.le]
  have hη : v/(8*r)+c/(4*r^2) ≤ b/r := by
    calc
      _ ≤ b/(8*r)+b/(4*r^2) := add_le_add
        (div_le_div_of_nonneg_right hv (by positivity))
        (div_le_div_of_nonneg_right hc (by positivity))
      _ ≤ b/(8*r)+b/(4*r) := add_le_add le_rfl
        (div_le_div_of_nonneg_left hb0 (by positivity : 0 < 4*r) hden)
      _ = 3/8*(b/r) := by field_simp; ring
      _ ≤ b/r := by nlinarith [div_nonneg hb0 hr0.le]
  have hδb : v*c/(4*r)+c^2/(4*r^2) ≤ b := hδ.trans (by
    apply (div_le_iff₀ hr0).mpr
    nlinarith)
  have hsum : r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)) ≤ 4*b*r := by
    have hrv := mul_le_mul_of_nonneg_left hv hr0.le
    have hbr := mul_le_mul_of_nonneg_left hr1 hb0
    nlinarith
  constructor
  · have hbr := mul_le_mul_of_nonneg_left hr hr0.le
    nlinarith
  · have hη0 : 0 ≤ v/(8*r)+c/(4*r^2) := by positivity
    have hsq := pow_le_pow_left₀ hη0 hη 2
    have hmain : 2*(r*v+c+e+(v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2 ≤ 8*b^3/r := by
      calc
        _ ≤ (2*(4*b*r))*(b/r)^2 := mul_le_mul
          (mul_le_mul_of_nonneg_left hsum (by norm_num)) hsq (sq_nonneg _) (by positivity)
        _ = _ := by field_simp; ring
    have hb23 : b^2 ≤ b^3 := pow_le_pow_right₀ hb (by omega)
    have hδ3 := hδ.trans (div_le_div_of_nonneg_right hb23 hr0.le)
    exact (add_le_add hmain hδ3).trans_eq (by ring)

open Matrix
open scoped InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_polynomial_comparison (r b : ℝ) (hb : 1 ≤ b) (hr : 4*b ≤ r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (hVn : ‖spinMatrixOperator V‖ ≤ b) (hCn : ‖spinMatrixOperator C‖ ≤ b)
    (hNn : ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ b)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤ 9*b^3/r := by
  have hb0 : 0 ≤ b := by linarith
  have hr0 : 0 < r := by linarith
  have hs := qmaFourTensor_scale_bounds hb hr hb0 hb0 (norm_nonneg _)
    (le_refl b) (le_refl b) hNn
  exact (qmaFourTensor_comparison r hr0 V C hVs hCs hV hH hb0 hb0 hVn hCn u hu hs.1).trans hs.2

theorem qmaFourTensor_polynomial_accuracy (b : ℝ) (hb : 1 ≤ b)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (hVn : ‖spinMatrixOperator V‖ ≤ b) (hCn : ‖spinMatrixOperator C‖ ≤ b)
    (hNn : ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ b)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix (9*b^3*N) (((9*b^3*N:ℝ):ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤ 1/(N:ℝ) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hb0 : 0 < b := by linarith
  have hb13 : b ≤ b^3 := by simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ 3 by omega)
  have hlarge : 4*b ≤ 9*b^3*N := by nlinarith [mul_le_mul_of_nonneg_left hN1 (by positivity : 0 ≤ 9*b^3)]
  have h := qmaFourTensor_polynomial_comparison (9*b^3*N) b hb hlarge V C hVs hCs hV hH hVn hCn hNn u hu
  have he : 9*b^3/(9*b^3*N) = 1/(N:ℝ) := by field_simp
  rwa [he] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorOperatorBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial norm budget for the exact calibrated effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensorEncoding_norm (n : ℕ) : ‖qmaMatrixOperator (qmaFourTensorEncoding n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  exact le_of_eq (qmaFourTensor_inclusion_norm n p)

theorem qmaFourTensor_column_operator_norm (V : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖qmaMatrixOperator (V*qmaFourTensorEncoding n)‖ ≤ ‖spinMatrixOperator V‖ := by
  rw [qmaMatrixOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (qmaFourTensorEncoding_norm n) (norm_nonneg _)).trans_eq (mul_one _))

theorem qmaFourTensor_compression_norm (C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖spinMatrixOperator ((qmaFourTensorEncoding n).conjTranspose*C*qmaFourTensorEncoding n)‖ ≤
      ‖spinMatrixOperator C‖ := by
  rw [← qmaMatrixOperator_square,qmaMatrixOperator_mul,qmaMatrixOperator_mul,qmaMatrixOperator_star]
  have hE := qmaFourTensorEncoding_norm n
  have hEs : ‖(qmaMatrixOperator (qmaFourTensorEncoding n)).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hE
  calc
    _ ≤ (‖(qmaMatrixOperator (qmaFourTensorEncoding n)).adjoint‖*‖qmaMatrixOperator C‖)*
        ‖qmaMatrixOperator (qmaFourTensorEncoding n)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*‖qmaMatrixOperator C‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hEs (norm_nonneg _)) hE (norm_nonneg _) (by positivity)
    _ = _ := by rw [one_mul,mul_one]; rfl

theorem qmaFourTensorEffectiveMatrix_norm (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤
      ‖spinMatrixOperator C‖+‖spinMatrixOperator V‖^2/8 := by
  have hgram : ‖spinMatrixOperator ((V*qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n))‖ ≤
      ‖spinMatrixOperator V‖^2 := by
    rw [← qmaMatrixOperator_square,qmaMatrixOperator_mul,qmaMatrixOperator_star,
      ContinuousLinearMap.norm_adjoint_comp_self]
    have h := qmaFourTensor_column_operator_norm V
    nlinarith [norm_nonneg (qmaMatrixOperator (V*qmaFourTensorEncoding n)),norm_nonneg (spinMatrixOperator V)]
  rw [qmaFourTensorEffectiveMatrix,spinMatrixOperator_sub]
  apply (norm_sub_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul]
  have hs : ‖(1/8:ℂ)‖ = (1/8:ℝ) := by norm_num
  rw [hs]
  have hleft := qmaFourTensor_compression_norm C
  nlinarith

theorem qmaFourTensorNormBudget_bounds (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    1 ≤ qmaFourTensorNormBudget V C ∧ ‖spinMatrixOperator V‖ ≤ qmaFourTensorNormBudget V C ∧
      ‖spinMatrixOperator C‖ ≤ qmaFourTensorNormBudget V C ∧
      ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ qmaFourTensorNormBudget V C := by
  have hv := norm_nonneg (spinMatrixOperator V)
  have hc := norm_nonneg (spinMatrixOperator C)
  have he := qmaFourTensorEffectiveMatrix_norm V C
  unfold qmaFourTensorNormBudget
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]

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

theorem qmaFourTensorFields_star (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    (qmaFourTensorFields site axis weight).conjTranspose = qmaFourTensorFields site axis weight := by
  simp only [qmaFourTensorFields,Matrix.conjTranspose_sum,qmaSiteMatrix_star,qmaFourAxisField_star]

theorem qmaFourTensorOnsite_star (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaFourTensorOnsite site axis weight constant).conjTranspose = qmaFourTensorOnsite site axis weight constant := by
  simp only [qmaFourTensorOnsite,Matrix.conjTranspose_add,qmaFourTensorFields_star,
    Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]

theorem qmaFourTensorFields_norm (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFields site axis weight)‖ ≤ 6*(∑ e, |weight e|) := by
  rw [qmaFourTensorFields,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorAxisField_norm _ _ _))

theorem qmaFourAxisFieldShift_abs (a : Fin 2) (t : ℝ) : |qmaFourAxisFieldShift a t| ≤ |t| := by
  unfold qmaFourAxisFieldShift
  split_ifs
  · simpa only [abs_zero] using abs_nonneg t
  · rw [abs_div]
    norm_num

theorem qmaFourTensorFieldShift_abs (axis : τ → Fin 2) (weight : τ → ℝ) :
    |qmaFourTensorFieldShift axis weight| ≤ ∑ e, |weight e| := by
  unfold qmaFourTensorFieldShift
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourAxisFieldShift_abs _ _))

theorem qmaFourTensorOnsite_norm (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorOnsite site axis weight constant)‖ ≤
      7*(∑ e, |weight e|)+|constant| := by
  have h1 : ‖spinMatrixOperator (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  have hs := qmaFourTensorFieldShift_abs axis weight
  have hf := qmaFourTensorFields_norm site axis weight
  rw [qmaFourTensorOnsite,spinMatrixOperator_add]
  apply (norm_add_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hscalar := mul_le_mul_of_nonneg_left h1 (abs_nonneg (constant-qmaFourTensorFieldShift axis weight))
  have habs := abs_sub constant (qmaFourTensorFieldShift axis weight)
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFourTensorFullFamily
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem qmaFourTensorFull_budget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    qmaFourTensorNormBudget (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFullCounterterm left right a b t site axis weight constant) ≤
        qmaFourTensorFullBudget t weight constant := by
  let s := ∑ e, (1+|t e|)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcoeff : (∑ e, |t e|) ≤ s := Finset.sum_le_sum (fun _ _ => by linarith)
  have hv := qmaFourTensorFamily_norm left right a b t
  have hc : ‖spinMatrixOperator (qmaFourTensorFullCounterterm left right a b t site axis weight constant)‖ ≤
      1228800*s+7*(∑ e, |weight e|)+|constant| := by
    rw [qmaFourTensorFullCounterterm,spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    have hp := (qmaFourTensorFamilyCounterterm_bound left right a b t).trans
      (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
    have hf := qmaFourTensorOnsite_norm site axis weight constant
    linarith
  have hv2 := pow_le_pow_left₀ (norm_nonneg (spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t))) hv 2
  change 1+‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖+
    ‖spinMatrixOperator (qmaFourTensorFullCounterterm left right a b t site axis weight constant)‖+
    ‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖^2 ≤
      1+7056*s+(1228800*s+7*(∑ e, |weight e|)+|constant|)+(7056*s)^2
  linarith

end ContinuumCoulomb

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

variable {τ : Type*} [Fintype τ]

theorem qmaFourTensorFull_accuracy_of_budget_oai (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant B : ℝ)
    (hbudget : qmaFourTensorFullBudget t weight constant ≤ B) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix (9*B^3*N)
        (((9*B^3*N:ℝ):ℂ) • qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFullCounterterm left right a b t site axis weight constant))-
      MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b t site axis weight constant)| ≤ 1/(N:ℝ) := by
  let V := qmaFourTensorFamilyCoupling left right a b t
  let C := qmaFourTensorFullCounterterm left right a b t site axis weight constant
  have hB := (qmaFourTensorFull_budget left right a b t site axis weight constant).trans hbudget
  have hb := qmaFourTensorNormBudget_bounds V C
  have hCs : C.conjTranspose = C := by
    simp only [C,qmaFourTensorFullCounterterm,Matrix.conjTranspose_add,qmaFourTensorFamilyCounterterm_star,
      qmaFourTensorOnsite_star]
  have h := qmaFourTensor_polynomial_accuracy B (hb.1.trans hB)
    V C (qmaFourTensorFamily_star left right a b t hneq) hCs
    (qmaFourTensorFamily_orthogonal left right a b t hneq)
    (qmaFourTensorFamily_excitation left right a b t hneq)
    (hb.2.1.trans hB) (hb.2.2.1.trans hB) (hb.2.2.2.trans hB)
    (EuclideanSpace.single (fun _ => 0) 1) (by simp [PiLp.norm_single]) N hN
  rw [show qmaFourTensorEffectiveMatrix V C = qmaFourTensorFullTarget left right a b t site axis weight constant
    from qmaFourTensorFull_effective left right a b t hneq hdist site axis weight constant] at h
  exact h

end ContinuumCoulomb

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget_oai.{u_1, u_2} := @OAI.ContinuumCoulomb.qmaFourTensorFull_accuracy_of_budget_oai.{u_1, u_2}
