-- Prove2me | solution 1 for OAI.ContinuumCoulomb.publishedCMPHardness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:01:49.316694+00:00
-- url     : https://prove2.me/submissions/b1476e83-5ebb-4485-8cde-4bf5a2ced35b

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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
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
import Mathlib.NumberTheory.Real.Irrational
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
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumFinalRoutingProgram_spatial_polynomialPromise
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumHistorySourceProgram_history_error
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumHistorySourceProgram_routed_realization
import Theorems.Thm_OAI_ContinuumCoulomb_QuantumHistorySpatial_source_data_power

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHamiltonian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

/-- Real quadratic form of the explicitly defined complete Hamiltonian. -/
theorem sourceHamiltonianForm_eq_expectation (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    sourceHamiltonianForm d u =
      (∑ s, star (u s) * sourceHamiltonian d u s).re := by
  unfold sourceHamiltonian sourceHamiltonianForm sourceHeisenbergForm
  simp only [Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  simp [Complex.mul_re, Complex.star_def]
  ring

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

/-- Matrix multiplication agrees with the swap-based Heisenberg action. -/
theorem sourceHeisenbergMatrix_mulVec (n : ℕ) (i j : Fin n) (u : SourceSpinVector n) :
    sourceHeisenbergMatrix n i j *ᵥ u = sourceHeisenbergAction i j u := by
  classical
  funext s
  simp only [sourceHeisenbergMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  simp [sourceHeisenbergAction]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_ManyBody_MediatorSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variational bottoms for the complete simultaneous-mediator spin
Hamiltonian and its effective source matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem sourceMatrixBottom_minimizer (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    ∃ p : MediatorLowSpace n, ‖p‖ = 1 ∧
      sourceMatrixBottom n M = ⟪p, spinMatrixOperator M p⟫_ℝ ∧
      ∀ q : MediatorLowSpace n, ‖q‖ = 1 →
        ⟪p, spinMatrixOperator M p⟫_ℝ ≤ ⟪q, spinMatrixOperator M q⟫_ℝ := by
  let C := (spinMatrixOperator M).restrictScalars ℝ
  let T : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let B : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let u : MediatorLowSpace n := EuclideanSpace.single (fun _ => 0) 1
  have hu : ‖u‖ = 1 := by simp [u]
  obtain ⟨p, hp, hmin⟩ := Perturbation.effectiveForm_minimizer C T B u hu
  have hform (q : MediatorLowSpace n) :
      Perturbation.effectiveForm C T B q = ⟪q, spinMatrixOperator M q⟫_ℝ := by
    simp [Perturbation.effectiveForm, Perturbation.inverseForm, C, T, B]
  have hbottom : Perturbation.effectiveBottom C T B = sourceMatrixBottom n M := by
    unfold Perturbation.effectiveBottom sourceMatrixBottom
    simp_rw [hform]
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← hbottom, Perturbation.effectiveBottom_eq C T B p hp hmin, hform]
  · intro q hq
    simpa only [hform, hq, one_pow, mul_one] using hmin q

theorem sourceMatrixForm_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ)
    (p : MediatorLowSpace n) (hp : ‖p‖ = 1) :
    ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ =
      ⟪p, spinMatrixOperator M p⟫_ℝ - k := by
  rw [spinMatrixOperator_sub, spinMatrixOperator_smul, spinMatrixOperator_one,
    _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right]
  have hscalar : ⟪p, (k : ℂ) • p⟫_ℝ = k := by
    rw [HubbardGlobal.euclidean_real_inner, inner_smul_right, inner_self_eq_norm_sq_to_K, hp]
    simp
  rw [hscalar]

theorem sourceMatrixBottom_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ) :
    sourceMatrixBottom n (M - (k : ℂ) • 1) = sourceMatrixBottom n M - k := by
  obtain ⟨p, hp, hbottom, hmin⟩ := sourceMatrixBottom_minimizer n M
  let S := {e | ∃ q : MediatorLowSpace n, ‖q‖ = 1 ∧
    e = ⟪q, spinMatrixOperator (M - (k : ℂ) • 1) q⟫_ℝ}
  have hmem : ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ ∈ S := ⟨p, hp, rfl⟩
  have hlower : ∀ e ∈ S, sourceMatrixBottom n M - k ≤ e := by
    rintro e ⟨q, hq, rfl⟩
    rw [sourceMatrixForm_shift n M k q hq, hbottom]
    exact sub_le_sub_right (hmin q hq) k
  have hbdd : BddBelow S := ⟨_, hlower⟩
  apply le_antisymm
  · exact (csInf_le hbdd hmem).trans_eq (by rw [sourceMatrixForm_shift n M k p hp, hbottom])
  · exact le_csInf ⟨_, hmem⟩ hlower

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateUnitary
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.value_sqrtHalf _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unitarity of the fixed verifier gates, needed for the
circuit-to-Hamiltonian construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qmaPhaseT_gram : qmaPhaseT.conjTranspose * qmaPhaseT = 1 := by
  have hs : (starRingEnd ℂ) bellScale = bellScale := bellScale_star
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaPhaseT,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,bellScale_star,star_mul,hs]
  ring_nf
  norm_num [bellScale_sq,hs]

theorem sourceTensor_gram (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ i, (M i).conjTranspose * M i = 1) :
    (sourceTensor n M).conjTranspose * sourceTensor n M = 1 := by
  rw [sourceTensor_conjTranspose,sourceTensor_mul]
  simp_rw [hM]
  exact sourceTensor_one n

theorem qmaControlledNot_involutive (work : ℕ) (control target : Fin (work+1))
    (hct : control ≠ target) : Function.Involutive (qmaControlledNot work control target) := by
  intro s
  have hc : qmaControlledNot work control target s control = s control := by
    simp [qmaControlledNot,hct]
  funext i
  change (if i = target ∧ qmaControlledNot work control target s control = 1 then
    Equiv.swap (0:Fin 2) 1 (qmaControlledNot work control target s i)
    else qmaControlledNot work control target s i) = s i
  rw [hc]
  by_cases hi : i = target
  · subst i
    by_cases hs : s control = 1 <;> simp [qmaControlledNot,hs]
  · simp [hi,qmaControlledNot]

theorem qmaGateMatrix_gram (work : ℕ) (g : QMAGate) (hg : g.WellFormed (work+1)) :
    (qmaGateMatrix work g).conjTranspose * qmaGateMatrix work g = 1 := by
  classical
  cases g with
  | hadamard i =>
    apply sourceTensor_gram
    intro k
    split_ifs <;> simp [qmaHadamard_gram]
  | phaseT i =>
    apply sourceTensor_gram
    intro k
    split_ifs <;> simp [qmaPhaseT_gram]
  | controlledNot i j =>
    have hij : qmaQubit work i ≠ qmaQubit work j := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1] at hval
      exact hg.2.2 hval
    have hf := qmaControlledNot_involutive work (qmaQubit work i) (qmaQubit work j) hij
    ext s t
    change (∑ b, star (if b = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) s
        then (1:ℂ) else 0) *
      (if b = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0)) =
      if s = t then 1 else 0
    simp only [apply_ite,star_one,star_zero]
    rw [Finset.sum_eq_single (qmaControlledNot work (qmaQubit work i) (qmaQubit work j) s)]
    · simp [hf.injective.eq_iff]
    · intro b _hb hbs
      simp [hbs]
    · simp

theorem qmaCircuitMatrix_gram (c : QMACircuit) (hc : c.WellFormed) :
    (qmaCircuitMatrix c).conjTranspose * qmaCircuitMatrix c = 1 := by
  have hfold (gs : List QMAGate) (hgs : ∀ g ∈ gs, g.WellFormed (c.work+1))
      (M : Matrix (SourceSpinBasis (c.work+1)) (SourceSpinBasis (c.work+1)) ℂ)
      (hM : M.conjTranspose*M = 1) :
      (gs.foldl (fun A g => qmaGateMatrix c.work g*A) M).conjTranspose *
        gs.foldl (fun A g => qmaGateMatrix c.work g*A) M = 1 := by
    induction gs generalizing M with
    | nil => exact hM
    | cons g gs ih =>
      apply ih (fun q hq => hgs q (List.mem_cons_of_mem g hq))
      rw [Matrix.conjTranspose_mul]
      calc
        M.conjTranspose*(qmaGateMatrix c.work g).conjTranspose*(qmaGateMatrix c.work g*M) =
            M.conjTranspose*((qmaGateMatrix c.work g).conjTranspose*qmaGateMatrix c.work g)*M := by
              noncomm_ring
        _ = 1 := by rw [qmaGateMatrix_gram c.work g (hgs g (List.mem_cons_self)),mul_one,hM]
  exact hfold c.gates hc.2 1 (by simp)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_ClockPathBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary quantitative propagation estimates for the finite clock.
They compare every clock slice to its initial slice. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem clock_path_anchor_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T i : ℕ) (hi : i ≤ T) :
    ‖f i-f 0‖^2 ≤ (T:ℝ)*clockPathEnergy f T := by
  have ht : ∑ j ∈ Finset.range i, (f (j+1)-f j) = f i-f 0 := by
    exact Finset.sum_range_sub f i
  have hn : ‖f i-f 0‖ ≤ ∑ j ∈ Finset.range i, ‖f (j+1)-f j‖ := by
    rw [←ht]
    exact norm_sum_le _ _
  have hsq : ‖f i-f 0‖^2 ≤ (∑ j ∈ Finset.range i, ‖f (j+1)-f j‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range i) (f := fun j => ‖f (j+1)-f j‖)
  have he : (∑ j ∈ Finset.range i, ‖f (j+1)-f j‖^2) ≤ clockPathEnergy f T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
    intro _ _ _
    positivity
  apply (hsq.trans hc).trans
  simp only [Finset.card_range]
  exact mul_le_mul (by exact_mod_cast hi) he (by positivity) (Nat.cast_nonneg T)

end ContinuumCoulomb

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

theorem norm_add_sq_four {E : Type*} [NormedAddCommGroup E] (a b : E) :
    4*‖a+b‖^2 ≤ 5*‖a‖^2+20*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-4*‖b‖)]

theorem norm_add_sq_three {E : Type*} [NormedAddCommGroup E] (a b : E) :
    3*‖a+b‖^2 ≤ 4*‖a‖^2+12*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-3*‖b‖)]

theorem clock_path_weighted_mass_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (T : ℕ) :
    4*(∑ i ∈ Finset.range (T+1), ‖f i‖^2) ≤
      5*(T+1:ℝ)*‖f 0‖^2+20*T*(T+1:ℝ)*clockPathEnergy f T := by
  have hb (i : ℕ) (hi : i ∈ Finset.range (T+1)) :
      4*‖f i‖^2 ≤ 5*‖f 0‖^2+20*(T:ℝ)*clockPathEnergy f T := by
    have ha := clock_path_anchor_bound f T i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have h := norm_add_sq_four (f 0) (f i-f 0)
    have he : f 0+(f i-f 0) = f i := by abel
    rw [he] at h
    linarith
  calc
    4*(∑ i ∈ Finset.range (T+1), ‖f i‖^2) =
        ∑ i ∈ Finset.range (T+1), 4*‖f i‖^2 := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (T+1),
        (5*‖f 0‖^2+20*(T:ℝ)*clockPathEnergy f T) := Finset.sum_le_sum hb
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      push_cast
      ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEvolution
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm preservation for the actual verifier evolution. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qma_matrix_mass_preserved {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (hM : M.conjTranspose*M = 1) (u : SourceSpinVector n) :
    sourceSpinMass (M.mulVec u) = sourceSpinMass u := by
  have hinner : star (M.mulVec u) ⬝ᵥ M.mulVec u = star u ⬝ᵥ u := by
    rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,hM,Matrix.one_mulVec]
  have hreal := congrArg Complex.re hinner
  have hre (z : ℂ) : (star z*z).re = Complex.normSq z := by
    simp [Complex.mul_re,Complex.normSq_apply]
  simpa only [dotProduct,Pi.star_apply,Complex.re_sum,hre,sourceSpinMass] using hreal

theorem qmaApplyMatrix_norm {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (hM : M.conjTranspose*M = 1) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaApplyMatrix M u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simpa only [qmaApplyMatrix,PiLp.toLp_apply,Complex.sq_norm,sourceSpinMass] using
    qma_matrix_mass_preserved M hM (fun s => u s)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPrefix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact circuit prefixes and their unitary changes of coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

theorem qmaApplyMatrix_mul {n : ℕ}
    (M N : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix (M*N) u = qmaApplyMatrix M (qmaApplyMatrix N u) := by
  ext s
  simp [qmaApplyMatrix,Matrix.mulVec_mulVec]

theorem qmaApplyMatrix_sub {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u w : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix M (u-w) = qmaApplyMatrix M u-qmaApplyMatrix M w := by
  ext s
  change (M.mulVec ((fun s => u s)-(fun s => w s))) s = _
  rw [Matrix.mulVec_sub]
  rfl

theorem qmaPrefixMatrix_gram (c : QMACircuit) (hc : c.WellFormed) (t : ℕ) :
    (qmaPrefixMatrix c t).conjTranspose*qmaPrefixMatrix c t = 1 := by
  let d : QMACircuit := { c with gates := c.gates.take t }
  have hd : d.WellFormed := ⟨hc.1,fun g hg => hc.2 g (List.mem_of_mem_take hg)⟩
  exact qmaCircuitMatrix_gram d hd

theorem qmaPrefixMatrix_cogram (c : QMACircuit) (hc : c.WellFormed) (t : ℕ) :
    qmaPrefixMatrix c t*(qmaPrefixMatrix c t).conjTranspose = 1 :=
  mul_eq_one_comm.mp (qmaPrefixMatrix_gram c hc t)

theorem qmaPrefixMatrix_succ (c : QMACircuit) (t : ℕ) (ht : t < c.gates.length) :
    qmaPrefixMatrix c (t+1) = qmaStepMatrix c t*qmaPrefixMatrix c t := by
  unfold qmaPrefixMatrix qmaStepMatrix
  rw [←List.take_concat_get' c.gates t ht,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [List.getD_eq_get c.gates (.hadamard 0) ⟨t,ht⟩]
  rfl

theorem qmaStepMatrix_gram (c : QMACircuit) (hc : c.WellFormed)
    (t : ℕ) (ht : t < c.gates.length) :
    (qmaStepMatrix c t).conjTranspose*qmaStepMatrix c t = 1 := by
  apply qmaGateMatrix_gram
  rw [List.getD_eq_get c.gates (.hadamard 0) ⟨t,ht⟩]
  exact hc.2 _ (List.get_mem _ _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative propagation for the actual H,T,CNOT circuit history. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open Matrix

theorem qmaHistoryGauge_norm (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ) :
    ‖qmaHistoryGauge c u t‖ = ‖u t‖ := by
  apply qmaApplyMatrix_norm
  simpa only [Matrix.conjTranspose_conjTranspose] using qmaPrefixMatrix_cogram c hc t

theorem qmaHistoryGauge_step (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1)))
    (t : ℕ) (ht : t < c.gates.length) :
    qmaHistoryGauge c u (t+1)-qmaHistoryGauge c u t =
      qmaApplyMatrix (qmaPrefixMatrix c (t+1)).conjTranspose
        (u (t+1)-qmaApplyMatrix (qmaStepMatrix c t) (u t)) := by
  have hp : (qmaPrefixMatrix c (t+1)).conjTranspose*qmaStepMatrix c t =
      (qmaPrefixMatrix c t).conjTranspose := by
    rw [qmaPrefixMatrix_succ c t ht,Matrix.conjTranspose_mul,mul_assoc,
      qmaStepMatrix_gram c hc t ht,mul_one]
  rw [qmaApplyMatrix_sub,←qmaApplyMatrix_mul,hp]
  rfl

theorem qmaHistoryGauge_energy (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    clockPathEnergy (qmaHistoryGauge c u) c.gates.length = qmaPropagationEnergy c u := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [qmaHistoryGauge_step c hc u t (Finset.mem_range.mp ht),qmaApplyMatrix_norm]
  simpa only [Matrix.conjTranspose_conjTranspose] using qmaPrefixMatrix_cogram c hc (t+1)

theorem qma_history_anchor_bound (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ)
    (ht : t ≤ c.gates.length) :
    ‖u t-qmaApplyMatrix (qmaPrefixMatrix c t) (u 0)‖^2 ≤
      (c.gates.length:ℝ)*qmaPropagationEnergy c u := by
  have heq : qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaHistoryGauge c u t-qmaHistoryGauge c u 0) =
      u t-qmaApplyMatrix (qmaPrefixMatrix c t) (u 0) := by
    rw [qmaApplyMatrix_sub]
    change qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaApplyMatrix (qmaPrefixMatrix c t).conjTranspose (u t)) -
      qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaApplyMatrix (qmaPrefixMatrix c 0).conjTranspose (u 0)) = _
    rw [←qmaApplyMatrix_mul,qmaPrefixMatrix_cogram c hc t]
    simp
  have h := clock_path_anchor_bound (qmaHistoryGauge c u) c.gates.length t ht
  rw [qmaHistoryGauge_energy c hc u] at h
  rw [←heq,qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc t)]
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncilla
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact witness embedding into the zero-ancilla subspace. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaInitialState_mass (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    sourceSpinMass (qmaInitialState c hc psi) = ‖psi‖^2 := by
  classical
  have he := (qmaZeroAncillaEquiv c hc).sum_comp (fun s => Complex.normSq (psi s))
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rw [←he]
  have hp (s : SourceSpinBasis (c.work+1)) :
      Complex.normSq (qmaInitialState c hc psi s) = if QMAAncillaZero c s then
        Complex.normSq (psi (qmaWitnessRestrict c hc s)) else 0 := by
    by_cases hs : QMAAncillaZero c s
    · have hs' : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
      simp only [qmaInitialState,ite_eq_left hs',ite_eq_left hs]
      rfl
    · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_right hs,Complex.normSq_zero]
  unfold sourceSpinMass
  simp_rw [hp]
  have hsub := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (QMAAncillaZero c))
    (by simp : ∀ s, s ∈ Finset.univ.filter (QMAAncillaZero c) ↔ QMAAncillaZero c s)
    (fun s => Complex.normSq (psi (qmaWitnessRestrict c hc s)))
  rw [Finset.sum_filter] at hsub
  exact hsub

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMask
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate projections for the initial and output penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaMask_norm_le {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) : ‖qmaMask p u‖ ≤ ‖u‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : p s <;> simp [qmaMask_apply,hs]

theorem qmaMask_complement_square {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u‖^2+‖qmaMask (fun s => ¬p s) u‖^2 = ‖u‖^2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : p s <;> simp [hs]

theorem qmaMask_sub_norm_le {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u v : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u-qmaMask p v‖ ≤ ‖u-v‖ := by
  rw [←map_sub]
  exact qmaMask_norm_le p (u-v)

theorem qmaMask_sub_self {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    u-qmaMask p u = qmaMask (fun s => ¬p s) u := by
  ext s
  by_cases hs : p s <;> simp [hs]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpoint
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The verifier acceptance probability is the exact endpoint projection
energy of its normalized zero-ancilla evolution. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaInputVector_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaInputVector c hc psi‖ = ‖psi‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [qmaInputVector,PiLp.toLp_apply,Complex.sq_norm,sourceSpinMass] using
    qmaInitialState_mass c hc psi

theorem qmaOutputVector_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaOutputVector c hc psi‖ = ‖psi‖ := by
  rw [qmaOutputVector,qmaApplyMatrix_norm _ (qmaCircuitMatrix_gram c hc),qmaInputVector_norm]

theorem qmaAcceptance_projection (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance c hc psi =
      ‖qmaMask (fun s => s (Fin.last c.work) = 1) (qmaOutputVector c hc psi)‖^2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s (Fin.last c.work) = 1 <;>
    simp [qmaMask_apply,hs,qmaOutputVector,qmaApplyMatrix,qmaInputVector,Complex.sq_norm]

theorem qmaRejectVector_square (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaRejectVector c hc psi‖^2 = ‖psi‖^2-qmaAcceptance c hc psi := by
  have h := qmaMask_complement_square (fun s => s (Fin.last c.work) = 1)
    (qmaOutputVector c hc psi)
  rw [←qmaAcceptance_projection,qmaOutputVector_norm] at h
  change qmaAcceptance c hc psi+‖qmaRejectVector c hc psi‖^2 = ‖psi‖^2 at h
  linarith

theorem qmaRejectVector_of_accept (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) : ‖qmaRejectVector c hc psi‖^2 ≤ 1/3 := by
  rw [qmaRejectVector_square,hpsi]
  linarith

theorem qmaRejectVector_of_sound (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : qmaAcceptance c hc psi ≤ 1/3) : 2/3 ≤ ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaRejectVector_square,hpsi]
  linarith

theorem qmaApplyMatrix_smul {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (a : ℂ) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix M (a • u) = a • qmaApplyMatrix M u := by
  ext s
  change (M.mulVec (a • (fun s => u s))) s = (a • M.mulVec (fun s => u s)) s
  rw [Matrix.mulVec_smul]

theorem qmaInputVector_smul (c : QMACircuit) (hc : c.WellFormed)
    (a : ℂ) (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaInputVector c hc (a • psi) = a • qmaInputVector c hc psi := by
  classical
  ext s
  by_cases hs : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0
  · simp [qmaInputVector,qmaInitialState]
  · simp [qmaInputVector,qmaInitialState,hs]

theorem qmaRejectVector_smul (c : QMACircuit) (hc : c.WellFormed)
    (a : ℂ) (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaRejectVector c hc (a • psi) = a • qmaRejectVector c hc psi := by
  rw [qmaRejectVector,qmaOutputVector,qmaInputVector_smul,qmaApplyMatrix_smul,map_smul]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSoundness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneous soundness for arbitrary, unnormalized witnesses. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaRejectVector_sound_all (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    (2/3:ℝ)*‖psi‖^2 ≤ ‖qmaRejectVector c hc psi‖^2 := by
  by_cases hz : psi = 0
  · subst psi
    simp
  have hn : ‖psi‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let phi := ((‖psi‖⁻¹ : ℝ) : ℂ) • psi
  have hphi : ‖phi‖ = 1 := by
    simp [phi,norm_smul,hn]
  have hscale : psi = (‖psi‖ : ℂ) • phi := by
    change psi = (‖psi‖ : ℝ) • (‖psi‖⁻¹ • psi)
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hb := qmaRejectVector_of_sound c hc phi hphi (hsound phi hphi)
  have he : ‖qmaRejectVector c hc psi‖^2 =
      ‖psi‖^2*‖qmaRejectVector c hc phi‖^2 := by
    conv_lhs => rw [hscale]
    rw [qmaRejectVector_smul]
    simp [norm_smul,mul_pow]
  rw [he]
  nlinarith [sq_nonneg ‖psi‖]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumInputProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The legal initial subspace is exactly the zero-ancilla witness embedding. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaInputVector_extract (c : QMACircuit) (hc : c.WellFormed)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputVector c hc (qmaExtractWitness c u) = qmaMask (QMAAncillaZero c) u := by
  classical
  ext s
  by_cases hs : QMAAncillaZero c s
  · have hs' : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
    simp only [qmaInputVector,qmaInitialState,PiLp.toLp_apply,ite_eq_left hs',
      qmaExtractWitness,qmaMask_apply,ite_eq_left hs]
    change u (qmaWitnessExtend c (qmaWitnessRestrict c hc s)) = u s
    rw [qmaWitnessExtend_restrict c hc s hs]
  · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
    simp only [qmaInputVector,qmaInitialState,PiLp.toLp_apply,ite_eq_right hs',
      qmaMask_apply,ite_eq_right hs]

theorem qmaExtractWitness_norm (c : QMACircuit) (hc : c.WellFormed)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaExtractWitness c u‖ = ‖qmaMask (QMAAncillaZero c) u‖ := by
  rw [←qmaInputVector_extract c hc u,qmaInputVector_norm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryEnergy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative circuit-history promise gap, for all history vectors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qma_history_legal_endpoint_bound (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c)
      (qmaMask (QMAAncillaZero c) (u 0))‖^2 ≤
      2*c.gates.length*qmaPropagationEnergy c u+2*qmaInputPenalty c u := by
  let v := qmaMask (QMAAncillaZero c) (u 0)
  have ha := qma_history_anchor_bound c hc u c.gates.length le_rfl
  rw [qmaPrefixMatrix_length] at ha
  have hb : ‖qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v)‖^2 = qmaInputPenalty c u := by
    rw [qmaApplyMatrix_norm _ (qmaCircuitMatrix_gram c hc)]
    dsimp [v]
    rw [qmaMask_sub_self]
    rfl
  have he : (u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) (u 0))+
      qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v) =
      u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) v := by
    rw [qmaApplyMatrix_sub]
    abel
  have h := norm_add_sq_two
    (u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) (u 0))
    (qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v))
  rw [he,hb] at h
  exact h.trans (by linarith)

theorem qma_history_output_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaMask (QMAAncillaZero c) (u 0)‖^2 ≤
      2*qmaOutputPenalty c u+12*c.gates.length*qmaPropagationEnergy c u+
        12*qmaInputPenalty c u := by
  let p := fun s : SourceSpinBasis (c.work+1) => s (Fin.last c.work) ≠ 1
  let v := qmaMask (QMAAncillaZero c) (u 0)
  let w := qmaApplyMatrix (qmaCircuitMatrix c) v
  have hs := qmaRejectVector_sound_all c hc hsound (qmaExtractWitness c (u 0))
  rw [qmaExtractWitness_norm c hc] at hs
  have hr : qmaRejectVector c hc (qmaExtractWitness c (u 0)) = qmaMask p w := by
    rw [qmaRejectVector,qmaOutputVector,qmaInputVector_extract]
  rw [hr] at hs
  have hd : ‖qmaMask p w-qmaMask p (u c.gates.length)‖^2 ≤
      2*c.gates.length*qmaPropagationEnergy c u+2*qmaInputPenalty c u := by
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (qmaMask_sub_norm_le p w (u c.gates.length)) 2
    rw [norm_sub_rev w] at h
    exact h.trans (qma_history_legal_endpoint_bound c hc u)
  have ht := norm_add_sq_three (qmaMask p (u c.gates.length))
    (qmaMask p w-qmaMask p (u c.gates.length))
  have he : qmaMask p (u c.gates.length)+
      (qmaMask p w-qmaMask p (u c.gates.length)) = qmaMask p w := by abel
  rw [he] at ht
  change 3*‖qmaMask p w‖^2 ≤ 4*qmaOutputPenalty c u+
    12*‖qmaMask p w-qmaMask p (u c.gates.length)‖^2 at ht
  nlinarith

theorem qma_history_energy_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaHistoryEnergy c u := by
  have hm := clock_path_weighted_mass_bound (qmaHistoryGauge c u) c.gates.length
  simp only [qmaHistoryGauge_norm c hc u,qmaHistoryGauge_energy c hc u] at hm
  change 4*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*‖u 0‖^2+
    20*c.gates.length*(c.gates.length+1:ℝ)*qmaPropagationEnergy c u at hm
  have hsplit := qmaMask_complement_square (QMAAncillaZero c) (u 0)
  change ‖qmaMask (QMAAncillaZero c) (u 0)‖^2+qmaInputPenalty c u = ‖u 0‖^2 at hsplit
  have hout := qma_history_output_sound c hc hsound u
  have hx := mul_le_mul_of_nonneg_left hout
    (by positivity : 0 ≤ 5*(c.gates.length+1:ℝ))
  have hi : 0 ≤ (c.gates.length+1:ℝ)*qmaInputPenalty c u := by
    unfold qmaInputPenalty
    positivity
  unfold qmaHistoryEnergy
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryWitness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaClockIndex_fin _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit accepting histories and their exact mass and energy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaIdealHistory_mass (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaHistoryMass c (qmaIdealHistory c hc psi) = (c.gates.length+1:ℝ)*‖psi‖^2 := by
  simp [qmaHistoryMass,qmaIdealHistory,
    qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc _),qmaInputVector_norm]

theorem qmaIdealHistory_propagation (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaPropagationEnergy c (qmaIdealHistory c hc psi) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  simp only [qmaIdealHistory,qmaPrefixMatrix_succ c t (Finset.mem_range.mp ht),
    qmaApplyMatrix_mul,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]

end ContinuumCoulomb

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

theorem qmaQuadratic_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (D.conjTranspose*D) u = ∑ r, Complex.normSq (D.mulVec u r) := by
  have he : star u ⬝ᵥ (D.conjTranspose*D).mulVec u =
      star (D.mulVec u) ⬝ᵥ D.mulVec u := by
    rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec]
  rw [qmaQuadratic,he]
  simp only [dotProduct,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp [Complex.mul_re,Complex.normSq_apply]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFiniteHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite clock coordinates and their exact Euclidean mass. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaHistoryFromVector_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaHistoryMass c (qmaHistoryFromVector c u) = ‖WithLp.toLp 2 u‖^2 := by
  unfold qmaHistoryMass
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [EuclideanSpace.norm_sq_eq,qmaHistoryFromVector_fin]
  rw [Fintype.sum_prod_type]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryMatrixForm
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite matrix is exactly the quadratic history form. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaPropagationMatrix_mulVec (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.work+1)) :
    (qmaPropagationMatrix c).mulVec u (t,s) =
      (qmaHistoryFromVector c u (t.val+1)-qmaApplyMatrix (qmaStepMatrix c t.val)
        (qmaHistoryFromVector c u t.val)) s := by
  rw [qmaPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simp [qmaPropagationMap,qmaHistoryFromVector,qmaClockIndex,qmaApplyMatrix,
]

theorem qmaPropagationMatrix_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic ((qmaPropagationMatrix c).conjTranspose*qmaPropagationMatrix c) u =
      qmaPropagationEnergy c (qmaHistoryFromVector c u) := by
  rw [qmaQuadratic_gram]
  unfold qmaPropagationEnergy
  rw [←Fin.sum_univ_eq_sum_range,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qmaPropagationMatrix_mulVec,Complex.sq_norm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized finite-dimensional spectral bounds for the history matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qmaHistoryVector_slice (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1)))
    (t : ℕ) (ht : t ≤ c.gates.length) :
    qmaHistoryFromVector c (fun p => qmaHistoryVector c u p) t = u t := by
  ext s
  simp [qmaHistoryFromVector,qmaClockIndex,qmaHistoryVector,Nat.min_eq_left ht]

theorem qmaHistoryVector_norm (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaHistoryVector c u‖^2 = qmaHistoryMass c u := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold qmaHistoryMass
  rw [←Fin.sum_univ_eq_sum_range,Fintype.sum_prod_type]
  simp [qmaHistoryVector,EuclideanSpace.norm_sq_eq]

theorem qmaHistoryVector_propagation (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaPropagationEnergy c (qmaHistoryFromVector c (fun p => qmaHistoryVector c u p)) =
      qmaPropagationEnergy c u := by
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [qmaHistoryVector_slice c u t (Nat.le_of_lt ht'),
    qmaHistoryVector_slice c u (t+1) (Nat.succ_le_of_lt ht')]

theorem qmaQuadratic_vector_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a : ℝ) (u : ι → ℂ) :
    qmaQuadratic M ((a:ℂ) • u) = a^2*qmaQuadratic M u := by
  simp [qmaQuadratic,Matrix.mulVec_smul,star_smul,dotProduct_smul,smul_dotProduct,
    Complex.mul_re,pow_two]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAncillaCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the joint ancilla penalty by a sum of individual qubit penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaAncillaCount_nonneg (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) :
    0 ≤ qmaAncillaCount c s := by
  unfold qmaAncillaCount
  positivity

theorem qmaAncillaCount_one_le (c : QMACircuit) (s : SourceSpinBasis (c.work+1))
    (hs : ¬QMAAncillaZero c s) : 1 ≤ qmaAncillaCount c s := by
  obtain ⟨i,hi,hne⟩ : ∃ i : Fin (c.work+1), c.witness ≤ i.val ∧ s i ≠ 0 := by
    by_contra hn
    apply hs
    intro i hi
    by_contra hne
    exact hn ⟨i,hi,hne⟩
  have h := Finset.single_le_sum
    (f := fun j : Fin (c.work+1) => if c.witness ≤ j.val ∧ s j ≠ 0 then (1:ℝ) else 0)
    (s := Finset.univ) (a := i) (by intro j _; positivity) (Finset.mem_univ _)
  simpa only [qmaAncillaCount,ite_eq_left (show c.witness ≤ i.val ∧ s i ≠ 0 from ⟨hi,hne⟩)] using h

theorem qmaAncillaCount_dominates (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) :
    (if QMAAncillaZero c s then (0:ℝ) else 1) ≤ qmaAncillaCount c s := by
  by_cases hs : QMAAncillaZero c s
  · simpa only [ite_eq_left hs] using qmaAncillaCount_nonneg c s
  · simpa only [ite_eq_right hs] using qmaAncillaCount_one_le c s hs

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The history input energy as a sum of individual ancilla projectors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_diagonal_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (u : ι → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun i => (d i : ℂ))) u =
      ∑ i, d i*Complex.normSq (u i) := by
  simp only [qmaQuadratic,dotProduct,Matrix.mulVec_diagonal,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re,Complex.normSq_apply]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryPenalty
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjacent 01 penalties separate all invalid unary clock states. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaClockFaultCount_nonneg (N : ℕ) (s : SourceSpinBasis N) :
    0 ≤ qmaClockFaultCount N s := by
  cases N with
  | zero => rfl
  | succ n => unfold qmaClockFaultCount; positivity

theorem qmaClockFaultCount_zero (N : ℕ) (s : SourceSpinBasis N) (hs : Antitone s) :
    qmaClockFaultCount N s = 0 := by
  cases N with
  | zero => rfl
  | succ n =>
    apply Finset.sum_eq_zero
    intro i _
    have hi := hs (Fin.castSucc_lt_succ (i := i)).le
    have hn : ¬(s i.castSucc = 0 ∧ s i.succ = 1) := by
      rintro ⟨hl,hr⟩
      rw [hl,hr] at hi
      norm_num at hi
    simp [hn]

theorem qmaClockFaultCount_one_le (N : ℕ) (s : SourceSpinBasis N) (hs : ¬Antitone s) :
    1 ≤ qmaClockFaultCount N s := by
  cases N with
  | zero =>
    exfalso
    apply hs
    intro i
    exact Fin.elim0 i
  | succ n =>
    have hn : ¬∀ i : Fin n, s i.succ ≤ s i.castSucc :=
      fun h => hs (Fin.antitone_iff_succ_le.mpr h)
    obtain ⟨i,hi⟩ := not_forall.mp hn
    have hv : s i.castSucc = 0 ∧ s i.succ = 1 := by
      constructor <;> apply Fin.ext
      all_goals
        have hleft := (s i.castSucc).isLt
        have hright := (s i.succ).isLt
        simp only [Fin.le_def] at hi
        simp only [Fin.val_zero,Fin.val_one]
        omega
    have h := Finset.single_le_sum
      (f := fun j : Fin n => if s j.castSucc = 0 ∧ s j.succ = 1 then (1:ℝ) else 0)
      (s := Finset.univ) (a := i) (by intro j _; positivity) (Finset.mem_univ _)
    simpa only [qmaClockFaultCount,ite_eq_left hv] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPinnedClock
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two fixed end bits make all clock transitions uniform, including the
empty circuit. Only adjacent-pair and endpoint penalties are used. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPinnedClockPenalty_nonneg (T : ℕ) (s : SourceSpinBasis (T+2)) :
    0 ≤ qmaPinnedClockPenalty T s := by
  unfold qmaPinnedClockPenalty
  have h := qmaClockFaultCount_nonneg (T+2) s
  positivity

theorem qmaPinnedClockPenalty_zero (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) : qmaPinnedClockPenalty T s = 0 := by
  simp [qmaPinnedClockPenalty,qmaClockFaultCount_zero _ _ hs.1,hs.2.1,hs.2.2]

theorem qmaPinnedClockPenalty_one_le (T : ℕ) (s : SourceSpinBasis (T+2))
    (hs : ¬QMALegalClock T s) : 1 ≤ qmaPinnedClockPenalty T s := by
  have hn := qmaClockFaultCount_nonneg (T+2) s
  by_cases ha : Antitone s
  · by_cases hl : s 0 = 1
    · have hr : s (Fin.last (T+1)) ≠ 0 := fun h => hs ⟨ha,hl,h⟩
      simp only [qmaPinnedClockPenalty,ite_eq_left hl,ite_eq_right hr,add_zero]
      linarith
    · unfold qmaPinnedClockPenalty
      rw [ite_eq_right hl]
      split <;> linarith
  · have h := qmaClockFaultCount_one_le (T+2) s ha
    unfold qmaPinnedClockPenalty
    split <;> split <;> linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockTransition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A guarded single-bit clock update preserves the legal clock sector.
The guard inspects only the two adjacent clock bits. -/

noncomputable section
namespace ContinuumCoulomb

theorem qmaClockLeft_ne_middle (T : ℕ) (i : Fin T) :
    qmaClockLeft T i ≠ qmaClockMiddle T i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [qmaClockLeft,qmaClockMiddle] at hv
  omega

theorem qmaClockRight_ne_middle (T : ℕ) (i : Fin T) :
    qmaClockRight T i ≠ qmaClockMiddle T i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [qmaClockRight,qmaClockMiddle] at hv
  omega

theorem qmaClockGuard_update (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2)) (a : Fin 2) :
    QMAClockGuard T i (Function.update s (qmaClockMiddle T i) a) ↔ QMAClockGuard T i s := by
  simp only [QMAClockGuard,Function.update_of_ne (qmaClockLeft_ne_middle T i),
    Function.update_of_ne (qmaClockRight_ne_middle T i)]

theorem qmaClock_update_antitone (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hs : Antitone s) (hg : QMAClockGuard T i s) (a : Fin 2) :
    Antitone (Function.update s (qmaClockMiddle T i) a) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro j
  by_cases hl : j.castSucc = qmaClockMiddle T i
  · have hr : j.succ = qmaClockRight T i := by
      apply Fin.ext
      have hv := congrArg Fin.val hl
      dsimp [qmaClockMiddle] at hv
      change j.val+1 = i.val+2
      omega
    rw [hl,hr,Function.update_self,Function.update_of_ne (qmaClockRight_ne_middle T i),hg.2]
    exact Fin.zero_le a
  · by_cases hr : j.succ = qmaClockMiddle T i
    · have hleft : j.castSucc = qmaClockLeft T i := by
        apply Fin.ext
        have hv := congrArg Fin.val hr
        dsimp [qmaClockMiddle] at hv
        change j.val = i.val
        omega
      rw [hr,hleft,Function.update_self,Function.update_of_ne (qmaClockLeft_ne_middle T i),hg.1]
      change a.val ≤ 1
      have ha := a.isLt
      omega
    · rw [Function.update_of_ne hl,Function.update_of_ne hr]
      exact hs (Fin.castSucc_lt_succ (i := j)).le

theorem qmaClock_update_legal (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hs : QMALegalClock T s) (hg : QMAClockGuard T i s) (a : Fin 2) :
    QMALegalClock T (Function.update s (qmaClockMiddle T i) a) := by
  refine ⟨qmaClock_update_antitone T i s hs.1 hg a,?_,?_⟩
  · have hn : (0 : Fin (T+2)) ≠ qmaClockMiddle T i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [qmaClockMiddle] at hv
      omega
    rw [Function.update_of_ne hn]
    exact hs.2.1
  · have hn : Fin.last (T+1) ≠ qmaClockMiddle T i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [qmaClockMiddle] at hv
      have hi := i.isLt
      omega
    rw [Function.update_of_ne hn]
    exact hs.2.2

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockStep
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each active guarded clock pair is either entirely legal or entirely
illegal; its legal pair is the intended consecutive history pair. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaClock_step_guard (T : ℕ) (i : Fin T) :
    QMAClockGuard T i (qmaHistoryClock T i.castSucc) := by
  constructor
  · simp [qmaHistoryClock,qmaUnaryClock,qmaClockLeft]
  · simp [qmaHistoryClock,qmaUnaryClock,qmaClockRight]

theorem qmaClock_step_zero (T : ℕ) (i : Fin T) :
    qmaHistoryClock T i.castSucc (qmaClockMiddle T i) = 0 := by
  simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle]

theorem qmaClock_step_update (T : ℕ) (i : Fin T) :
    Function.update (qmaHistoryClock T i.castSucc) (qmaClockMiddle T i) 1 =
      qmaHistoryClock T i.succ := by
  funext j
  by_cases hj : j = qmaClockMiddle T i
  · subst j
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle]
  · rw [Function.update_of_ne hj]
    have hn : j.val ≠ i.val+1 := fun h => hj (Fin.ext h)
    have he : j.val < i.val+1 ↔ j.val < i.val+1+1 := by omega
    simp only [qmaHistoryClock,qmaUnaryClock,Fin.val_castSucc,Fin.val_succ,he]

theorem qmaClock_step_legal_iff (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hg : QMAClockGuard T i s) (hz : s (qmaClockMiddle T i) = 0) :
    QMALegalClock T (Function.update s (qmaClockMiddle T i) 1) ↔ QMALegalClock T s := by
  constructor
  · intro hs
    have hg' : QMAClockGuard T i (Function.update s (qmaClockMiddle T i) 1) :=
      (qmaClockGuard_update T i s 1).mpr hg
    have h := qmaClock_update_legal T i _ hs hg' 0
    rw [Function.update_idem,←hz,Function.update_eq_self] at h
    exact h
  · intro hs
    exact qmaClock_update_legal T i s hs hg 1

theorem qmaClock_step_legal_before (T : ℕ) (i : Fin T) (s : SourceSpinBasis (T+2))
    (hg : QMAClockGuard T i s) (hz : s (qmaClockMiddle T i) = 0)
    (hs : QMALegalClock T s) : qmaHistoryClock T i.castSucc = s := by
  obtain ⟨t,ht⟩ := qmaHistoryClock_of_legal T s hs
  have hl : i.val < t.val+1 := by
    by_contra hn
    have h := hg.1
    rw [←ht] at h
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockLeft,hn] at h
  have hm : ¬i.val+1 < t.val+1 := by
    intro hn
    rw [←ht] at hz
    simp [qmaHistoryClock,qmaUnaryClock,qmaClockMiddle,hn] at hz
  have he : t = i.castSucc := by
    apply Fin.ext
    simp only [Fin.val_castSucc]
    omega
  simpa only [he] using ht

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumClockSector
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The valid clock sector is exactly the finite circuit clock, with its
full complement retained in the norm decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaClock_sector_sum (T : ℕ) (f : SourceSpinBasis (T+2) → ℝ) :
    (∑ s, f s) = (∑ t : Fin (T+1), f (qmaHistoryClock T t))+
      ∑ s, if QMALegalClock T s then 0 else f s := by
  have he := (qmaHistoryClockEquiv T).sum_comp (fun s => f s.val)
  have hs := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (QMALegalClock T))
    (by simp : ∀ s, s ∈ Finset.univ.filter (QMALegalClock T) ↔ QMALegalClock T s) f
  rw [Finset.sum_filter] at hs
  have hsplit : (∑ s, f s) =
      (∑ s, if QMALegalClock T s then f s else 0)+
      ∑ s, if QMALegalClock T s then 0 else f s := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : QMALegalClock T s <;> simp [h]
  rw [hsplit,hs,←he]
  rfl

theorem qmaClock_invalid_mass_bound (T : ℕ) (f : SourceSpinBasis (T+2) → ℝ)
    (hf : ∀ s, 0 ≤ f s) :
    (∑ s, if QMALegalClock T s then 0 else f s) ≤
      ∑ s, qmaPinnedClockPenalty T s*f s := by
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : QMALegalClock T s
  · simp only [ite_eq_left hs]
    exact mul_nonneg (qmaPinnedClockPenalty_nonneg T s) (hf s)
  · simp only [ite_eq_right hs]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (qmaPinnedClockPenalty_one_le T s hs) (hf s)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full unary-clock form retains every clock configuration. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaUnaryMass_split (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaUnaryMass c u =
      (∑ p : QMAHistoryBasis c, Complex.normSq (qmaUnaryRestrict c u p))+
      qmaUnaryInvalidMass c u := by
  unfold qmaUnaryMass qmaUnaryInvalidMass qmaUnaryRestrict
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  exact qmaClock_sector_sum c.gates.length (fun s => ∑ a, Complex.normSq (u (s,a)))

theorem qmaUnaryInvalidMass_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaUnaryInvalidMass c u ≤ qmaUnaryClockEnergy c u := by
  apply qmaClock_invalid_mass_bound
  intro s
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg (u (s,a)))

theorem qmaUnaryResidual_valid (c : QMACircuit) (u : QMAUnaryBasis c → ℂ)
    (t : Fin c.gates.length) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryResidual c u t (qmaHistoryClock c.gates.length t.castSucc) a =
      (qmaPropagationMatrix c).mulVec (qmaUnaryRestrict c u) (t,a) := by
  rw [qmaPropagationMatrix,LinearMap.toMatrix'_mulVec]
  unfold qmaUnaryResidual
  rw [qmaClock_step_update]
  rfl

theorem qmaUnaryPropagationEnergy_valid_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaPropagationEnergy c (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤
      qmaUnaryPropagationEnergy c u := by
  rw [←qmaPropagationMatrix_energy,qmaQuadratic_gram,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro t _
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0 then
        ∑ a, Complex.normSq (qmaUnaryResidual c u t s a) else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length t.castSucc)
    (by intro s _; split
        · exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
        · exact le_rfl) (Finset.mem_univ _)
  have hg : QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
      qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 :=
    ⟨qmaClock_step_guard c.gates.length t,qmaClock_step_zero c.gates.length t⟩
  simpa only [ite_eq_left hg,qmaUnaryResidual_valid] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEnergy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local endpoint penalties dominate the finite history penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaOutputPenalty_sum (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaOutputPenalty c (qmaHistoryFromVector c u) =
      ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
        Complex.normSq (u (Fin.last c.gates.length,a)) else 0 := by
  unfold qmaOutputPenalty
  have hslice : qmaHistoryFromVector c u c.gates.length =
      WithLp.toLp 2 (fun a => u (Fin.last c.gates.length,a)) := by
    ext a
    exact qmaHistoryFromVector_fin c u (Fin.last c.gates.length) a
  rw [hslice,EuclideanSpace.norm_sq_eq]
  simp [qmaMask_apply,apply_ite,Complex.sq_norm]

theorem qmaUnaryOutputEnergy_valid_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaOutputPenalty c (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤ qmaUnaryOutputEnergy c u := by
  rw [qmaOutputPenalty_sum]
  have hm : qmaHistoryClock c.gates.length (Fin.last c.gates.length) (qmaOutputMarker c) = 1 := by
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker]
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if s (qmaOutputMarker c) = 1 then
        ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
          Complex.normSq (u (s,a)) else 0 else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length (Fin.last c.gates.length))
    (by intro s _; split
        · apply Finset.sum_nonneg
          intro a _
          split
          · exact Complex.normSq_nonneg _
          · exact le_rfl
        · exact le_rfl) (Finset.mem_univ _)
  simpa only [ite_eq_left hm,qmaUnaryRestrict,qmaUnaryOutputEnergy] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnarySoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Soundness on the entire unary-clock Hilbert space, including every
invalid clock configuration. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaUnaryInvalidMass_nonneg (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    0 ≤ qmaUnaryInvalidMass c u := by
  apply Finset.sum_nonneg
  intro s _
  split
  · exact le_rfl
  · exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEmbedding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric embedding of the finite history into all unary clock strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaUnaryInclusion_injective (c : QMACircuit) : Function.Injective (qmaUnaryInclusion c) := by
  intro p q h
  change (qmaHistoryClock c.gates.length p.1,p.2) =
    (qmaHistoryClock c.gates.length q.1,q.2) at h
  apply Prod.ext
  · exact qmaHistoryClock_injective c.gates.length (congrArg Prod.fst h)
  · exact congrArg (fun r : QMAUnaryBasis c => r.2) h

@[simp] theorem qmaUnaryExtend_valid (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin (c.gates.length+1)) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryExtend c u (qmaHistoryClock c.gates.length t,a) = u (t,a) :=
  (qmaUnaryInclusion_injective c).extend_apply u (fun _ => 0) (t,a)

theorem qmaUnaryExtend_zero (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (s : SourceSpinBasis (c.gates.length+2)) (a : SourceSpinBasis (c.work+1))
    (hs : ¬QMALegalClock c.gates.length s) : qmaUnaryExtend c u (s,a) = 0 := by
  apply Function.extend_apply'
  rintro ⟨p,hp⟩
  apply hs
  have h := qmaHistoryClock_legal c.gates.length p.1
  rwa [show qmaHistoryClock c.gates.length p.1 = s from congrArg Prod.fst hp] at h

@[simp] theorem qmaUnaryRestrict_extend (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryRestrict c (qmaUnaryExtend c u) = u := by
  funext p
  exact qmaUnaryExtend_valid c u p.1 p.2

theorem qmaUnaryExtend_invalid_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryInvalidMass c (qmaUnaryExtend c u) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : QMALegalClock c.gates.length s
  · simp only [ite_eq_left hs]
  · simp only [ite_eq_right hs,qmaUnaryExtend_zero c u s _ hs,Complex.normSq_zero,Finset.sum_const_zero]

theorem qmaUnaryExtend_mass (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryMass c (qmaUnaryExtend c u) = ∑ p, Complex.normSq (u p) := by
  rw [qmaUnaryMass_split,qmaUnaryRestrict_extend,qmaUnaryExtend_invalid_mass,add_zero]

theorem qmaUnaryExtend_clock_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryClockEnergy c (qmaUnaryExtend c u) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : QMALegalClock c.gates.length s
  · rw [qmaPinnedClockPenalty_zero _ _ hs,zero_mul]
  · simp only [qmaUnaryExtend_zero c u s _ hs,Complex.normSq_zero,Finset.sum_const_zero,mul_zero]

theorem qmaUnaryResidual_extend_invalid (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.gates.length+2))
    (hg : QMAClockGuard c.gates.length t s) (hz : s (qmaClockMiddle c.gates.length t) = 0)
    (hs : ¬QMALegalClock c.gates.length s) (a : SourceSpinBasis (c.work+1)) :
    qmaUnaryResidual c (qmaUnaryExtend c u) t s a = 0 := by
  have ha : ¬QMALegalClock c.gates.length (Function.update s (qmaClockMiddle c.gates.length t) 1) :=
    fun h => hs ((qmaClock_step_legal_iff c.gates.length t s hg hz).mp h)
  have he : (fun b => qmaUnaryExtend c u (s,b)) = 0 := by
    funext b
    exact qmaUnaryExtend_zero c u s b hs
  unfold qmaUnaryResidual
  rw [he,Matrix.mulVec_zero,qmaUnaryExtend_zero c u _ a ha]
  simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryEmbeddingEnergy
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact energy preservation of the accepting unary-clock embedding. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaUnaryExtend_weighted_sum (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (w : SourceSpinBasis (c.gates.length+2) → SourceSpinBasis (c.work+1) → ℝ) :
    (∑ s : SourceSpinBasis (c.gates.length+2), ∑ a,
      w s a*Complex.normSq (qmaUnaryExtend c u (s,a))) =
    ∑ t : Fin (c.gates.length+1), ∑ a,
      w (qmaHistoryClock c.gates.length t) a*Complex.normSq (u (t,a)) := by
  have he := qmaClock_sector_sum c.gates.length (fun s =>
    ∑ a, w s a*Complex.normSq (qmaUnaryExtend c u (s,a)))
  have hz : (∑ s : SourceSpinBasis (c.gates.length+2),
      if QMALegalClock c.gates.length s then 0 else
        ∑ a, w s a*Complex.normSq (qmaUnaryExtend c u (s,a))) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : QMALegalClock c.gates.length s
    · exact ite_eq_left hs
    · simp only [ite_eq_right hs,qmaUnaryExtend_zero c u s _ hs,
        Complex.normSq_zero,mul_zero,Finset.sum_const_zero]
  rw [hz,add_zero] at he
  simpa only [qmaUnaryExtend_valid] using he

theorem qmaHistoryClock_output_marker (c : QMACircuit) (t : Fin (c.gates.length+1)) :
    qmaHistoryClock c.gates.length t (qmaOutputMarker c) = 1 ↔ t = Fin.last c.gates.length := by
  by_cases ht : t = Fin.last c.gates.length
  · subst t
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker]
  · have hn : t.val ≠ c.gates.length := fun h => ht (Fin.ext h)
    have hh : ¬c.gates.length < t.val+1 := by omega
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker,hh,ht]

theorem qmaUnaryExtend_output_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryOutputEnergy c (qmaUnaryExtend c u) =
      qmaOutputPenalty c (qmaHistoryFromVector c u) := by
  have h := qmaUnaryExtend_weighted_sum c u (fun s a =>
    if s (qmaOutputMarker c) = 1 ∧ a (Fin.last c.work) ≠ 1 then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,
    Finset.sum_const_zero,qmaHistoryClock_output_marker] at h
  rw [qmaOutputPenalty_sum]
  simpa only [qmaUnaryOutputEnergy,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] using h

theorem qmaUnaryExtend_propagation_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryPropagationEnergy c (qmaUnaryExtend c u) =
      qmaPropagationEnergy c (qmaHistoryFromVector c u) := by
  rw [←qmaPropagationMatrix_energy,qmaQuadratic_gram,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  have hz : QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
      qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 :=
    ⟨qmaClock_step_guard _ _,qmaClock_step_zero _ _⟩
  calc
    _ = (if QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
        qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 then
        ∑ a, Complex.normSq (qmaUnaryResidual c (qmaUnaryExtend c u) t
          (qmaHistoryClock c.gates.length t.castSucc) a) else 0) := by
      apply Finset.sum_eq_single (qmaHistoryClock c.gates.length t.castSucc)
      · intro s _ hne
        by_cases ha : QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0
        · rw [ite_eq_left ha]
          have hs : ¬QMALegalClock c.gates.length s := by
            intro hs
            exact hne (qmaClock_step_legal_before _ _ _ ha.1 ha.2 hs).symm
          apply Finset.sum_eq_zero
          intro a _
          rw [qmaUnaryResidual_extend_invalid c u t s ha.1 ha.2 hs a,Complex.normSq_zero]
        · exact ite_eq_right ha
      · simp
    _ = _ := by simp only [ite_eq_left hz,qmaUnaryResidual_valid,qmaUnaryRestrict_extend]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnaryMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Hermitian matrix on all clock and computation qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaUnaryPropagationMatrix_form (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c) u =
      qmaUnaryPropagationEnergy c u := by
  rw [qmaQuadratic_gram,qmaUnaryPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simp [Fintype.sum_prod_type,qmaUnaryPropagationMap,qmaUnaryPropagationEnergy,
    apply_ite,Finset.sum_ite_irrel]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUnarySpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full qubit-space history Hamiltonian has a strict inverse-polynomial
promise gap. No restriction to the valid clock subspace is assumed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaUnaryMass_norm (c : QMACircuit) (u : EuclideanSpace ℂ (QMAUnaryBasis c)) :
    qmaUnaryMass c (fun p => u p) = ‖u‖^2 := by
  simp only [qmaUnaryMass,EuclideanSpace.norm_sq_eq,Complex.sq_norm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaUnaryExtend_valid _root_.OAI.ContinuumCoulomb.qmaUnaryRestrict_extend _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input checks may occur at separate history times before their qubits are changed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaMask_norm_sq {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u‖^2 = ∑ s, if p s then ‖u s‖^2 else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : p s <;> simp [qmaMask_apply,hs]

theorem qmaInputPenalty_le_checks (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputPenalty c u ≤ ∑ i : Fin (c.work+1), ‖qmaMask (qmaInputCheck c i) (u 0)‖^2 := by
  simp only [qmaInputPenalty,qmaMask_norm_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  have h := mul_le_mul_of_nonneg_right (qmaAncillaCount_dominates c s) (sq_nonneg ‖u 0 s‖)
  have hs : (∑ i : Fin (c.work+1), if qmaInputCheck c i s then ‖u 0 s‖^2 else 0) =
      qmaAncillaCount c s*‖u 0 s‖^2 := by
    rw [qmaAncillaCount,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c.witness ≤ i.val ∧ s i ≠ 0
    · simp [qmaInputCheck,hi]
    · simp [qmaInputCheck,hi]
  rw [hs]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  by_cases hc : QMAAncillaZero c s <;> simp [hc]

theorem qmaInputPenalty_le_distributed (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hcheck : ∀ (i : Fin (c.work+1)) (v : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))),
      ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c (τ i)) v)‖ =
        ‖qmaMask (qmaInputCheck c i) v‖)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputPenalty c u ≤ 2*qmaDistributedInput c τ u+
      2*(c.work+1:ℝ)*c.gates.length*qmaPropagationEnergy c u := by
  apply (qmaInputPenalty_le_checks c u).trans
  have h (i : Fin (c.work+1)) : ‖qmaMask (qmaInputCheck c i) (u 0)‖^2 ≤
      2*‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2+
        2*c.gates.length*qmaPropagationEnergy c u := by
    let v := qmaApplyMatrix (qmaPrefixMatrix c (τ i)) (u 0)
    have hd := pow_le_pow_left₀ (norm_nonneg _)
      (qmaMask_sub_norm_le (qmaInputCheck c i) v (u (τ i))) 2
    rw [norm_sub_rev v] at hd
    have ha := qma_history_anchor_bound c hc u (τ i) (hτ i)
    have hs := norm_add_sq_two (qmaMask (qmaInputCheck c i) (u (τ i)))
      (qmaMask (qmaInputCheck c i) v-qmaMask (qmaInputCheck c i) (u (τ i)))
    rw [add_sub_cancel, hcheck i (u 0)] at hs
    dsimp only [v] at hd
    linarith
  calc
    _ ≤ ∑ i : Fin (c.work+1),
        (2*‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2+
          2*c.gates.length*qmaPropagationEnergy c u) := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,qmaDistributedInput]
      push_cast
      ring

theorem qmaDistributedHistoryEnergy_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hcheck : ∀ (i : Fin (c.work+1)) (v : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))),
      ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c (τ i)) v)‖ =
        ‖qmaMask (qmaInputCheck c i) v‖)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaDistributedHistoryEnergy c τ u := by
  have h := qmaInputPenalty_le_distributed c hc τ hτ hcheck u
  have he : qmaHistoryEnergy c u ≤ qmaDistributedHistoryEnergy c τ u := by
    unfold qmaHistoryEnergy qmaDistributedHistoryEnergy
    nlinarith
  exact (qma_history_energy_sound c hc hsound u).trans
    (mul_le_mul_of_nonneg_left he (by positivity))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireSwap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaUnaryExtend_valid _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact three-CNOT transfers for a circuit whose active wires move through a grid. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaWirePermutation_mul {n : ℕ} (f g : SourceSpinBasis n → SourceSpinBasis n) :
    qmaWirePermutation f*qmaWirePermutation g = qmaWirePermutation (f ∘ g) := by
  ext s t
  simp only [qmaWirePermutation,Matrix.mul_apply,mul_ite,mul_zero]
  rw [Finset.sum_eq_single (g t)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem qmaControlledNot_swap (work : ℕ) (i j : Fin (work+1)) (hij : i ≠ j)
    (s : SourceSpinBasis (work+1)) :
    qmaControlledNot work i j (qmaControlledNot work j i (qmaControlledNot work i j s)) =
      s ∘ Equiv.swap i j := by
  funext k
  by_cases hki : k = i
  · subst k
    generalize hi : s i = a
    generalize hj : s j = b
    fin_cases a <;> fin_cases b <;>
      simp [qmaControlledNot,hij,hi,hj]
  by_cases hkj : k = j
  · subst k
    generalize hi : s i = a
    generalize hj : s j = b
    fin_cases a <;> fin_cases b <;>
      simp [qmaControlledNot,hij,Ne.symm hij,hi,hj]
  · simp [qmaControlledNot,hki,hkj,Equiv.swap_apply_def]

theorem qmaGateMatrix_cnot_fin {work : ℕ} (i j : Fin (work+1)) :
    qmaGateMatrix work (.controlledNot i.val j.val) = qmaWirePermutation (qmaControlledNot work i j) := by
  rw [qmaGateMatrix,qmaQubit_fin,qmaQubit_fin]
  rfl

theorem qmaWireSwap_matrix {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j) :
    qmaCircuitMatrix ⟨work,0,qmaWireSwapGates i j⟩ =
      qmaWirePermutation (fun s => s ∘ Equiv.swap i j) := by
  simp only [qmaCircuitMatrix,qmaWireSwapGates,List.foldl_cons,List.foldl_nil,
    qmaGateMatrix_cnot_fin,mul_one]
  rw [qmaWirePermutation_mul,qmaWirePermutation_mul]
  congr 1
  funext s
  exact qmaControlledNot_swap work i j hij s

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateProduct
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaUnaryExtend_valid _root_.OAI.ContinuumCoulomb.qmaUnaryRestrict_extend _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sequential products for the circuit transformations used by the sparse history. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

theorem qmaGateProduct_fold (work : ℕ) (gs : List QMAGate)
    (M : Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ) :
    gs.foldl (fun A g => qmaGateMatrix work g*A) M = qmaGateProduct work gs*M := by
  induction gs generalizing M with
  | nil => simp [qmaGateProduct,qmaCircuitMatrix]
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    change _ = gs.foldl (fun A g => qmaGateMatrix work g*A) (qmaGateMatrix work g*1)*M
    rw [ih]
    simp only [mul_one,mul_assoc]

theorem qmaGateProduct_append (work : ℕ) (xs ys : List QMAGate) :
    qmaGateProduct work (xs++ys) = qmaGateProduct work ys*qmaGateProduct work xs := by
  change (xs++ys).foldl _ 1 = _
  rw [List.foldl_append,qmaGateProduct_fold]
  rfl

theorem qmaGateProduct_singleton (work : ℕ) (g : QMAGate) :
    qmaGateProduct work [g] = qmaGateMatrix work g := by
  simp [qmaGateProduct,qmaCircuitMatrix]

theorem qmaGateProduct_nil (work : ℕ) : qmaGateProduct work [] = 1 := rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireRelabel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaUnaryExtend_valid _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate changes for gates and circuit products. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem sourceTensor_wire_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    sourceTensor n (fun k => M (σ.symm k)) = qmaWireRelabelMatrix σ (sourceTensor n M) := by
  ext s t
  change (∏ k, M (σ.symm k) (s k) (t k)) = ∏ k, M k (s (σ k)) (t (σ k))
  exact Fintype.prod_equiv σ.symm _ _ (by intro k; simp)

theorem qmaControlledNot_wire_relabel (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (i j : Fin (work+1)) (s : SourceSpinBasis (work+1)) :
    qmaControlledNot work i j (qmaWireBasis σ s) =
      qmaWireBasis σ (qmaControlledNot work (σ i) (σ j) s) := by
  funext k
  by_cases hk : k = j
  · subst k
    by_cases hs : s (σ i) = 1 <;> simp [qmaControlledNot,qmaWireBasis,hs]
  · have hσ : σ k ≠ σ j := fun h => hk (σ.injective h)
    simp [qmaControlledNot,qmaWireBasis,hk,hσ]

theorem qmaRelabelGate_matrix (work : ℕ) (σ : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateMatrix work (qmaRelabelGate work σ g) =
      qmaWireRelabelMatrix σ (qmaGateMatrix work g) := by
  cases g with
  | hadamard i =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    rw [← sourceTensor_wire_relabel]
    congr 1
    funext k
    simp [Equiv.symm_apply_eq]
  | phaseT i =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    rw [← sourceTensor_wire_relabel]
    congr 1
    funext k
    simp [Equiv.symm_apply_eq]
  | controlledNot i j =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    ext s t
    change (if s = qmaControlledNot work (σ (qmaQubit work i)) (σ (qmaQubit work j)) t
      then (1:ℂ) else 0) =
      if qmaWireBasis σ s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j)
        (qmaWireBasis σ t) then 1 else 0
    simp only [qmaControlledNot_wire_relabel, (qmaWireBasis σ).injective.eq_iff]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumUntouchedInput
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A qubit's initialization check can be placed immediately before its first gate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem QMALocalOn.entry_zero_of_outside {n : ℕ} {S : Finset (Fin n)}
    {M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ}
    (hM : QMALocalOn S M) {i : Fin n} (hi : i ∉ S)
    (s t : SourceSpinBasis n) (hst : s i ≠ t i) : M s t = 0 := by
  obtain ⟨A,rfl⟩ := hM
  rw [qmaLocalLift_apply]
  have h : (fun k : {k // k ∉ S} => s k.val) ≠ (fun k : {k // k ∉ S} => t k.val) := by
    intro he
    exact hst (congrFun he ⟨i,hi⟩)
  simp [h]

theorem qmaLocal_mask_commute {n : ℕ} {S : Finset (Fin n)}
    {M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ}
    (hM : QMALocalOn S M) {i : Fin n} (hi : i ∉ S) (P : Fin 2 → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaMask (fun s => P (s i)) (qmaApplyMatrix M u) =
      qmaApplyMatrix M (qmaMask (fun s => P (s i)) u) := by
  ext s
  change (if P (s i) then ∑ t, M s t*u t else 0) =
    ∑ t, M s t*(if P (t i) then u t else 0)
  by_cases hs : P (s i)
  · rw [ite_eq_left hs]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : P (t i)
    · simp [ht]
    · have he : s i ≠ t i := fun h => ht (h ▸ hs)
      simp [ht,hM.entry_zero_of_outside hi s t he]
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : P (t i)
    · have he : s i ≠ t i := fun h => hs (h ▸ ht)
      simp [ht,hM.entry_zero_of_outside hi s t he]
    · simp [ht]

theorem qmaGateProduct_mask_commute (work : ℕ) (gs : List QMAGate)
    (i : Fin (work+1)) (hi : ∀ g ∈ gs, i ∉ qmaGateSites work g)
    (P : Fin 2 → Prop) (u : EuclideanSpace ℂ (SourceSpinBasis (work+1))) :
    qmaMask (fun s => P (s i)) (qmaApplyMatrix (qmaGateProduct work gs) u) =
      qmaApplyMatrix (qmaGateProduct work gs) (qmaMask (fun s => P (s i)) u) := by
  induction gs using List.reverseRecOn with
  | nil => simp [qmaGateProduct_nil]
  | append_singleton gs g ih =>
    simp only [qmaGateProduct_append,qmaGateProduct_singleton,qmaApplyMatrix_mul]
    rw [qmaLocal_mask_commute (qmaGateMatrix_local work g)
      (hi g (by simp)) P,ih (fun g hg => hi g (by simp [hg]))]

theorem qmaInputCheck_prefix_untouched (c : QMACircuit) (hc : c.WellFormed)
    (i : Fin (c.work+1)) (t : ℕ)
    (hi : ∀ g ∈ c.gates.take t, i ∉ qmaGateSites c.work g)
    (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c t) u)‖ =
      ‖qmaMask (qmaInputCheck c i) u‖ := by
  have h := qmaGateProduct_mask_commute c.work (c.gates.take t) i hi
    (fun b => c.witness ≤ i.val ∧ b ≠ 0) u
  change qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c t) u) =
    qmaApplyMatrix (qmaPrefixMatrix c t) (qmaMask (qmaInputCheck c i) u) at h
  rw [h,qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc t)]

theorem qmaDistributedHistoryEnergy_sound_untouched (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i), i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaDistributedHistoryEnergy c τ u :=
  qmaDistributedHistoryEnergy_sound c hc τ hτ
    (fun i v => qmaInputCheck_prefix_untouched c hc i (τ i) (hi i) v) hsound u

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferSweep
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sweeps of disjoint three-CNOT wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaTransferGates_matrix {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1)))
    (hp : ∀ p ∈ ps, p.1 ≠ p.2) :
    qmaGateProduct work (qmaTransferGates ps) =
      qmaWirePermutation (fun s => s ∘ qmaTransferPermutation ps) := by
  induction ps with
  | nil =>
    ext s t
    simp [qmaTransferGates,qmaGateProduct_nil,qmaTransferPermutation,qmaWirePermutation,Matrix.one_apply]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    rw [qmaTransferGates,qmaGateProduct_append,ih (fun p h => hp p (by simp [h]))]
    rw [show qmaGateProduct work (qmaWireSwapGates i j) =
      qmaWirePermutation (fun s => s ∘ Equiv.swap i j) from
        qmaWireSwap_matrix i j (hp (i,j) (by simp))]
    rw [qmaWirePermutation_mul]
    rfl

theorem qmaTransferPermutation_fixed {n : ℕ} (ps : List (Fin n × Fin n)) (k : Fin n)
    (hk : ∀ p ∈ ps, k ≠ p.1 ∧ k ≠ p.2) : qmaTransferPermutation ps k = k := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    change Equiv.swap i j (qmaTransferPermutation ps k) = k
    rw [ih (fun p h => hk p (by simp [h]))]
    exact Equiv.swap_apply_of_ne_of_ne (hk (i,j) (by simp)).1 (hk (i,j) (by simp)).2

theorem qmaTransferPermutation_exchanges {n : ℕ} (ps : List (Fin n × Fin n))
    (hp : ps.Pairwise QMATransferDisjoint) (p : Fin n × Fin n) (hm : p ∈ ps) :
    qmaTransferPermutation ps p.1 = p.2 ∧ qmaTransferPermutation ps p.2 = p.1 := by
  induction ps with
  | nil => simp at hm
  | cons q ps ih =>
    obtain ⟨hq,ht⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hm with rfl | hm
    · have h₁ : qmaTransferPermutation ps p.1 = p.1 :=
        qmaTransferPermutation_fixed ps p.1 (fun p h => ⟨(hq p h).1,(hq p h).2.1⟩)
      have h₂ : qmaTransferPermutation ps p.2 = p.2 :=
        qmaTransferPermutation_fixed ps p.2 (fun p h => ⟨(hq p h).2.2.1,(hq p h).2.2.2⟩)
      change Equiv.swap p.1 p.2 (qmaTransferPermutation ps p.1) = p.2 ∧
        Equiv.swap p.1 p.2 (qmaTransferPermutation ps p.2) = p.1
      simp [h₁,h₂]
    · obtain ⟨h₁,h₂⟩ := ih ht hm
      change Equiv.swap q.1 q.2 (qmaTransferPermutation ps p.1) = p.2 ∧
        Equiv.swap q.1 q.2 (qmaTransferPermutation ps p.2) = p.1
      rw [h₁,h₂]
      exact ⟨Equiv.swap_apply_of_ne_of_ne (hq p hm).2.1.symm (hq p hm).2.2.2.symm,
        Equiv.swap_apply_of_ne_of_ne (hq p hm).1.symm (hq p hm).2.2.1.symm⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFirstUse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete schedule of initialization checks, one at each qubit's first use. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaFirstUse_untouched (c : QMACircuit) (i : Fin (c.work+1)) :
    ∀ g ∈ c.gates.take (qmaFirstUse c i), i ∉ qmaGateSites c.work g := by
  intro g hg
  have h := List.false_of_mem_take_findIdx hg
  exact of_decide_eq_false h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving a complete register between two disjoint rows. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowPairs_disjoint {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) : (qmaRowPairs l r).Pairwise QMATransferDisjoint := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  have hne : i ≠ j := ne_of_lt hij
  exact ⟨fun h => hne (hl h),hlr i j,(hlr j i).symm,fun h => hne (hr h)⟩

theorem qmaRowTransfer_coordinates {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (i : Fin n) :
    qmaTransferPermutation (qmaRowPairs l r) (l i) = r i ∧
      qmaTransferPermutation (qmaRowPairs l r) (r i) = l i :=
  qmaTransferPermutation_exchanges _ (qmaRowPairs_disjoint l r hl hr hlr) (l i,r i)
    (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem qmaRowTransfer_fixed {n work : ℕ} (l r : Fin n → Fin (work+1))
    (k : Fin (work+1)) (hl : ∀ i, k ≠ l i) (hr : ∀ i, k ≠ r i) :
    qmaTransferPermutation (qmaRowPairs l r) k = k := by
  apply qmaTransferPermutation_fixed
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨hl i,hr i⟩

theorem qmaRowTransfer_matrix {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hlr : ∀ i j, l i ≠ r j) :
    qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) =
      qmaWirePermutation (fun s => s ∘ qmaTransferPermutation (qmaRowPairs l r)) :=
  qmaTransferGates_matrix _ (qmaRowPairs_distinct l r hlr)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireIntertwining
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining identities for moving operators together with their active wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaWirePermutation_mul_matrix {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (s t : SourceSpinBasis n) :
    (qmaWirePermutation e*M) s t = M (e.symm s) t := by
  simp only [Matrix.mul_apply,qmaWirePermutation]
  rw [Finset.sum_eq_single (e.symm s)]
  · simp
  · intro b _ hb
    have h : s ≠ e b := fun he => hb ((e.eq_symm_apply.mpr he.symm))
    simp [h]
  · simp

theorem qmaMatrix_mul_wirePermutation {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (s t : SourceSpinBasis n) :
    (M*qmaWirePermutation e) s t = M s (e t) := by
  simp only [Matrix.mul_apply,qmaWirePermutation]
  rw [Finset.sum_eq_single (e t)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem qmaWirePermutation_intertwines {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    qmaWirePermutation e*M = M.submatrix e.symm e.symm*qmaWirePermutation e := by
  ext s t
  rw [qmaWirePermutation_mul_matrix,qmaMatrix_mul_wirePermutation]
  simp

theorem qmaWireBasis_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (qmaWireBasis σ).symm = qmaWireBasis σ.symm := by
  ext s k
  rfl

theorem qmaGate_wire_intertwines (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) :
    qmaWirePermutation (qmaWireBasis σ)*qmaGateMatrix work g =
      qmaGateMatrix work (qmaRelabelGate work σ.symm g)*qmaWirePermutation (qmaWireBasis σ) := by
  rw [qmaWirePermutation_intertwines,qmaRelabelGate_matrix,qmaWireBasis_symm]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumTransferGate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logical gate may be inserted when its operands have reached the next row. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaRelabelGate_fixed (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (hs : ∀ i ∈ qmaGateSites work g, σ i = i) : qmaRelabelGate work σ g = g := by
  cases g with
  | hadamard i =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg]
  | phaseT i =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg]
  | controlledNot i j =>
    have hi := hs (qmaQubit work i) (by simp [qmaGateSites])
    have hj := hs (qmaQubit work j) (by simp [qmaGateSites])
    rw [qmaRelabelGate,hi,hj]
    simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1]

theorem qmaTransferGates_append {work : ℕ}
    (xs ys : List (Fin (work+1) × Fin (work+1))) :
    qmaTransferGates (xs++ys) = qmaTransferGates xs++qmaTransferGates ys := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨i,j⟩
    simp only [List.cons_append,qmaTransferGates,ih,List.append_assoc]

theorem qmaTransfer_gate_commute {work : ℕ}
    (ps : List (Fin (work+1) × Fin (work+1))) (hp : ∀ p ∈ ps, p.1 ≠ p.2)
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (ha : ∀ i ∈ qmaGateSites work g, ∀ p ∈ ps, i ≠ p.1 ∧ i ≠ p.2) :
    qmaGateProduct work (qmaTransferGates ps)*qmaGateMatrix work g =
      qmaGateMatrix work g*qmaGateProduct work (qmaTransferGates ps) := by
  let σ := qmaTransferPermutation ps
  have hs : ∀ i ∈ qmaGateSites work g, σ i = i :=
    fun i hi => qmaTransferPermutation_fixed ps i (ha i hi)
  have hi : ∀ i ∈ qmaGateSites work g, σ.symm i = i := by
    intro i h
    exact σ.symm_apply_eq.mpr (hs i h).symm
  rw [qmaTransferGates_matrix ps hp]
  change qmaWirePermutation (qmaWireBasis σ)*qmaGateMatrix work g =
    qmaGateMatrix work g*qmaWirePermutation (qmaWireBasis σ)
  rw [qmaGate_wire_intertwines,qmaRelabelGate_fixed work σ.symm g hg hi]

theorem qmaTransfer_insert_gate {work : ℕ}
    (xs ys : List (Fin (work+1) × Fin (work+1))) (hy : ∀ p ∈ ys, p.1 ≠ p.2)
    (g : QMAGate) (hg : g.WellFormed (work+1))
    (ha : ∀ i ∈ qmaGateSites work g, ∀ p ∈ ys, i ≠ p.1 ∧ i ≠ p.2) :
    qmaGateProduct work (qmaTransferGates xs++[g]++qmaTransferGates ys) =
      qmaGateMatrix work g*qmaGateProduct work (qmaTransferGates (xs++ys)) := by
  simp only [qmaTransferGates_append,qmaGateProduct_append,qmaGateProduct_singleton]
  rw [←mul_assoc,qmaTransfer_gate_commute ys hy g hg ha,mul_assoc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete row-major physical qubits for the space-time wire construction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridTransfer_coordinates (rows width : ℕ) (r : Fin rows) (i : Fin (width+1)) :
    let σ := qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))
    σ (qmaGridQubit rows width r.castSucc i) = qmaGridQubit rows width r.succ i ∧
      σ (qmaGridQubit rows width r.succ i) = qmaGridQubit rows width r.castSucc i := by
  exact qmaRowTransfer_coordinates _ _ (qmaGridRow_injective rows width r.castSucc)
    (qmaGridRow_injective rows width r.succ)
    (qmaGridRows_disjoint rows width r.castSucc r.succ (qmaGridRow_ne rows r)) i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact composition of logical gates with successive physical wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaWireBasis_product {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    qmaWirePermutation (qmaWireBasis σ)*qmaWirePermutation (qmaWireBasis τ) =
      qmaWirePermutation (qmaWireBasis (σ.trans τ)) := by
  rw [qmaWirePermutation_mul]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumMappedGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit gate addresses for a logical register embedded in a larger wire grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRelabelGate_map (sourceWork targetWork : ℕ)
    (f : Fin (sourceWork+1) → Fin (targetWork+1))
    (σ : Equiv.Perm (Fin (targetWork+1))) (g : QMAGate) :
    qmaRelabelGate targetWork σ (qmaMapGate sourceWork targetWork f g) =
      qmaMapGate sourceWork targetWork (σ ∘ f) g := by
  cases g <;> simp only [qmaMapGate,qmaRelabelGate,qmaQubit_fin,Function.comp_apply]

theorem qmaMapGate_congr (sourceWork targetWork : ℕ)
    (f h : Fin (sourceWork+1) → Fin (targetWork+1)) (he : ∀ i, f i = h i) (g : QMAGate) :
    qmaMapGate sourceWork targetWork f g = qmaMapGate sourceWork targetWork h g := by
  have hf : f = h := funext he
  rw [hf]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cumulative row-transfer frame locates the active register exactly. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridFrame_active (rows width t : ℕ) (ht : t ≤ rows) (i : Fin (width+1)) :
    (qmaGridFrame rows width t ht).symm (qmaGridQubit rows width 0 i) =
      qmaGridQubit rows width ⟨t,by omega⟩ i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : t ≤ rows := by omega
    let r : Fin rows := ⟨t,by omega⟩
    change (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))).symm
        ((qmaGridFrame rows width t hp).symm (qmaGridQubit rows width 0 i)) = _
    rw [ih hp]
    exact (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))).symm_apply_eq.mpr
        (qmaGridTransfer_coordinates rows width r i).2.symm

theorem qmaGridFrame_gate (rows width t : ℕ) (ht : t ≤ rows) (g : QMAGate) :
    qmaRelabelGate (qmaGridWork rows width) (qmaGridFrame rows width t ht).symm
      (qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width 0) g) =
    qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width ⟨t,by omega⟩) g := by
  rw [qmaRelabelGate_map]
  apply qmaMapGate_congr
  intro i
  exact qmaGridFrame_active rows width t ht i

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridCircuit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete circuit that transfers its full active register to a fresh row per gate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaGridTransfer_frame (rows width start : ℕ) (h : start < rows) :
    qmaGateProduct (qmaGridWork rows width) (qmaGridTransfer rows width ⟨start,h⟩)*
      qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width start (Nat.le_of_lt h))) =
    qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+1) h)) := by
  unfold qmaGridTransfer
  rw [qmaRowTransfer_matrix _ _
    (qmaGridRows_disjoint rows width _ _ (qmaGridRow_ne rows ⟨start,h⟩))]
  exact qmaWireBasis_product _ _

theorem qmaGridCircuitFrom_matrix (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    qmaGateProduct (qmaGridWork rows width) (qmaGridCircuitFrom rows width start gs h)*
      qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width start (by omega))) =
    qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+gs.length) h))*
      qmaGateProduct (qmaGridWork rows width)
        (gs.map (qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width 0))) := by
  induction gs generalizing start with
  | nil => simp [qmaGridCircuitFrom,qmaGateProduct_nil]
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    let work := qmaGridWork rows width
    let G := qmaGateMatrix work (qmaMapGate width work (qmaGridQubit rows width 0) g)
    let P := qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+1) hs))
    have hg : qmaGateMatrix work (qmaMapGate width work
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)*P = P*G := by
      rw [←qmaGridFrame_gate rows width (start+1) hs g]
      exact (qmaGate_wire_intertwines work _ _).symm
    simp only [qmaGridCircuitFrom,List.map_cons]
    rw [show qmaMapGate width work (qmaGridQubit rows width 0) g ::
        gs.map (qmaMapGate width work (qmaGridQubit rows width 0)) =
      [qmaMapGate width work (qmaGridQubit rows width 0) g] ++
        gs.map (qmaMapGate width work (qmaGridQubit rows width 0)) from rfl]
    simp only [qmaGateProduct_append,qmaGateProduct_singleton]
    calc
      _ = qmaGateProduct work (qmaGridCircuitFrom rows width (start+1) gs ht)*
          (qmaGateMatrix work (qmaMapGate width work
            (qmaGridQubit rows width ⟨start+1,by omega⟩) g)*P) := by
          dsimp only [P,work]
          rw [mul_assoc,mul_assoc,qmaGridTransfer_frame rows width start hs]
      _ = qmaGateProduct work (qmaGridCircuitFrom rows width (start+1) gs ht)*P*G := by
          rw [hg,mul_assoc]
      _ = _ := by
          rw [ih (start+1) ht]
          have he : start+1+gs.length = start+(g::gs).length := by simp; omega
          simp only [he,mul_assoc,G,work]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting the original register from fresh grid wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaPaddedLeft_ne_right (work extra : ℕ) (i : Fin (work+1)) (j : Fin extra) :
    qmaPaddedLeft work extra i ≠ qmaPaddedRight work extra j := by
  intro h
  have hv := congrArg Fin.val ((qmaPaddedIndex work extra).injective h)
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

theorem qmaPaddedBasis_left (work extra : ℕ) (s : SourceSpinBasis (work+extra+1))
    (i : Fin (work+1)) : (qmaPaddedBasis work extra s).1 i = s (qmaPaddedLeft work extra i) := rfl

theorem qmaPaddedBasis_right (work extra : ℕ) (s : SourceSpinBasis (work+extra+1))
    (i : Fin extra) : (qmaPaddedBasis work extra s).2 i = s (qmaPaddedRight work extra i) := rfl

theorem qmaPaddedBasis_symm_left (work extra : ℕ)
    (p : SourceSpinBasis (work+1) × SourceSpinBasis extra) (i : Fin (work+1)) :
    (qmaPaddedBasis work extra).symm p (qmaPaddedLeft work extra i) = p.1 i :=
  congrFun (congrArg Prod.fst ((qmaPaddedBasis work extra).apply_symm_apply p)) i

theorem qmaPaddedBasis_symm_right (work extra : ℕ)
    (p : SourceSpinBasis (work+1) × SourceSpinBasis extra) (i : Fin extra) :
    (qmaPaddedBasis work extra).symm p (qmaPaddedRight work extra i) = p.2 i :=
  congrFun (congrArg Prod.snd ((qmaPaddedBasis work extra).apply_symm_apply p)) i

theorem sourceTensor_padded (work extra : ℕ)
    (M : Fin (work+extra+1) → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (work+extra+1) M).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
    sourceTensor (work+1) (fun i => M (qmaPaddedLeft work extra i)) ⊗ₖ
      sourceTensor extra (fun j => M (qmaPaddedRight work extra j)) := by
  ext p q
  change (∏ k, M k ((qmaPaddedBasis work extra).symm p k)
    ((qmaPaddedBasis work extra).symm q k)) = _
  rw [← (qmaPaddedIndex work extra).prod_comp]
  rw [Fin.prod_univ_add]
  change (∏ i, M (qmaPaddedLeft work extra i)
    ((qmaPaddedBasis work extra).symm p (qmaPaddedLeft work extra i))
    ((qmaPaddedBasis work extra).symm q (qmaPaddedLeft work extra i)))*
    (∏ j, M (qmaPaddedRight work extra j)
    ((qmaPaddedBasis work extra).symm p (qmaPaddedRight work extra j))
    ((qmaPaddedBasis work extra).symm q (qmaPaddedRight work extra j))) = _
  simp only [qmaPaddedBasis_symm_left,qmaPaddedBasis_symm_right]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedGate
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.ContinuumCoulomb.qmaPaddedLeft_val _root_.OAI.ContinuumCoulomb.qmaPaddedRight_val _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh wires are exact identity spectators for the lifted verifier circuit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaControlledNot_padded_left (work extra : ℕ) (c t : Fin (work+1))
    (s : SourceSpinBasis (work+extra+1)) :
    (qmaPaddedBasis work extra
      (qmaControlledNot (work+extra) (qmaPaddedLeft work extra c) (qmaPaddedLeft work extra t) s)).1 =
    qmaControlledNot work c t (qmaPaddedBasis work extra s).1 := by
  funext i
  by_cases hit : i = t
  · subst i
    by_cases hc : s (qmaPaddedLeft work extra c) = 1 <;>
      simp [qmaControlledNot,qmaPaddedBasis_left,hc]
  · have hleft := (qmaPaddedLeft_injective work extra).ne hit
    simp [qmaPaddedBasis_left,qmaControlledNot,hit,hleft]

theorem qmaControlledNot_padded_right (work extra : ℕ) (c t : Fin (work+1))
    (s : SourceSpinBasis (work+extra+1)) :
    (qmaPaddedBasis work extra
      (qmaControlledNot (work+extra) (qmaPaddedLeft work extra c) (qmaPaddedLeft work extra t) s)).2 =
    (qmaPaddedBasis work extra s).2 := by
  funext j
  have hj := (qmaPaddedLeft_ne_right work extra t j).symm
  simp [qmaPaddedBasis_right,qmaControlledNot,hj]

theorem qmaGateMatrix_padded (work extra : ℕ) (g : QMAGate) :
    (qmaGateMatrix (work+extra) (qmaMapGate work (work+extra) (qmaPaddedLeft work extra) g)).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      qmaGateMatrix work g ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ) := by
  cases g with
  | hadamard i =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    rw [sourceTensor_padded]
    have hl : (fun k : Fin (work+1) =>
        if qmaPaddedLeft work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaHadamard else 1) = (fun k => if k = qmaQubit work i then qmaHadamard else 1) := by
      funext k
      simp only [(qmaPaddedLeft_injective work extra).eq_iff]
    have hr : (fun k : Fin extra =>
        if qmaPaddedRight work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaHadamard else 1) = (fun _ => 1) := by
      funext k
      exact ite_eq_right (qmaPaddedLeft_ne_right work extra (qmaQubit work i) k).symm
    rw [hl,hr,sourceTensor_one]
  | phaseT i =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    rw [sourceTensor_padded]
    have hl : (fun k : Fin (work+1) =>
        if qmaPaddedLeft work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaPhaseT else 1) = (fun k => if k = qmaQubit work i then qmaPhaseT else 1) := by
      funext k
      simp only [(qmaPaddedLeft_injective work extra).eq_iff]
    have hr : (fun k : Fin extra =>
        if qmaPaddedRight work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaPhaseT else 1) = (fun _ => 1) := by
      funext k
      exact ite_eq_right (qmaPaddedLeft_ne_right work extra (qmaQubit work i) k).symm
    rw [hl,hr,sourceTensor_one]
  | controlledNot i j =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    ext p q
    let B := qmaPaddedBasis work extra
    let F := qmaControlledNot (work+extra) (qmaPaddedLeft work extra (qmaQubit work i))
      (qmaPaddedLeft work extra (qmaQubit work j))
    let f := qmaControlledNot work (qmaQubit work i) (qmaQubit work j)
    have hb : B (F (B.symm q)) = (f q.1,q.2) := by
      apply Prod.ext
      · rw [qmaControlledNot_padded_left]
        simp only [B,f,Equiv.apply_symm_apply]
      · rw [qmaControlledNot_padded_right]
        simp only [B,Equiv.apply_symm_apply]
    have he : B.symm p = F (B.symm q) ↔ p = (f q.1,q.2) := by
      constructor
      · intro h
        simpa only [Equiv.apply_symm_apply,hb] using congrArg B h
      · intro h
        apply B.injective
        simpa only [Equiv.apply_symm_apply,hb] using h
    change (if B.symm p = F (B.symm q) then (1:ℂ) else 0) =
      (if p.1 = f q.1 then 1 else 0)*(if p.2 = q.2 then 1 else 0)
    by_cases h₁ : p.1 = f q.1 <;> by_cases h₂ : p.2 = q.2 <;>
      simp [he,Prod.ext_iff,h₁,h₂]

theorem qmaGateProduct_padded (work extra : ℕ) (gs : List QMAGate) :
    (qmaGateProduct (work+extra) (gs.map (qmaMapGate work (work+extra) (qmaPaddedLeft work extra)))).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      qmaGateProduct work gs ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ) := by
  induction gs using List.reverseRecOn with
  | nil => simp [qmaGateProduct_nil,Matrix.submatrix_one_equiv]
  | append_singleton gs g ih =>
    simp only [List.map_append,List.map_cons,List.map_nil,qmaGateProduct_append,
      qmaGateProduct_singleton]
    rw [←Matrix.submatrix_mul_equiv _ _ (qmaPaddedBasis work extra).symm
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm,
      qmaGateMatrix_padded,ih,←Matrix.mul_kronecker_mul,one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWireState
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact state and measurement transport under wire permutations. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaWirePermutation_apply {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) (s : SourceSpinBasis n) :
    qmaApplyMatrix (qmaWirePermutation e) u s = u (e.symm s) := by
  change (∑ t, (if s = e t then (1:ℂ) else 0)*u t) = _
  rw [Finset.sum_eq_single (e.symm s)]
  · simp
  · intro t _ ht
    have hs : s ≠ e t := fun h => ht ((e.eq_symm_apply.mpr h.symm))
    simp [hs]
  · simp

theorem qmaWirePermutation_norm {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaApplyMatrix (qmaWirePermutation e) u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,qmaWirePermutation_apply]
  exact e.symm.sum_comp (fun s => ‖u s‖^2)

theorem qmaWirePermutation_mask {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (b : Fin 2) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaMask (fun s => s (σ.symm i) = b)
      (qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) u) =
    qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) (qmaMask (fun s => s i = b) u) := by
  ext s
  simp only [qmaMask_apply,qmaWirePermutation_apply,qmaWireBasis_symm]
  rfl

theorem qmaWirePermutation_probability {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (b : Fin 2) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask (fun s => s (σ.symm i) = b)
      (qmaApplyMatrix (qmaWirePermutation (qmaWireBasis σ)) u)‖^2 =
    ‖qmaMask (fun s => s i = b) u‖^2 := by
  rw [qmaWirePermutation_mask,qmaWirePermutation_norm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lifted circuit starts with exactly the original witness and zero fresh wires. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPaddedAncillaZero (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (s : SourceSpinBasis (c.work+extra+1)) :
    QMAAncillaZero (qmaPaddedCircuit c extra) s ↔
      QMAAncillaZero c (qmaPaddedBasis c.work extra s).1 ∧
        (qmaPaddedBasis c.work extra s).2 = 0 := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (qmaPaddedLeft c.work extra i) hi
    · funext j
      apply h (qmaPaddedRight c.work extra j)
      change c.witness ≤ c.work+1+j.val
      have hc' : c.witness ≤ c.work := hc.1
      omega
  · rintro ⟨hl,hr⟩ k hk
    suffices h : ∀ a : Fin ((c.work+1)+extra),
        c.witness ≤ (qmaPaddedIndex c.work extra a).val →
        s (qmaPaddedIndex c.work extra a) = 0 by
      have hm := h ((qmaPaddedIndex c.work extra).symm k)
      have he := (qmaPaddedIndex c.work extra).apply_symm_apply k
      rw [he] at hm
      exact hm hk
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · intro hi
      exact hl i hi
    · intro _
      exact congrFun hr j

theorem qmaPaddedWitnessRestrict (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaWitnessRestrict (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) s =
      qmaWitnessRestrict c hc (qmaPaddedBasis c.work extra s).1 := by
  funext i
  change s ⟨i.val,_⟩ = (qmaPaddedBasis c.work extra s).1 ⟨i.val,_⟩
  rw [qmaPaddedBasis_left]
  congr 1

theorem qmaInitialState_padded (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaInitialState (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi s =
      qmaInitialState c hc psi (qmaPaddedBasis c.work extra s).1 *
        if (qmaPaddedBasis c.work extra s).2 = 0 then 1 else 0 := by
  by_cases hs : QMAAncillaZero (qmaPaddedCircuit c extra) s
  · have hs' : ∀ i : Fin (c.work+extra+1), c.witness ≤ i.val → s i = 0 := hs
    obtain ⟨hl,hr⟩ := (qmaPaddedAncillaZero c hc extra s).mp hs
    have hl' : ∀ i : Fin (c.work+1), c.witness ≤ i.val →
        (qmaPaddedBasis c.work extra s).1 i = 0 := hl
    simp only [qmaInitialState,ite_eq_left hs',ite_eq_left hl',ite_eq_left hr,mul_one]
    exact congrArg (fun v => psi v) (qmaPaddedWitnessRestrict c hc extra s)
  · have hs' : ¬∀ i : Fin (c.work+extra+1), c.witness ≤ i.val → s i = 0 := hs
    by_cases hl : QMAAncillaZero c (qmaPaddedBasis c.work extra s).1
    · have hr : (qmaPaddedBasis c.work extra s).2 ≠ 0 :=
        fun h => hs ((qmaPaddedAncillaZero c hc extra s).mpr ⟨hl,h⟩)
      have hl' : ∀ i : Fin (c.work+1), c.witness ≤ i.val →
          (qmaPaddedBasis c.work extra s).1 i = 0 := hl
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_left hl',ite_eq_right hr,mul_zero]
    · have hl' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val →
          (qmaPaddedBasis c.work extra s).1 i = 0 := hl
      simp only [qmaInitialState,ite_eq_right hs',ite_eq_right hl',zero_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPaddedEvolution
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tensor evolution of the verifier together with zero fresh wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaTensor_zero_vector {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α α ℂ) (u : α → ℂ) (b : β) (p : α × β) :
    (M ⊗ₖ (1 : Matrix β β ℂ)).mulVec (fun q => u q.1*(if q.2 = b then 1 else 0)) p =
      M.mulVec u p.1*(if p.2 = b then 1 else 0) := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  by_cases hp : p.2 = b <;> simp [Matrix.one_apply,hp]

theorem qmaPadded_apply (work extra : ℕ)
    (N : Matrix (SourceSpinBasis (work+extra+1)) (SourceSpinBasis (work+extra+1)) ℂ)
    (M : Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ)
    (hN : N.submatrix (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      M ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ))
    (v : SourceSpinBasis (work+extra+1) → ℂ) (u : SourceSpinBasis (work+1) → ℂ)
    (hv : ∀ s, v s = u (qmaPaddedBasis work extra s).1*
      (if (qmaPaddedBasis work extra s).2 = 0 then 1 else 0))
    (s : SourceSpinBasis (work+extra+1)) :
    N.mulVec v s = M.mulVec u (qmaPaddedBasis work extra s).1*
      (if (qmaPaddedBasis work extra s).2 = 0 then 1 else 0) := by
  let B := qmaPaddedBasis work extra
  have hu : v ∘ B.symm = fun p => u p.1*(if p.2 = 0 then 1 else 0) := by
    funext p
    simp only [Function.comp_apply,hv,B,Equiv.apply_symm_apply]
  have h := Matrix.submatrix_mulVec_equiv N (v ∘ B.symm) B.symm B.symm
  have he : (v ∘ B.symm) ∘ B = v := by funext s; simp
  change N.submatrix B.symm B.symm *ᵥ (v ∘ B.symm) =
    (N *ᵥ ((v ∘ B.symm) ∘ B)) ∘ B.symm at h
  rw [he,show N.submatrix B.symm B.symm = _ from hN,hu] at h
  have hp := congrFun h (B s)
  simpa only [Function.comp_apply,Equiv.symm_apply_apply,qmaTensor_zero_vector] using hp.symm

theorem qmaOutputVector_padded (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaOutputVector (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi s =
      qmaOutputVector c hc psi (qmaPaddedBasis c.work extra s).1 *
        if (qmaPaddedBasis c.work extra s).2 = 0 then 1 else 0 := by
  apply qmaPadded_apply c.work extra (qmaCircuitMatrix (qmaPaddedCircuit c extra))
    (qmaCircuitMatrix c) (qmaGateProduct_padded c.work extra c.gates)
    (qmaInitialState (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi)
    (qmaInitialState c hc psi) (qmaInitialState_padded c hc extra psi) s

theorem qmaPaddedOutput_probability (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (i : Fin (c.work+1)) (b : Fin 2) :
    ‖qmaMask (fun s => s (qmaPaddedLeft c.work extra i) = b)
      (qmaOutputVector (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi)‖^2 =
    ‖qmaMask (fun s => s i = b) (qmaOutputVector c hc psi)‖^2 := by
  have hout (p : SourceSpinBasis (c.work+1) × SourceSpinBasis extra) :
      (qmaOutputVector (qmaPaddedCircuit c extra)
        (qmaPaddedCircuit_wellFormed c hc extra) psi).ofLp
          ((qmaPaddedBasis c.work extra).symm p) =
      (qmaOutputVector c hc psi).ofLp p.1 * (if p.2 = 0 then 1 else 0) := by
    simpa only [Equiv.apply_symm_apply] using
      qmaOutputVector_padded c hc extra psi ((qmaPaddedBasis c.work extra).symm p)
  rw [qmaMask_norm_sq,qmaMask_norm_sq]
  rw [←(qmaPaddedBasis c.work extra).symm.sum_comp]
  simp only [hout,qmaPaddedBasis_symm_left,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i = b
  · simp only [ha,ite_true, if_true]
    rw [Finset.sum_eq_single (0 : SourceSpinBasis extra)]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  · simp [ha]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridAcceptance
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete fresh-row circuit preserves verifier acceptance exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaGridQubit_zero (rows width : ℕ) :
    qmaGridQubit rows width 0 = qmaPaddedLeft width (rows*(width+1)) := by
  funext i
  apply Fin.ext
  simp [qmaGridQubit]

theorem qmaWirePermutation_refl (n : ℕ) :
    qmaWirePermutation (qmaWireBasis (Equiv.refl (Fin n))) =
      (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) := by
  ext s t
  simp only [qmaWirePermutation,qmaWireBasis,Equiv.coe_fn_mk,Matrix.one_apply]
  rfl

theorem qmaGridCircuit_matrix (c : QMACircuit) :
    qmaCircuitMatrix (qmaGridCircuit c) =
      qmaWirePermutation (qmaWireBasis
        (qmaGridFrame c.gates.length c.work c.gates.length le_rfl))*
      qmaCircuitMatrix (qmaPaddedCircuit c (c.gates.length*(c.work+1))) := by
  change qmaGateProduct (qmaGridWork c.gates.length c.work)
      (qmaGridCircuitFrom c.gates.length c.work 0 c.gates _) =
    qmaWirePermutation (qmaWireBasis
      (qmaGridFrame c.gates.length c.work c.gates.length le_rfl))*
    qmaGateProduct (qmaGridWork c.gates.length c.work)
      (c.gates.map (qmaMapGate c.work (qmaGridWork c.gates.length c.work)
        (qmaPaddedLeft c.work (c.gates.length*(c.work+1)))))
  have h := qmaGridCircuitFrom_matrix c.gates.length c.work 0 c.gates (by omega)
  simpa only [qmaGridFrame,qmaWirePermutation_refl,mul_one,Nat.zero_add,qmaGridQubit_zero] using h

theorem qmaGridCircuit_output (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaOutputVector (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi =
      qmaApplyMatrix (qmaWirePermutation (qmaWireBasis
        (qmaGridFrame c.gates.length c.work c.gates.length le_rfl)))
        (qmaOutputVector (qmaPaddedCircuit c (c.gates.length*(c.work+1)))
          (qmaPaddedCircuit_wellFormed c hc _) psi) := by
  change qmaApplyMatrix (qmaCircuitMatrix (qmaGridCircuit c))
      (qmaInputVector (qmaPaddedCircuit c (c.gates.length*(c.work+1)))
        (qmaPaddedCircuit_wellFormed c hc _) psi) = _
  rw [qmaGridCircuit_matrix,qmaApplyMatrix_mul]
  rfl

theorem qmaGridFrame_output (c : QMACircuit) :
    (qmaGridFrame c.gates.length c.work c.gates.length le_rfl).symm
      (qmaPaddedLeft c.work (c.gates.length*(c.work+1)) (Fin.last c.work)) =
      Fin.last (qmaGridWork c.gates.length c.work) := by
  rw [←qmaGridQubit_zero,qmaGridFrame_active]
  apply Fin.ext
  change c.gates.length*(c.work+1)+c.work = c.work+c.gates.length*(c.work+1)
  omega

theorem qmaGridCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  rw [qmaAcceptance_projection (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi,
    qmaAcceptance_projection c hc psi,qmaGridCircuit_output c hc psi]
  rw [←qmaGridFrame_output]
  rw [qmaWirePermutation_probability]
  exact qmaPaddedOutput_probability c hc _ psi (Fin.last c.work) 1

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSwapConjugation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conjugation by the three-CNOT adjacent-swap program. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaWireSwap_conjugate {work : ℕ} (i j : Fin (work+1)) (hij : i ≠ j)
    (g : QMAGate) :
    qmaGateProduct work (qmaWireSwapGates i j)*qmaGateMatrix work g*
      qmaGateProduct work (qmaWireSwapGates i j) =
        qmaGateMatrix work (qmaRelabelGate work (Equiv.swap i j) g) := by
  have hm : qmaGateProduct work (qmaWireSwapGates i j) =
      qmaWirePermutation (qmaWireBasis (Equiv.swap i j)) := qmaWireSwap_matrix i j hij
  rw [hm]
  rw [qmaGate_wire_intertwines,Equiv.symm_swap,mul_assoc,qmaWireBasis_product,
    Equiv.swap_swap,qmaWirePermutation_refl,mul_one]

theorem qmaSwap_relabels_ordered {work : ℕ} (i j k : Fin (work+1))
    (hki : k ≠ i) (hkj : k ≠ j) (forward : Bool) :
    qmaRelabelGate work (Equiv.swap i j) (qmaOrderedCnot j.val k.val forward) =
      qmaOrderedCnot i.val k.val forward := by
  cases forward <;>
    simp [qmaOrderedCnot,qmaRelabelGate,qmaQubit_fin,
      Equiv.swap_apply_of_ne_of_ne hki hkj]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAdjacentCnot
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size adjacent-CNOT program for one arbitrarily separated CNOT. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaAdjacentCnot_matrix (work a d : ℕ) (h : a+d+1 < work+1) (b : Bool) :
    qmaGateProduct work (qmaAdjacentCnot work a d h b) =
      qmaGateMatrix work (qmaOrderedCnot a (a+d+1) b) := by
  induction d generalizing a with
  | zero => exact qmaGateProduct_singleton _ _
  | succ d ih =>
    let i : Fin (work+1) := ⟨a,by omega⟩
    let j : Fin (work+1) := ⟨a+1,by omega⟩
    let k : Fin (work+1) := ⟨a+(d+1)+1,h⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    have hki : k ≠ i := by intro he; have := congrArg Fin.val he; dsimp [k,i] at this; omega
    have hkj : k ≠ j := by intro he; have := congrArg Fin.val he; dsimp [k,j] at this; omega
    simp only [qmaAdjacentCnot,qmaGateProduct_append,ih]
    rw [←mul_assoc]
    have he : a+1+d+1 = k.val := by dsimp [k]; omega
    rw [he]
    exact (qmaWireSwap_conjugate i j hij (qmaOrderedCnot j.val k.val b)).trans
      (congrArg (qmaGateMatrix work) (qmaSwap_relabels_ordered i j k hki hkj b))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalAction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actions of local flips and spectator-identity tensor factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaBitFlip_involutive (i : ι) : Function.Involutive (qmaBitFlip i) := by
  intro s
  funext j
  by_cases h : j = i
  · subst j
    simp [qmaBitFlip]
  · simp [qmaBitFlip,h]

theorem qmaBitFlipMatrix_mulVec (i : ι) (u : (ι → Fin 2) → ℂ) (s : ι → Fin 2) :
    (qmaBitFlipMatrix i).mulVec u s = u (qmaBitFlip i s) := by
  change (∑ t, (if s = qmaBitFlip i t then (1:ℂ) else 0)*u t) = _
  have he (t : ι → Fin 2) : s = qmaBitFlip i t ↔ t = qmaBitFlip i s := by
    constructor
    · intro h
      rw [h,qmaBitFlip_involutive]
    · intro h
      rw [h,qmaBitFlip_involutive]
  simp only [he,ite_mul,one_mul,zero_mul]
  simp

theorem qmaJoinMatrix_one_left_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) (u : (ι ⊕ κ → Fin 2) → ℂ)
    (s : ι ⊕ κ → Fin 2) :
    (qmaJoinMatrix (ι := ι) 1 A).mulVec u s =
      A.mulVec (fun b => u (Sum.elim (s ∘ Sum.inl) b)) (s ∘ Sum.inr) := by
  let e := Equiv.sumArrowEquivProdArrow ι κ (Fin 2)
  change (∑ t, qmaJoinMatrix 1 A s t*u t) = _
  rw [←e.symm.sum_comp (fun t => qmaJoinMatrix 1 A s t*u t),Fintype.sum_prod_type]
  change (∑ a, ∑ b, (if (s ∘ Sum.inl) = a then (1:ℂ) else 0)*
    A (s ∘ Sum.inr) b*u (Sum.elim a b)) = _
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [eq_comm,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationAction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact agreement of the local propagation operator with the full
unary-clock Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaLocalPropagationDelta_action (c : QMACircuit) (t : Fin c.gates.length)
    (u : QMAUnaryBasis c → ℂ) (s : QMACircuitQubit c → Fin 2) :
    (qmaLocalPropagationDelta c t).mulVec (u ∘ qmaCircuitQubitSplit c) s =
      qmaUnaryPropagationMap c u (t,qmaCircuitQubitSplit c s) := by
  rw [qmaLocalPropagationDelta,←Matrix.mulVec_mulVec,qmaGuardProjection,Matrix.mulVec_diagonal]
  by_cases h : QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0
  · rw [ite_eq_left h,one_mul,Matrix.sub_mulVec]
    change (qmaBitFlipMatrix (Sum.inl (qmaClockMiddle c.gates.length t))).mulVec
      (u ∘ qmaCircuitQubitSplit c) s-
      (qmaJoinMatrix 1 (qmaStepMatrix c t.val)).mulVec (u ∘ qmaCircuitQubitSplit c) s = _
    rw [qmaBitFlipMatrix_mulVec,qmaJoinMatrix_one_left_mulVec]
    have he : qmaCircuitQubitSplit c (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) s) =
        (Function.update (s ∘ Sum.inl) (qmaClockMiddle c.gates.length t) 1,s ∘ Sum.inr) := by
      apply Prod.ext
      · funext i
        by_cases hi : i = qmaClockMiddle c.gates.length t
        · subst i
          simp [qmaCircuitQubitSplit,qmaBitFlip,h.2]
        · simp [qmaCircuitQubitSplit,qmaBitFlip,hi]
      · funext i
        simp [qmaCircuitQubitSplit,qmaBitFlip]
    change u (qmaCircuitQubitSplit c (qmaBitFlip _ s))-
      (qmaStepMatrix c t.val).mulVec
        (fun b => u (qmaCircuitQubitSplit c (Sum.elim (s ∘ Sum.inl) b))) (s ∘ Sum.inr) = _
    rw [he]
    change _ = if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
        s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then _ else _
    rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h,zero_mul]
    exact (ite_eq_right h).symm

theorem qmaPropagationSlice_eq (c : QMACircuit) (t : Fin c.gates.length) :
    qmaPropagationSlice c t = (qmaLocalPropagationDelta c t).submatrix
      (qmaCircuitQubitSplit c).symm (qmaCircuitQubitSplit c).symm := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  funext p
  have h := qmaLocalPropagationDelta_action c t u ((qmaCircuitQubitSplit c).symm p)
  rw [Matrix.submatrix_mulVec_equiv]
  have he : u ∘ ((qmaCircuitQubitSplit c).symm).symm = u ∘ qmaCircuitQubitSplit c := rfl
  rw [he]
  change ((qmaUnaryPropagationMatrix c).mulVec u) (t,p) = _
  rw [qmaUnaryPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simpa only [Equiv.apply_symm_apply,Function.comp_apply] using h.symm

theorem qmaUnaryPropagationGram_sum (c : QMACircuit) :
    (qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c =
      ∑ t : Fin c.gates.length, (qmaPropagationSlice c t).conjTranspose*qmaPropagationSlice c t := by
  ext p q
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,qmaPropagationSlice,Matrix.submatrix_apply,id_eq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLocalDecomposition
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sum of finite-support terms for the full unary-clock Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaSubmatrix_add {α β γ δ : Type*} (A B : Matrix α β ℂ)
    (f : γ → α) (g : δ → β) : (A+B).submatrix f g = A.submatrix f g+B.submatrix f g := rfl

theorem qmaSubmatrix_smul {α β γ δ : Type*} (z : ℂ) (A : Matrix α β ℂ)
    (f : γ → α) (g : δ → β) : (z • A).submatrix f g = z • A.submatrix f g := rfl

theorem qmaUnaryPropagationGram_reindex (c : QMACircuit) :
    ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      ∑ t : Fin c.gates.length,
        (qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t := by
  have hs (t : Fin c.gates.length) :
      (qmaPropagationSlice c t).submatrix (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
        qmaLocalPropagationDelta c t := by
    rw [qmaPropagationSlice_eq]
    ext s r
    simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  calc
    _ = ∑ t : Fin c.gates.length,
        ((qmaPropagationSlice c t).conjTranspose*qmaPropagationSlice c t).submatrix
          (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) := by
      ext s r
      simp only [qmaUnaryPropagationGram_sum,Matrix.submatrix_apply,Matrix.sum_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [←Matrix.submatrix_mul_equiv _ _ (qmaCircuitQubitSplit c)
        (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c),←Matrix.conjTranspose_submatrix,hs]

theorem qmaUnaryClockDiagonal_reindex (c : QMACircuit) :
    (Matrix.diagonal (fun p => (qmaUnaryClockDiagonal c p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      (∑ i : Fin (c.gates.length+1), qmaClockFaultTerm c i)+qmaClockLeftTerm c+qmaClockRightTerm c := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [Matrix.add_apply,Matrix.sum_apply,qmaClockFaultTerm,qmaPairDiagonal,
      qmaClockLeftTerm,qmaClockRightTerm,qmaBitDiagonal,Matrix.diagonal_apply_eq]
    change ((qmaPinnedClockPenalty c.gates.length (s ∘ Sum.inl) : ℝ) : ℂ) =
      (∑ i : Fin (c.gates.length+1), if s (Sum.inl i.castSucc) = 0 ∧
        s (Sum.inl i.succ) = 1 then (1:ℂ) else 0)+
      (if s (Sum.inl 0) = 1 then 0 else 1)+
      (if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)
    unfold qmaPinnedClockPenalty qmaClockFaultCount
    rw [Complex.ofReal_add,Complex.ofReal_add,Complex.ofReal_sum]
    congr 2
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : s (Sum.inl i.castSucc) = 0 ∧ s (Sum.inl i.succ) = 1
      · simp [hi]
      · simp [hi]
    · by_cases hl : s (Sum.inl 0) = 1 <;> simp [Function.comp_apply,hl]
    · by_cases hr : s (Sum.inl (Fin.last (c.gates.length+1))) = 0
      <;> simp [Function.comp_apply,hr]
  · simp [h,Matrix.sum_apply,qmaClockFaultTerm,qmaPairDiagonal,
      qmaClockLeftTerm,qmaClockRightTerm,qmaBitDiagonal]

theorem qmaUnaryOutputDiagonal_reindex (c : QMACircuit) :
    (Matrix.diagonal (fun p => (qmaUnaryOutputDiagonal c p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) = qmaOutputTerm c := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [qmaOutputTerm,qmaPairDiagonal,Matrix.diagonal_apply_eq]
    change Complex.ofReal (qmaUnaryOutputDiagonal c (qmaCircuitQubitSplit c s)) = _
    unfold qmaUnaryOutputDiagonal
    by_cases ho : s (Sum.inl (qmaOutputMarker c)) = 1 ∧ s (Sum.inr (Fin.last c.work)) ≠ 1
    · have ho' : (qmaCircuitQubitSplit c s).1 (qmaOutputMarker c) = 1 ∧
          (qmaCircuitQubitSplit c s).2 (Fin.last c.work) ≠ 1 := ho
      calc
        _ = Complex.ofReal 1 := congrArg Complex.ofReal (ite_eq_left ho')
        _ = 1 := by norm_num
        _ = _ := (ite_eq_left ho).symm
    · have ho' : ¬((qmaCircuitQubitSplit c s).1 (qmaOutputMarker c) = 1 ∧
          (qmaCircuitQubitSplit c s).2 (Fin.last c.work) ≠ 1) := ho
      calc
        _ = Complex.ofReal 0 := congrArg Complex.ofReal (ite_eq_right ho')
        _ = 0 := by norm_num
        _ = _ := (ite_eq_right ho).symm
  · simp [h,qmaOutputTerm,qmaPairDiagonal]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCoordinateSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local qubit-coordinate matrices retain the full-space spectral
bounds, through explicit basis equivalences. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : β ≃ α) (A : Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (A.submatrix e e) (u ∘ e) = qmaQuadratic A u := by
  have he : (u ∘ e) ∘ e.symm = u := by funext i; simp
  unfold qmaQuadratic
  rw [Matrix.submatrix_mulVec_equiv,he]
  change (∑ i : β, star (u (e i))*A.mulVec u (e i)).re =
    (∑ i : α, star (u i)*A.mulVec u i).re
  exact congrArg Complex.re (e.sum_comp (fun i => star (u i)*A.mulVec u i))

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

theorem value_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    value (finiteProduct f) = ∏ a, value (f a) := by
  simp only [finiteProduct,value_product,enumerate,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin α).symm.prod_comp (fun a => value (f a))

theorem value_pauli (μ : Fin 4) (a b : Fin 2) :
    value (pauli μ a b) = qmaPauli μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,qmaPauli,pauliX,pauliY,pauliZ]

end ContinuumCoulomb.QuantumFixedPauli

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOperatorQuadratic
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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedClock
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local initialization checks at arbitrary unary-clock positions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaClockAt_history (T : ℕ) (t u : Fin (T+1)) :
    qmaClockAt T t (qmaHistoryClock T u) ↔ u = t := by
  simp only [qmaClockAt,qmaHistoryClock,qmaUnaryClock,Fin.val_castSucc,Fin.val_succ]
  constructor
  · intro ⟨h₁,h₂⟩
    have ha : t.val < u.val+1 := by
      by_contra h
      simp [h] at h₁
    have hb : ¬t.val+1 < u.val+1 := by
      intro h
      simp [h] at h₂
    apply Fin.ext
    omega
  · rintro rfl
    simp

theorem qmaUnaryDistributedInput_restrict (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaDistributedInput c (fun i => (τ i).val)
      (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤ qmaUnaryDistributedInput c τ u := by
  unfold qmaDistributedInput qmaUnaryDistributedInput
  apply Finset.sum_le_sum
  intro i _
  rw [qmaMask_norm_sq]
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if qmaClockAt c.gates.length (τ i) s then
        ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
          Complex.normSq (u (s,a)) else 0 else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length (τ i))
    (by
      intro s _
      split
      · apply Finset.sum_nonneg
        intro a _
        split
        · exact Complex.normSq_nonneg _
        · exact le_rfl
      · exact le_rfl) (Finset.mem_univ _)
  have hs : (∑ a : SourceSpinBasis (c.work+1),
      if qmaInputCheck c i a then
        ‖qmaHistoryFromVector c (qmaUnaryRestrict c u) (τ i).val a‖^2 else 0) =
      ∑ a : SourceSpinBasis (c.work+1), if qmaInputCheck c i a then
        Complex.normSq (u (qmaHistoryClock c.gates.length (τ i),a)) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [qmaHistoryFromVector_fin]
    simp only [qmaUnaryRestrict,Complex.sq_norm]
  rw [hs]
  simpa only [qmaClockAt_history,ite_true, if_true] using h

theorem qmaUnaryDistributedEnergy_restrict (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (qmaUnaryRestrict c u))+qmaUnaryClockEnergy c u ≤
      qmaUnaryDistributedEnergy c τ u := by
  have hi := qmaUnaryDistributedInput_restrict c τ u
  have ho := qmaUnaryOutputEnergy_valid_le c u
  have hp := mul_le_mul_of_nonneg_left (qmaUnaryPropagationEnergy_valid_le c u)
    (by positivity : 0 ≤ (14*(c.work+1)+8:ℝ)*c.gates.length)
  unfold qmaDistributedHistoryEnergy qmaUnaryDistributedEnergy
  linarith

theorem qmaUnaryDistributedEnergy_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) (u : QMAUnaryBasis c → ℂ) :
    2*qmaUnaryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaUnaryDistributedEnergy c τ u := by
  have hs := qmaDistributedHistoryEnergy_sound_untouched c hc (fun i => (τ i).val)
    (fun i => Nat.le_of_lt_succ (τ i).isLt) hi hsound
    (qmaHistoryFromVector c (qmaUnaryRestrict c u))
  rw [qmaHistoryFromVector_mass] at hs
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm] at hs
  have hb := qmaUnaryInvalidMass_le c u
  have hn := qmaUnaryInvalidMass_nonneg c u
  have hcoef : (2:ℝ) ≤ 5*(c.gates.length+1:ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) c.gates.length
    linarith
  have hb' : 2*qmaUnaryInvalidMass c u ≤
      5*(c.gates.length+1:ℝ)*qmaUnaryClockEnergy c u :=
    (mul_le_mul_of_nonneg_right hcoef hn).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  have he := mul_le_mul_of_nonneg_left (qmaUnaryDistributedEnergy_restrict c τ u)
    (by positivity : 0 ≤ 5*(c.gates.length+1:ℝ))
  rw [qmaUnaryMass_split]
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedWitness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Accepting histories retain exactly their output energy under distributed checks. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaUnaryExtend_distributed_input (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryDistributedInput c τ (qmaUnaryExtend c u) =
      qmaDistributedInput c (fun i => (τ i).val) (qmaHistoryFromVector c u) := by
  unfold qmaUnaryDistributedInput qmaDistributedInput
  apply Finset.sum_congr rfl
  intro i _
  have h := qmaUnaryExtend_weighted_sum c u (fun s a =>
    if qmaClockAt c.gates.length (τ i) s ∧ qmaInputCheck c i a then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,
    Finset.sum_const_zero,qmaClockAt_history] at h
  rw [qmaMask_norm_sq]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [qmaHistoryFromVector_fin]
  simp only [Complex.sq_norm]

theorem qmaInputVector_single_check_zero (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (i : Fin (c.work+1)) :
    qmaMask (qmaInputCheck c i) (qmaInputVector c hc psi) = 0 := by
  ext s
  by_cases hi : qmaInputCheck c i s
  · have hs : ¬∀ j : Fin (c.work+1), c.witness ≤ j.val → s j = 0 := by
      intro h
      exact hi.2 (h i hi.1)
    simp [hi,qmaInputVector,qmaInitialState,hs]
  · simp [hi]

theorem qmaIdealHistory_distributed_input (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaDistributedInput c (fun i => (τ i).val) (qmaIdealHistory c hc psi) = 0 := by
  unfold qmaDistributedInput qmaIdealHistory
  apply Finset.sum_eq_zero
  intro i _
  rw [qmaInputCheck_prefix_untouched c hc i (τ i).val (hi i),
    qmaInputVector_single_check_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem qmaUnaryExtend_distributed_energy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryDistributedEnergy c τ (qmaUnaryExtend c u) =
      qmaDistributedHistoryEnergy c (fun i => (τ i).val) (qmaHistoryFromVector c u) := by
  rw [qmaUnaryDistributedEnergy,qmaUnaryExtend_clock_energy,
    qmaUnaryExtend_distributed_input,qmaUnaryExtend_output_energy,
    qmaUnaryExtend_propagation_energy,zero_add]
  rfl

theorem qmaIdealHistory_distributed_energy (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val) (qmaIdealHistory c hc psi) =
      ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaDistributedHistoryEnergy,qmaIdealHistory_distributed_input c hc τ hi,
    qmaIdealHistory_propagation]
  simp only [mul_zero,add_zero,qmaOutputPenalty,qmaIdealHistory,qmaPrefixMatrix_length,
    qmaRejectVector,qmaOutputVector]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distributed-input history is an actual Hermitian matrix on all unary strings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaUnaryDistributedDiagonal_form (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))) u =
      qmaUnaryDistributedInput c τ u := by
  rw [qmaQuadratic_diagonal_real]
  simp only [qmaUnaryDistributedDiagonal,Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,
    qmaUnaryDistributedInput]

theorem qmaUnaryDistributedHamiltonian_form (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) u = qmaUnaryDistributedEnergy c τ u := by
  unfold qmaUnaryDistributedHamiltonian
  rw [qmaQuadratic_add,qmaQuadratic_add,qmaQuadratic_add]
  have hs : ((14*(c.work+1)+8)*c.gates.length:ℂ) =
      (((14*(c.work+1)+8)*c.gates.length:ℝ):ℂ) := by push_cast; rfl
  rw [hs,show (14:ℂ) = ((14:ℝ):ℂ) from rfl,qmaQuadratic_smul,qmaQuadratic_smul,
    qmaUnaryDistributedDiagonal_form,qmaQuadratic_diagonal_real,
    qmaQuadratic_diagonal_real,qmaUnaryPropagationMatrix_form]
  simp only [qmaUnaryDistributedEnergy,qmaUnaryClockEnergy,qmaUnaryOutputEnergy,
    qmaUnaryClockDiagonal,qmaUnaryOutputDiagonal,Fintype.sum_prod_type,
    ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.mul_sum]

theorem qmaUnaryDistributedInput_reindex (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    ((14:ℂ) • Matrix.diagonal (fun p => (qmaUnaryDistributedDiagonal c τ p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      ∑ i : Fin (c.work+1), qmaDistributedInputTerm c τ i := by
  rw [qmaSubmatrix_smul,Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,qmaDistributedInputTerm,
      Matrix.diagonal_apply_eq,qmaUnaryDistributedDiagonal,Complex.ofReal_sum,Function.comp_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : (qmaCircuitQubitSplit c s).1 = s ∘ Sum.inl := rfl
    have hr : (qmaCircuitQubitSplit c s).2 = s ∘ Sum.inr := rfl
    rw [hs,hr]
    by_cases hp : qmaClockAt c.gates.length (τ i) (s ∘ Sum.inl) ∧
      qmaInputCheck c i (s ∘ Sum.inr)
    · simp [hp]
    · simp [hp]
  · simp [Matrix.smul_apply,h,Matrix.sum_apply,qmaDistributedInputTerm]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedSpectrum
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distributed-input Hamiltonian retains the verifier's inverse-polynomial gap. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaDistributedHistoryVector_energy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (fun p => qmaHistoryVector c u p)) =
      qmaDistributedHistoryEnergy c (fun i => (τ i).val) u := by
  unfold qmaDistributedHistoryEnergy qmaOutputPenalty qmaDistributedInput
  rw [qmaHistoryVector_propagation,qmaHistoryVector_slice c u c.gates.length le_rfl]
  simp_rw [qmaHistoryVector_slice c u (τ _).val (Nat.le_of_lt_succ (τ _).isLt)]

theorem qmaUnaryDistributedHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMAUnaryBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) := by
  rw [qmaUnaryDistributedHamiltonian_form,←qmaUnaryMass_norm]
  exact qmaUnaryDistributedEnergy_sound c hc τ hi hsound (fun p => u p)

theorem qmaUnaryDistributedHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMAUnaryBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*
        qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) ≤ 1 := by
  let v := qmaHistoryVector c (qmaIdealHistory c hc psi)
  let w : EuclideanSpace ℂ (QMAUnaryBasis c) := WithLp.toLp 2 (qmaUnaryExtend c (fun p => v p))
  have hw : ‖w‖^2 = (c.gates.length+1:ℝ) := by
    rw [←qmaUnaryMass_norm]
    change qmaUnaryMass c (qmaUnaryExtend c (fun p => v p)) = _
    rw [qmaUnaryExtend_mass]
    have hv := qmaHistoryVector_norm c (qmaIdealHistory c hc psi)
    rw [qmaIdealHistory_mass,hpsi] at hv
    simpa only [v,EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow,mul_one] using hv
  have he : qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) =
      ‖qmaRejectVector c hc psi‖^2 := by
    rw [qmaUnaryDistributedHamiltonian_form]
    change qmaUnaryDistributedEnergy c τ (qmaUnaryExtend c (fun p => v p)) = _
    rw [qmaUnaryExtend_distributed_energy]
    change qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (fun p => qmaHistoryVector c (qmaIdealHistory c hc psi) p)) = _
    rw [qmaDistributedHistoryVector_energy,qmaIdealHistory_distributed_energy c hc τ hi]
  have hn : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hw
    have hp : (0:ℝ) < c.gates.length+1 := by positivity
    norm_num at hw
    linarith
  let u := ((‖w‖⁻¹:ℝ):ℂ) • w
  refine ⟨u,by simp [u,norm_smul,hn],?_⟩
  have hq : qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) =
      (‖w‖⁻¹)^2*qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) := by
    exact qmaQuadratic_vector_smul _ _ _
  have hb : 3*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) ≤ ‖w‖^2 := by
    rw [he,hw]
    have h := mul_le_mul_of_nonneg_left (qmaRejectVector_of_accept c hc psi hpsi hacc)
      (by positivity : 0 ≤ 3*(c.gates.length+1:ℝ))
    nlinarith
  have h := mul_le_mul_of_nonneg_left hb (sq_nonneg (‖w‖⁻¹))
  have heq : (‖w‖⁻¹)^2*‖w‖^2 = 1 := by field_simp
  rw [hq]
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linear-size, five-local term family with distributed initialization checks. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaDistributedQubitHamiltonian_decomposition (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    qmaDistributedQubitHamiltonian c τ =
      ((∑ i : Fin (c.gates.length+1), qmaClockFaultTerm c i)+qmaClockLeftTerm c+qmaClockRightTerm c)+
      qmaOutputTerm c+(∑ i : Fin (c.work+1), qmaDistributedInputTerm c τ i)+
      ((14*(c.work+1)+8)*c.gates.length:ℂ) • ∑ t : Fin c.gates.length,
        (qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t := by
  unfold qmaDistributedQubitHamiltonian qmaUnaryDistributedHamiltonian
  simp only [qmaSubmatrix_add]
  rw [qmaUnaryClockDiagonal_reindex,qmaUnaryOutputDiagonal_reindex,
    qmaUnaryDistributedInput_reindex,qmaSubmatrix_smul,qmaUnaryPropagationGram_reindex]

theorem qmaDistributedTerm_sum (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (∑ t : QMACircuitTerm c, qmaDistributedTermMatrix c τ t) =
      qmaDistributedQubitHamiltonian c τ := by
  rw [qmaDistributedQubitHamiltonian_decomposition]
  have h10 : (1:Fin 2) ≠ 0 := by decide
  simp only [Fintype.sum_sum_type,qmaDistributedTermMatrix,Fin.sum_univ_two,
    Fin.isValue,ite_true, if_true,h10,ite_false, if_false,Finset.univ_unique,Finset.sum_singleton,
    ←Finset.smul_sum]
  ext s t
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing a gate by an exact bounded-length nearest-neighbor gate sequence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaNearestGate_matrix (work : ℕ) (g : QMAGate) :
    qmaGateProduct work (qmaNearestGate work g) = qmaGateMatrix work g := by
  cases g with
  | hadamard i => exact qmaGateProduct_singleton _ _
  | phaseT i => exact qmaGateProduct_singleton _ _
  | controlledNot i j =>
    by_cases h : i < j ∧ j < work+1
    · simp only [qmaNearestGate,dite_eq_left h,qmaAdjacentCnot_matrix,qmaOrderedCnot,ite_true, if_true]
      have he : i+(j-i-1)+1 = j := by omega
      rw [he]
    · by_cases h' : j < i ∧ i < work+1
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_left h',qmaAdjacentCnot_matrix,
          qmaOrderedCnot,Bool.false_eq_true,ite_false, if_false]
        have he : j+(i-j-1)+1 = i := by omega
        rw [he]
      · simp only [qmaNearestGate,dite_eq_right h,dite_eq_right h',qmaGateProduct_singleton]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumNearestCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact nearest-neighbor compilation with an explicit polynomial size bound. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaNearestList_matrix (work : ℕ) (gs : List QMAGate) :
    qmaGateProduct work (gs.flatMap (qmaNearestGate work)) = qmaGateProduct work gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change qmaGateProduct work (qmaNearestGate work g ++ gs.flatMap (qmaNearestGate work)) = _
    rw [qmaGateProduct_append,ih,qmaNearestGate_matrix]
    change _ = qmaGateProduct work ([g]++gs)
    rw [qmaGateProduct_append,qmaGateProduct_singleton]

theorem qmaNearestCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  have hm : qmaCircuitMatrix (qmaNearestCircuit c) = qmaCircuitMatrix c :=
    qmaNearestList_matrix c.work c.gates
  unfold qmaAcceptance
  rw [hm]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed row transfer is independent of the chosen column order. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaRowTransfer_reindex {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin n)) :
    qmaTransferPermutation (qmaRowPairs (l ∘ e) (r ∘ e)) =
      qmaTransferPermutation (qmaRowPairs l r) := by
  have hl' : Function.Injective (l ∘ e) := hl.comp e.injective
  have hr' : Function.Injective (r ∘ e) := hr.comp e.injective
  have hlr' : ∀ i j, (l ∘ e) i ≠ (r ∘ e) j := fun i j => hlr (e i) (e j)
  apply Equiv.ext
  intro k
  by_cases hleft : ∃ i, k = l i
  · obtain ⟨i,rfl⟩ := hleft
    have ht := (qmaRowTransfer_coordinates (l ∘ e) (r ∘ e) hl' hr' hlr' (e.symm i)).1
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,
      (qmaRowTransfer_coordinates l r hl hr hlr i).1] using ht
  by_cases hright : ∃ i, k = r i
  · obtain ⟨i,rfl⟩ := hright
    have ht := (qmaRowTransfer_coordinates (l ∘ e) (r ∘ e) hl' hr' hlr' (e.symm i)).2
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,
      (qmaRowTransfer_coordinates l r hl hr hlr i).2] using ht
  · rw [qmaRowTransfer_fixed (l ∘ e) (r ∘ e) k
      (fun i hi => hleft ⟨e i,hi⟩) (fun i hi => hright ⟨e i,hi⟩),
      qmaRowTransfer_fixed l r k (fun i hi => hleft ⟨i,hi⟩) (fun i hi => hright ⟨i,hi⟩)]

theorem qmaRowTransfer_matrix_reindex {n work : ℕ} (l r : Fin n → Fin (work+1))
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin n)) :
    qmaGateProduct work (qmaTransferGates (qmaRowPairs (l ∘ e) (r ∘ e))) =
      qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) := by
  rw [qmaRowTransfer_matrix (l ∘ e) (r ∘ e) (fun i j => hlr (e i) (e j)),
    qmaRowTransfer_matrix l r hlr,qmaRowTransfer_reindex l r hl hr hlr e]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRowInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logical gate is inserted immediately after its last operand arrives. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaGateCut_site (work : ℕ) (e : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (i : Fin (work+1)) (hi : i ∈ qmaGateSites work g) :
    (e.symm i).val < qmaGateCut work e g := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (e.symm j).val) hi)

theorem qmaRowStage_tail_avoids (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) :
    ∀ k ∈ qmaGateSites work (qmaMapGate width work r g),
      ∀ p ∈ (qmaRowPairs (l ∘ e) (r ∘ e)).drop (qmaGateCut width e g),
        k ≠ p.1 ∧ k ≠ p.2 := by
  intro k hk p hp
  rw [qmaMapGate_sites] at hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨j,hj,hp⟩ := List.mem_drop_iff_getElem.mp hp
  have hj' : qmaGateCut width e g+j < width+1 := by
    simpa only [qmaRowPairs,List.length_ofFn,Nat.add_comm] using hj
  have he : (l (e ⟨qmaGateCut width e g+j,hj'⟩),
      r (e ⟨qmaGateCut width e g+j,hj'⟩)) = p := by
    simpa only [qmaRowPairs,List.getElem_ofFn,Function.comp_apply] using hp
  rw [←he]
  refine ⟨(hlr _ i).symm,?_⟩
  intro heq
  have hh := hr heq
  have hcut := qmaGateCut_site width e g i hi
  rw [hh,e.symm_apply_apply] at hcut
  change qmaGateCut width e g+j < qmaGateCut width e g at hcut
  omega

theorem qmaRowStage_matrix (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hl : Function.Injective l)
    (hr : Function.Injective r) (hlr : ∀ i j, l i ≠ r j)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) (hg : g.WellFormed (width+1)) :
    qmaGateProduct work (qmaRowStage width work l r e g) =
      qmaGateMatrix work (qmaMapGate width work r g)*
        qmaGateProduct work (qmaTransferGates (qmaRowPairs l r)) := by
  unfold qmaRowStage
  rw [qmaTransfer_insert_gate _ _
    (fun p hp => qmaRowPairs_distinct (l ∘ e) (r ∘ e)
      (fun i j => hlr (e i) (e j)) p (List.mem_of_mem_drop hp))
    _ (qmaMapGate_wellFormed width work r hr g hg)
    (qmaRowStage_tail_avoids width work l r hr hlr e g),
    List.take_append_drop,qmaRowTransfer_matrix_reindex l r hl hr hlr e]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCircuit
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternating row sweeps with gates inserted at the arrival of their operands. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaSweepCircuitFrom_matrix (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    qmaGateProduct (qmaGridWork rows width) (qmaSweepCircuitFrom rows width start gs h) =
      qmaGateProduct (qmaGridWork rows width) (qmaGridCircuitFrom rows width start gs h) := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    simp only [qmaSweepCircuitFrom,qmaGridCircuitFrom,qmaGateProduct_append,
      qmaGateProduct_singleton]
    rw [ih (start+1) ht (fun k hk => hg k (by simp [hk]))]
    have hstage := qmaRowStage_matrix width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaGridRow_injective rows width _) (qmaGridRow_injective rows width _)
      (qmaGridRows_disjoint rows width _ _ (by intro he; have := congrArg Fin.val he; simp at this))
      (qmaSweepOrder width (rows-1-start)) g (hg g (by simp))
    rw [hstage]
    rfl

theorem qmaSweepCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaSweepCircuit c) (qmaSweepCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  have hm : qmaCircuitMatrix (qmaSweepCircuit c) = qmaCircuitMatrix (qmaGridCircuit c) :=
    qmaSweepCircuitFrom_matrix _ _ _ _ _ hc.2
  calc
    _ = qmaAcceptance (qmaGridCircuit c) (qmaGridCircuit_wellFormed c hc) psi := by
      unfold qmaAcceptance
      rw [hm]
      rfl
    _ = _ := qmaGridCircuit_acceptance c hc psi

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGridLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete polynomial-size verifier with geometrically local computation gates. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaSparseCircuit c) (qmaSparseCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  rw [qmaSweepCircuit_acceptance (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc),
    qmaNearestCircuit_acceptance c hc]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceWalls
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nearest-neighbor reference chain has only two zero-wall sectors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaReferenceWalls_zero_iff (n : ℕ) (s : SourceSpinBasis (n+1)) :
    qmaReferenceWalls n s = 0 ↔ ∀ i, s i = s 0 := by
  constructor
  · intro h
    have he : Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) = ∅ :=
      Finset.card_eq_zero.mp h
    have hadj (i : Fin n) : s i.castSucc = s i.succ := by
      by_contra hn
      have hm : i ∈ Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) := by
        simp [hn]
      rw [he] at hm
      exact Finset.notMem_empty i hm
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).symm.trans ih
  · intro h
    unfold qmaReferenceWalls
    have he : Finset.univ.filter (fun i : Fin n => s i.castSucc ≠ s i.succ) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hn
      exact hn ((h i.castSucc).trans (h i.succ).symm)
    rw [he]
    rfl

theorem qmaReferenceWalls_constant (n : ℕ) (b : Fin 2) :
    qmaReferenceWalls n (fun _ => b) = 0 :=
  (qmaReferenceWalls_zero_iff n _).mpr (by intro i; rfl)

theorem qmaReferenceWalls_pos (n : ℕ) (s : SourceSpinBasis (n+1))
    (hs : ¬∀ i, s i = s 0) : 1 ≤ qmaReferenceWalls n s := by
  have hn : qmaReferenceWalls n s ≠ 0 := fun h => hs ((qmaReferenceWalls_zero_iff n s).mp h)
  omega

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTensor
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact diagonal tensors and the computational-basis reference-chain penalty. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaZSign_wall (a b : Fin 2) :
    (1/2 : ℂ)*(1-qmaZSign a*qmaZSign b) = if a = b then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [qmaZSign]

theorem qmaReferenceZPenalty_diagonal (n : ℕ) :
    qmaReferenceZPenalty n = qmaReferenceWallMatrix n := by
  unfold qmaReferenceZPenalty
  simp_rw [sourceLocalPauli_z_diagonal,Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases h : s = t
  · subst t
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,
      Matrix.one_apply_eq,Matrix.diagonal_apply_eq,qmaReferenceWallMatrix]
    simp_rw [qmaZSign_wall]
    simp [qmaReferenceWalls,Finset.card_filter]
  · simp [Matrix.sum_apply,Matrix.smul_apply,qmaReferenceWallMatrix,h]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferencePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nearest-neighbor real YY penalty has a unit complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaReferenceYPenalty_diagonalized (n : ℕ) :
    (qmaReferenceTensor (n+1)).conjTranspose*qmaReferenceYPenalty n*
      qmaReferenceTensor (n+1) = qmaReferenceWallMatrix n := by
  unfold qmaReferenceYPenalty
  rw [Matrix.mul_sum,Matrix.sum_mul]
  simp_rw [qmaReferenceYEdge_diagonalized]
  exact qmaReferenceZPenalty_diagonal n

theorem qmaQuadratic_change_basis {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix α β ℂ) (M : Matrix α α ℂ) (u : β → ℂ) :
    qmaQuadratic (B.conjTranspose*M*B) u = qmaQuadratic M (B.mulVec u) := by
  unfold qmaQuadratic
  rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceBlocks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sector decomposition for distributed realification. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem qmaReferenceBlocks_quadratic (n : ℕ) (B : SourceSpinBasis n → Matrix α α ℂ)
    (u : SourceSpinBasis n × α → ℂ) :
    qmaQuadratic (qmaReferenceBlocks n B) u =
      ∑ s, qmaQuadratic (B s) (fun a => u (s,a)) := by
  simp [qmaQuadratic,qmaReferenceBlocks,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Complex.re_sum]

omit [Fintype α] [DecidableEq α] in
theorem qmaReferenceBlocks_sum {κ : Type*} [Fintype κ] (n : ℕ)
    (B : κ → SourceSpinBasis n → Matrix α α ℂ) :
    qmaReferenceBlocks n (fun s => ∑ j, B j s) = ∑ j, qmaReferenceBlocks n (B j) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases h : s = t <;> simp [qmaReferenceBlocks,Matrix.sum_apply,h]

theorem qmaReferencePenalty_blocks (n : ℕ) :
    (qmaReferenceExtension (α := α) (n+1)).conjTranspose*
      (qmaReferenceYPenalty n ⊗ₖ (1 : Matrix α α ℂ))*
        qmaReferenceExtension (α := α) (n+1) =
    qmaReferenceBlocks (n+1) (fun s => (qmaReferenceWalls n s : ℂ) • (1 : Matrix α α ℂ)) := by
  unfold qmaReferenceExtension
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  simp only [←Matrix.mul_kronecker_mul,one_mul,qmaReferenceYPenalty_diagonalized]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t
  · subst t
    simp [qmaReferenceWallMatrix,qmaReferenceBlocks]
  · simp [qmaReferenceWallMatrix,qmaReferenceBlocks,hs]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceFamily
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete distributed reference Hamiltonian and its exact sector matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaReferenceFamily_diagonalized (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    (qmaReferenceExtension (α := α) (n+1)).conjTranspose*qmaReferenceFamily n A Δ*
      qmaReferenceExtension (α := α) (n+1) =
    qmaReferenceBlocks (n+1) (qmaReferenceSector n A Δ) := by
  unfold qmaReferenceFamily
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,mul_smul_comm,smul_mul_assoc]
  simp_rw [qmaDistributedRebitTerm_blocks]
  rw [qmaReferencePenalty_blocks]
  rw [←qmaReferenceBlocks_sum]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t <;>
    simp [qmaReferenceBlocks,qmaReferenceSector,hs,mul_assoc]

omit [Fintype α] in
theorem qmaReferenceSector_one (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    qmaReferenceSector n A Δ (fun _ => 1) = ∑ i, A i := by
  simp [qmaReferenceSector,qmaReferenceWalls_constant,qmaReferenceSectorTerm]

omit [Fintype α] in
theorem qmaReferenceSector_zero (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    qmaReferenceSector n A Δ (fun _ => 0) = qmaConjugateMatrix (∑ i, A i) := by
  ext a b
  simp [qmaReferenceSector,qmaReferenceWalls_constant,qmaReferenceSectorTerm,qmaConjugateMatrix,Matrix.sum_apply]

omit [DecidableEq α] in
theorem qmaConjugate_quadratic (A : Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (qmaConjugateMatrix A) u = qmaQuadratic A (fun a => star (u a)) := by
  unfold qmaConjugateMatrix
  have he : star u ⬝ᵥ Matrix.mulVec (fun a b => star (A a b)) u =
      star (star (fun a => star (u a)) ⬝ᵥ A.mulVec (fun a => star (u a))) := by
    simp [dotProduct,Matrix.mulVec]
  unfold qmaQuadratic
  rw [he]
  simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceLower
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive local history terms make a constant-strength reference penalty sufficient. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem qmaQuadratic_sum {κ : Type*} [Fintype κ] (A : κ → Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (∑ i, A i) u = ∑ i, qmaQuadratic (A i) u := by
  have h (s : Finset κ) : qmaQuadratic (∑ i ∈ s, A i) u = ∑ i ∈ s, qmaQuadratic (A i) u := by
    classical
    induction s using Finset.induction with
    | empty => simp [qmaQuadratic]
    | @insert i s hi ih => simp only [Finset.sum_insert hi,qmaQuadratic_add,ih]
  exact h Finset.univ

theorem qmaQuadratic_identity (u : α → ℂ) :
    qmaQuadratic (1 : Matrix α α ℂ) u = ∑ i, Complex.normSq (u i) := by
  simp [qmaQuadratic,dotProduct,Complex.mul_re,Complex.normSq_apply]

omit [DecidableEq α] in
theorem qmaReferenceSector_nonnegative (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (s : SourceSpinBasis (n+1)) (u : α → ℂ) :
    0 ≤ qmaQuadratic (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s) u := by
  rw [qmaQuadratic_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases hs : s i = 0
  · rw [qmaReferenceSectorTerm,ite_eq_left hs,qmaConjugate_quadratic]
    exact hpos i _
  · rw [qmaReferenceSectorTerm,ite_eq_right hs]
    exact hpos i u

theorem qmaReferenceSector_lower (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : a ≤ Δ)
    (hA : ∀ u, a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (∑ i, A i) u)
    (s : SourceSpinBasis (n+1)) (u : α → ℂ) :
    a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ s) u := by
  have hm : 0 ≤ ∑ i, Complex.normSq (u i) := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  by_cases hs : ∀ i, s i = s 0
  · have he : s = fun _ => s 0 := funext hs
    rw [he]
    generalize hb : s 0 = b
    fin_cases b
    · change a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ (fun _ => 0)) u
      rw [qmaReferenceSector_zero,qmaConjugate_quadratic]
      simpa using hA (fun i => star (u i))
    · change a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (qmaReferenceSector n A Δ (fun _ => 1)) u
      rw [qmaReferenceSector_one]
      exact hA u
  · have hw : (1:ℝ) ≤ qmaReferenceWalls n s := by exact_mod_cast qmaReferenceWalls_pos n s hs
    have hp := qmaReferenceSector_nonnegative n A hpos s u
    have he : qmaQuadratic (qmaReferenceSector n A Δ s) u =
        qmaQuadratic (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s) u+
          Δ*(qmaReferenceWalls n s:ℝ)*(∑ i, Complex.normSq (u i)) := by
      rw [qmaReferenceSector,qmaQuadratic_add]
      have hc : (Δ:ℂ)*(qmaReferenceWalls n s:ℂ) = ((Δ*(qmaReferenceWalls n s:ℝ):ℝ):ℂ) := by simp
      rw [hc,qmaQuadratic_smul,qmaQuadratic_identity]
    rw [he]
    have hΔ0 : 0 ≤ Δ := ha.trans hΔ
    have hg : a ≤ Δ*(qmaReferenceWalls n s:ℝ) := by nlinarith
    exact (mul_le_mul_of_nonneg_right hg hm).trans (le_add_of_nonneg_left hp)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedPositive
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every concrete distributed-history term is positive semidefinite. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaDistributedTerm_nonnegative (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c)
    (u : (QMACircuitQubit c → Fin 2) → ℂ) :
    0 ≤ qmaQuadratic (qmaDistributedTermMatrix c τ t) u := by
  rcases t with i | (b | (i | (v | t)))
  · change 0 ≤ qmaQuadratic (qmaClockFaultTerm c i) u
    unfold qmaClockFaultTerm qmaPairDiagonal
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · fin_cases b
    · change 0 ≤ qmaQuadratic (qmaClockLeftTerm c) u
      unfold qmaClockLeftTerm qmaBitDiagonal
      simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> simp [Complex.mul_re]
      all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
    · change 0 ≤ qmaQuadratic (qmaClockRightTerm c) u
      unfold qmaClockRightTerm qmaBitDiagonal
      simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> simp [Complex.mul_re]
      all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (qmaDistributedInputTerm c τ i) u
    unfold qmaDistributedInputTerm
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (qmaOutputTerm c) u
    unfold qmaOutputTerm qmaPairDiagonal
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)) u
    have he : ((14*(c.work+1)+8)*c.gates.length:ℂ) =
        (((14*(c.work+1)+8)*c.gates.length:ℝ):ℂ) := by push_cast; rfl
    rw [he,qmaQuadratic_smul,qmaQuadratic_gram]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space variational comparison for the actual distributed reference family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaReferenceExtension_mass (n : ℕ) (u : SourceSpinBasis n × α → ℂ) :
    (∑ p, Complex.normSq ((qmaReferenceExtension (α := α) n).mulVec u p)) =
      ∑ p, Complex.normSq (u p) := by
  rw [←qmaQuadratic_gram,qmaReferenceExtension_gram,qmaQuadratic_identity]

theorem qmaReferenceFamily_lower (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : a ≤ Δ)
    (hA : ∀ u, a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (∑ i, A i) u)
    (u : SourceSpinBasis (n+1) × α → ℂ) :
    a*(∑ p, Complex.normSq (u p)) ≤ qmaQuadratic (qmaReferenceFamily n A Δ) u := by
  let B := qmaReferenceExtension (α := α) (n+1)
  let v := B.conjTranspose.mulVec u
  have hv : B.mulVec v = u := by
    change B.mulVec (B.conjTranspose.mulVec u) = u
    rw [Matrix.mulVec_mulVec,qmaReferenceExtension_cogram,Matrix.one_mulVec]
  have hm : (∑ p, Complex.normSq (v p)) = ∑ p, Complex.normSq (u p) := by
    rw [←hv,qmaReferenceExtension_mass]
  calc
    _ = ∑ s, a*(∑ i, Complex.normSq (v (s,i))) := by
      rw [←hm,Fintype.sum_prod_type,Finset.mul_sum]
    _ ≤ ∑ s, qmaQuadratic (qmaReferenceSector n A Δ s) (fun i => v (s,i)) :=
      Finset.sum_le_sum (fun s _ => qmaReferenceSector_lower n A hpos a Δ ha hΔ hA s _)
    _ = qmaQuadratic (qmaReferenceBlocks (n+1) (qmaReferenceSector n A Δ)) v :=
      (qmaReferenceBlocks_quadratic _ _ _).symm
    _ = qmaQuadratic (qmaReferenceFamily n A Δ) (B.mulVec v) := by
      rw [←qmaReferenceFamily_diagonalized,qmaQuadratic_change_basis]
    _ = _ := by rw [hv]

theorem qmaReferenceTrial_energy (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (Δ : ℝ) (u : α → ℂ) :
    qmaQuadratic (qmaReferenceFamily n A Δ) (qmaReferenceTrial n u) =
      qmaQuadratic (∑ i, A i) u := by
  unfold qmaReferenceTrial
  rw [←qmaQuadratic_change_basis,qmaReferenceFamily_diagonalized,qmaReferenceBlocks_quadratic]
  rw [Finset.sum_eq_single (fun _ => (1:Fin 2))]
  · simp only [ite_true, if_true,qmaReferenceSector_one]
  · intro s _ hs
    simp only [hs,ite_false, if_false]
    simp [qmaQuadratic,Matrix.mulVec,dotProduct]
  · simp

theorem qmaReferenceTrial_mass (n : ℕ) (u : α → ℂ) :
    (∑ p, Complex.normSq (qmaReferenceTrial n u p)) = ∑ i, Complex.normSq (u i) := by
  unfold qmaReferenceTrial
  rw [qmaReferenceExtension_mass,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (fun _ => (1:Fin 2))]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumQuadraticReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of finite quadratic forms and masses under a basis equivalence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_reindex_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix β β ℂ) (u : α → ℂ) :
    qmaQuadratic (M.submatrix e e) u = qmaQuadratic M (u ∘ e.symm) := by
  have hm := Matrix.submatrix_mulVec_equiv M u e e
  unfold qmaQuadratic
  rw [hm]
  have he := e.sum_comp (fun j => star (u (e.symm j))*M.mulVec (u ∘ e.symm) j)
  simp only [Equiv.symm_apply_apply] at he
  exact congrArg Complex.re he

theorem qmaMass_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u : α → ℂ) :
    (∑ i, Complex.normSq (u (e.symm i))) = ∑ i, Complex.normSq (u i) :=
  e.symm.sum_comp (fun i => Complex.normSq (u i))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDistributedGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.HubbardGlobal.fockCoordinates_assemble _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_fresh _root_.OAI.ContinuumCoulomb.MediatorGraph.basisEquiv_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distributed history bounds transported to the actual tensor-qubit basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaDistributedQubit_lower (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : (QMACircuitQubit c → Fin 2) → ℂ) :
    (2/(5*(c.gates.length+1:ℝ)))*(∑ i, Complex.normSq (u i)) ≤
      qmaQuadratic (qmaDistributedQubitHamiltonian c τ) u := by
  let e := qmaCircuitQubitSplit c
  have h := qmaUnaryDistributedHamiltonian_sound c hc τ hi hsound
    (WithLp.toLp 2 (u ∘ e.symm))
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm] at h
  have hm : (∑ i, Complex.normSq ((u ∘ e.symm) i)) = ∑ i, Complex.normSq (u i) :=
    qmaMass_reindex e u
  rw [hm] at h
  unfold qmaDistributedQubitHamiltonian
  rw [qmaQuadratic_reindex_equiv]
  have hd : 0 < 5*(c.gates.length+1:ℝ) := by positivity
  calc
    _ = (2*(∑ i, Complex.normSq (u i)))/(5*(c.gates.length+1:ℝ)) := by ring
    _ ≤ _ := (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using h)

theorem qmaDistributedQubit_accepting (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : (QMACircuitQubit c → Fin 2) → ℂ,
      (∑ i, Complex.normSq (u i)) = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaDistributedQubitHamiltonian c τ) u ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaUnaryDistributedHamiltonian_accepting c hc τ hi psi hpsi hacc
  let e := qmaCircuitQubitSplit c
  refine ⟨(fun s => v (e s)),?_,?_⟩
  · have hm := e.sum_comp (fun p => Complex.normSq (v p))
    rw [hm]
    have hn := congrArg (fun t : ℝ => t^2) hv
    simpa only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow] using hn
  · unfold qmaDistributedQubitHamiltonian
    rw [qmaQuadratic_reindex_equiv]
    have hh : (fun s => v (e s)) ∘ e.symm = fun p => v p := by funext p; simp
    rw [hh]
    exact he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full reference Hamiltonian as explicit bounded-support real terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaReferenceTerm_sum (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    (∑ t, qmaReferenceTermMatrix n A t) = qmaReferenceOnQubits n A := by
  ext s t
  simp only [Fintype.sum_sum_type,Matrix.add_apply,Matrix.sum_apply,qmaReferenceTermMatrix,
    qmaReferenceOnQubits,qmaReferenceFamily,Matrix.submatrix_apply,Complex.ofReal_one,one_smul,qmaReferenceYPenalty]
  change (∑ i, qmaDistributedRebitOnQubits (n+1) i (A i) s t)+
    (∑ i, qmaReferenceEdgeOnQubits n i s t) =
    (∑ i, qmaDistributedRebitOnQubits (n+1) i (A i) s t)+
    ((∑ i, qmaReferenceYEdge n i) (s ∘ Sum.inl) (t ∘ Sum.inl))*
      (1 : Matrix (ι → Fin 2) _ ℂ) (s ∘ Sum.inr) (t ∘ Sum.inr)
  simp only [Matrix.sum_apply,Finset.sum_mul]
  rfl

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reordering actual history terms preserves the full-space reference gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaOrderedReferenceTerms_sum (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (∑ i, qmaOrderedReferenceTerms c hT τ i) = qmaDistributedQubitHamiltonian c τ := by
  unfold qmaOrderedReferenceTerms
  rw [(qmaOrderedTermEquiv c hT τ).sum_comp,qmaDistributedTerm_sum]

theorem qmaOrderedReferenceHistory_lower (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < c.gates.length) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : QMAHistoryReferenceBasis c → ℂ) :
    (2/(5*(c.gates.length+1:ℝ)))*(∑ p, Complex.normSq (u p)) ≤
      qmaQuadratic (qmaOrderedReferenceHistory c hT τ) u := by
  have hd : 0 < 5*(c.gates.length+1:ℝ) := by positivity
  have ha : (2:ℝ)/(5*(c.gates.length+1:ℝ)) ≤ 1 := by
    apply (div_le_one hd).mpr
    have : (0:ℝ) ≤ c.gates.length := Nat.cast_nonneg _
    linarith
  apply qmaReferenceFamily_lower _ _ (fun i => qmaDistributedTerm_nonnegative c τ _) _ _
    (by positivity) ha
  intro v
  change _ ≤ qmaQuadratic (∑ i, qmaOrderedReferenceTerms c hT τ i) v
  rw [qmaOrderedReferenceTerms_sum]
  exact qmaDistributedQubit_lower c hc τ hi hsound v

theorem qmaOrderedReferenceHistory_accepting (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < c.gates.length) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : QMAHistoryReferenceBasis c → ℂ, (∑ p, Complex.normSq (u p)) = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaOrderedReferenceHistory c hT τ) u ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaDistributedQubit_accepting c hc τ hi psi hpsi hacc
  refine ⟨qmaReferenceTrial (qmaHistoryReferenceWork c) v,?_,?_⟩
  · rw [qmaReferenceTrial_mass]
    exact hv
  · unfold qmaOrderedReferenceHistory
    rw [qmaReferenceTrial_energy,qmaOrderedReferenceTerms_sum]
    exact he

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedModel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time-ordered real six-local model retains both verifier bounds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaOrderedHistoryModel_sum (c : QMACircuit) (hT : 0 < c.gates.length) :
    (∑ t, (qmaOrderedHistoryModel c hT).matrix t) =
      qmaReferenceOnQubits (qmaHistoryReferenceWork c)
        (qmaOrderedReferenceTerms c hT (qmaFirstUseTime c)) :=
  qmaReferenceTerm_sum _ _

theorem qmaOrderedHistoryModel_yes (c : QMACircuit) (hT : 0 < c.gates.length) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    (qmaOrderedHistoryModel c hT).energy ≤ 1/(3*(c.gates.length+1:ℝ)) := by
  obtain ⟨v,hv,he⟩ := qmaOrderedReferenceHistory_accepting c hc hT (qmaFirstUseTime c)
    (qmaFirstUse_untouched c) psi hpsi hacc
  let e := Equiv.sumArrowEquivProdArrow (Fin (qmaHistoryReferenceWork c+1))
    (QMACircuitQubit c) (Fin 2)
  let u : EuclideanSpace ℂ ((Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c) → Fin 2) :=
    WithLp.toLp 2 (v ∘ e)
  have hu : ‖u‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    simp only [u,EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow]
    exact (e.sum_comp (fun p => Complex.normSq (v p))).trans hv
  unfold QMARealLocalModel.energy
  rw [qmaOrderedHistoryModel_sum]
  apply (qmaNormalizedBottom_le _ u hu).trans
  have hq : qmaQuadratic (qmaReferenceOnQubits (qmaHistoryReferenceWork c)
      (qmaOrderedReferenceTerms c hT (qmaFirstUseTime c))) (fun p => u p) =
      qmaQuadratic (qmaOrderedReferenceHistory c hT (qmaFirstUseTime c)) v :=
    qmaQuadratic_reindex e _ v
  rw [hq]
  exact (le_div_iff₀ (by positivity : 0 < 3*(c.gates.length+1:ℝ))).mpr (by linarith)

theorem qmaOrderedHistoryModel_no (c : QMACircuit) (hT : 0 < c.gates.length) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    2/(5*(c.gates.length+1:ℝ)) ≤ (qmaOrderedHistoryModel c hT).energy := by
  unfold QMARealLocalModel.energy
  rw [qmaOrderedHistoryModel_sum]
  apply le_qmaNormalizedBottom _ (EuclideanSpace.single (fun _ => (0:Fin 2)) (1:ℂ))
    (by simp [PiLp.norm_single])
  intro u hu
  change EuclideanSpace ℂ ((Fin (qmaHistoryReferenceWork c+1) ⊕ QMACircuitQubit c) → Fin 2) at u
  have hu1 : ‖u‖ = 1 := hu
  let e := Equiv.sumArrowEquivProdArrow (Fin (qmaHistoryReferenceWork c+1))
    (QMACircuitQubit c) (Fin 2)
  have h := qmaOrderedReferenceHistory_lower c hc hT (qmaFirstUseTime c) (qmaFirstUse_untouched c)
    hsound ((fun p => u p) ∘ e.symm)
  have hm : (∑ p, Complex.normSq (((fun q => u q) ∘ e.symm) p)) = 1 := by
    change (∑ p, Complex.normSq (u (e.symm p))) = 1
    rw [qmaMass_reindex e (fun p => u p)]
    calc
      _ = ‖u‖^2 := by
        simpa only [Complex.sq_norm] using (EuclideanSpace.norm_sq_eq u).symm
      _ = 1 := by rw [hu1]; norm_num
  rw [hm,mul_one] at h
  change _ ≤ qmaQuadratic ((qmaOrderedReferenceHistory c hT (qmaFirstUseTime c)).submatrix e e) (fun p => u p)
  rw [qmaQuadratic_reindex_equiv]
  exact h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumAlgebraicHistory
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

theorem value_identity {α : Type} [DecidableEq α] (s t : α) :
    value (identity s t) = (1 : Matrix α α ℂ) s t := by
  by_cases h : s = t <;> simp [identity,Matrix.one_apply,h]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedArmProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal evaluation and enumeration of the three buffered endpoint arms.
The lane color is unary, as required by the polynomial geometric size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedArmProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

 theorem length_eq (colors : Fin 3 → ℕ) (a : Fin 3) :
    qmaBufferedArmLength colors (fun _ => false) a = length a (colors a) := by
  simp only [qmaBufferedArmLength,qmaBufferedPort,qmaBufferedOffset,Bool.false_eq_true,
    ite_false, if_false,length,qmaBufferedDoglegLength]
  split_ifs <;> omega

end ContinuumCoulomb.QuantumBufferedArmProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSingletStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted multi-terminal singlet stars for the lattice routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaHeisenberg_symm (n : ℕ) (i j : Fin n) :
    sourceHeisenbergMatrix n i j = sourceHeisenbergMatrix n j i := by
  unfold sourceHeisenbergMatrix sourceSpinSwap
  rw [Equiv.swap_comm i j]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkErasure
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse route's library loop erasure is the explicit right-to-left
finite-list algorithm. This identifies the actual path data needed by the
literal spatial compiler. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb
namespace QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram

variable {α : Type} [DecidableEq α]

variable {G : SimpleGraph α} {a b c : α}

private theorem support_dropUntil (p : G.Walk a b) (h : c ∈ p.support) :
    (p.dropUntil c h).support = p.support.drop (p.support.idxOf c) := by
  have hi := List.idxOf_lt_length_of_mem h
  have hs := p.length_support
  have hib : p.support.idxOf c ≤ p.length := by omega
  rw [SimpleGraph.Walk.dropUntil_eq_drop,SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,Nat.min_eq_left hib]

theorem support_bypass (p : G.Walk a b) : erase p.support = p.bypass.support := by
  induction p with
  | nil => simp [erase,step,SimpleGraph.Walk.bypass]
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.support_cons,erase_cons,ih]
    simp only [step,SimpleGraph.Walk.bypass]
    split_ifs with h
    · exact (support_dropUntil p.bypass h).symm
    · rfl

end QuantumWalkErasure

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem bufferedPath_support_explicit
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedPath hd e).val.support =
      QuantumWalkErasure.erase (M.bufferedWalk hd e).support :=
  (QuantumWalkErasure.support_bypass (M.bufferedWalk hd e)).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumWalkSupport
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_energy _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_qubit_index _root_.OAI.ContinuumCoulomb.QMASpatialExchangeModel.withOrdinalSlots_term_index _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual buffered walk is a finite list of explicit arm and Manhattan
points. Loop erasure therefore computes the path used by the port geometry. -/

noncomputable section
namespace ContinuumCoulomb

 theorem qmaGridWalk_support_list (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaGridWalk p L hstep).support = (List.range (L+1)).map p := by
  induction L generalizing p with
  | zero => simp [qmaGridWalk]
  | succ L ih =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_cons,ih,List.range_succ_eq_map,
      List.map_cons,List.map_map,Function.comp_def]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

@[simp] theorem endpointArmWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    (M.endpointArmWalk hd v e).support = M.endpointArmList hd v e := by
  simp only [endpointArmWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,
    endpointArmList]

@[simp] theorem spacedWalk_support_eq (e : M.Term) :
    (M.spacedWalk e).support = M.spacedList e := by
  simp only [spacedWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,spacedList]

 theorem bufferedWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) : (M.bufferedWalk hd e).support = M.bufferedList hd e := by
  simp only [bufferedWalk,SimpleGraph.Walk.support_append,SimpleGraph.Walk.support_reverse,
    endpointArmWalk_support_eq,spacedWalk_support_eq,bufferedList]

 theorem bufferedPath_support_list (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) :
    (M.bufferedPath hd e).val.support = QuantumWalkErasure.erase (M.bufferedList hd e) := by
  rw [M.bufferedPath_support_explicit,M.bufferedWalk_support_eq]

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumEndpointListProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm list is computed from its ordinal port, lane color and
coarse vertex. All three quantities are supplied by the explicit slot and
incident-rank programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEndpointListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem armList_fin (a : Fin 3) (color : ℕ) :
    armList (a.val,color) = (List.range (QuantumBufferedArmProgram.length a color+1)).map
      (QuantumBufferedArmProgram.point a color) := by
  fin_cases a <;> simp [armList]

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    value B (M.routeVertex v,((M.endpointPorts hd v).assign e).val,(M.laneColor e.val).val) =
      M.endpointArmList hd v e := by
  unfold value
  rw [armList_fin,List.map_map]
  rw [← M.endpointColors_assigned hd v e]
  simp only [QMASpatialExchangeModel.endpointArmList,QMASpatialExchangeModel.endpointArmLength,
    QuantumBufferedArmProgram.length_eq,translate,Function.comp_def]
  rfl

end ContinuumCoulomb.QuantumEndpointListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumManhattanListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the Manhattan segment with an explicit fixed route budget.
The cap makes enumeration polynomial on every input, and disappears for
the spatial routes satisfying the proved length bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumManhattanListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_exact (K : ℕ) (x : Ends) (h : qmaManhattanLength x.1 x.2 ≤ K) :
    value K x = (List.range (qmaManhattanLength x.1 x.2+1)).map (qmaManhattanPoint x.1 x.2) := by
  simp only [value,Nat.min_eq_right h]

end ContinuumCoulomb.QuantumManhattanListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpacedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the bounded Manhattan portion of each actual buffered route.
The horizontal and vertical translations are literal binary arithmetic. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpacedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem point_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) (p : Pair) :
    point B (M.laneColor e).val p = qmaLanePoint (M.spacedColor e) p := rfl

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) :
    value A B ((M.laneColor e).val,M.routeVertex (M.left e),M.routeVertex (M.right e)) =
      M.spacedList e := by
  unfold value
  rw [point_actual,point_actual,QuantumManhattanListProgram.value_exact]
  · rfl
  · exact M.spaced_length e

end ContinuumCoulomb.QuantumSpacedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumBufferedListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal construction and loop erasure of the complete buffered route.
The input consists of two computed fine-grid endpoints, one lane color and
the two computed incident port ranks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B (actualInput M hd e) = M.bufferedList hd e := by
  unfold value actualInput
  rw [QuantumEndpointListProgram.value_actual,QuantumSpacedListProgram.value_actual,
    QuantumEndpointListProgram.value_actual]
  rfl

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    path A B (actualInput M hd e) = (M.bufferedPath hd e).val.support := by
  rw [path,value_actual,M.bufferedPath_support_list]

end ContinuumCoulomb.QuantumBufferedListProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumCircuitPadding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.value_sqrtHalf _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two cancelling Hadamards remove the empty-circuit exception without changing acceptance. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaHadamard_selfAdjoint : qmaHadamard.conjTranspose = qmaHadamard := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qmaHadamard,Matrix.conjTranspose_apply,bellScale_star]

theorem qmaHadamard_square : qmaHadamard*qmaHadamard = 1 := by
  simpa only [qmaHadamard_selfAdjoint] using qmaHadamard_gram

theorem qmaGateMatrix_hadamard_square (work i : ℕ) :
    qmaGateMatrix work (.hadamard i)*qmaGateMatrix work (.hadamard i) = 1 := by
  change sourceTensor _ _*sourceTensor _ _ = _
  rw [sourceTensor_mul,← sourceTensor_one (work+1)]
  congr 1
  funext k
  split_ifs <;> simp [qmaHadamard_square]

theorem qmaNonemptyCircuit_matrix (c : QMACircuit) :
    qmaCircuitMatrix (qmaNonemptyCircuit c) = qmaCircuitMatrix c := by
  change qmaGateProduct c.work (c.gates++[.hadamard 0,.hadamard 0]) = _
  rw [qmaGateProduct_append]
  have hh : qmaGateProduct c.work [.hadamard 0,.hadamard 0] = 1 := by
    simpa only [qmaGateProduct,qmaCircuitMatrix,List.foldl_cons,List.foldl_nil,mul_one] using
      qmaGateMatrix_hadamard_square c.work 0
  rw [hh,one_mul]
  rfl

theorem qmaNonemptyCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  unfold qmaAcceptance
  rw [qmaNonemptyCircuit_matrix]
  rfl

end ContinuumCoulomb

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

theorem siteNumber_injective (c : QMACircuit) : Function.Injective (siteNumber c) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [siteNumber] at h
  all_goals have hi := i.isLt
  all_goals have hj := j.isLt
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))

end ContinuumCoulomb.QuantumOrderedSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySiteProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered gate and propagation support lists. The values agree
with the exact support order used by the local history matrix tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySiteProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem gateLabels_actual (work : ℕ) (g : QMAGate) :
    gateLabels (work,g)=(QuantumOrderedSupport.gateSites work g).map Fin.val := by
  cases g <;> rfl

theorem propagationLabels_actual (c : QMACircuit) (t : Fin c.gates.length) :
    propagationLabels (c,t.val)=
      (QuantumOrderedSupport.propagationSites c t).map (distributedNumber c) := by
  simp only [propagationLabels,gateAt,gateLabels_actual,
    QuantumOrderedSupport.propagationSites,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,distributedNumber,qmaClockLeft,qmaClockMiddle,qmaClockRight]
  rfl

end ContinuumCoulomb.QuantumHistorySiteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem ordered_get (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    (ordered c)[i.val]'(by rw [ordered_length c hT]; exact i.isLt) =
      encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  simp only [ordered_actual c hT,List.getElem_map,qmaOrderedTermEquiv_get]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCoefficient
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

end ContinuumCoulomb.QuantumAlgebraicHistory

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
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDescriptorSites
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The descriptor compiler computes the very same ordered support labels
as the mathematical local-history construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open QuantumHistorySiteProgram

theorem distributedLabels_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    distributedLabels c (encode c a) =
      (QuantumOrderedSupport.distributedSites c (qmaFirstUseTime c) a).map
        (distributedNumber c) := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;>
      simp [distributedLabels,encode,QuantumOrderedSupport.distributedSites,distributedNumber]
  · simp only [distributedLabels,encode]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    rfl
  · simp only [distributedLabels,encode]
    norm_num only
    exact propagationLabels_actual c t

theorem referenceWork_eq (c : QMACircuit) : referenceWork c=qmaHistoryReferenceWork c := rfl

theorem orderedAt_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    orderedAt c i.val = encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  unfold orderedAt
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [ordered_length c hT]; exact i.isLt)]
  exact ordered_get c hT i

theorem number_inr (c : QMACircuit) (q : QMACircuitQubit c) :
    QuantumOrderedSupport.siteNumber c (.inr q)=
      referenceWork c+1+distributedNumber c q := by
  cases q <;> simp [QuantumOrderedSupport.siteNumber,distributedNumber,referenceWork_eq,
    Nat.add_assoc]

theorem rebitLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    rebitLabels c i.val =
      (QuantumOrderedSupport.rawSites c hT (.inl i)).map
        (QuantumOrderedSupport.siteNumber c) := by
  rw [rebitLabels,orderedAt_actual c hT i,distributedLabels_actual]
  simp only [QuantumOrderedSupport.rawSites,List.map_cons,List.map_map,Function.comp_def,
    QuantumOrderedSupport.siteNumber]
  congr 1
  apply List.map_congr_left
  intro q _
  exact (number_inr c q).symm

theorem referenceLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    referenceLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      (QuantumOrderedSupport.rawSites c hT a).map
        (QuantumOrderedSupport.siteNumber c) := by
  cases a with
  | inl i =>
    change (if i.val < referenceWork c+1 then rebitLabels c i.val else _) = _
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact rebitLabels_actual c hT i
  | inr i =>
    change referenceLabels c (qmaHistoryReferenceWork c+1+i.val) = _
    rw [referenceLabels,ite_eq_right (by rw [referenceWork_eq]; omega)]
    simp only [referenceWork_eq,Nat.add_sub_cancel_left,QuantumOrderedSupport.rawSites,
      List.map_cons,List.map_nil,QuantumOrderedSupport.siteNumber,Fin.val_castSucc,Fin.val_succ]

theorem supportLabels_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    supportLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      QuantumOrderedSupport.encodedSites c hT a := by
  rw [supportLabels,referenceLabels_actual c hT a,
    List.dedup_map_of_injective (QuantumOrderedSupport.siteNumber_injective c)]
  rfl

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSupportLookup
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local support coordinates are read by literal label lookup.
This identifies a small matrix input with its zero extension on spectator
qubits, without enumerating the ambient spin basis. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSupportLookup
open ExactQuantumFactoring.BitStackProgram

theorem value_map_get {α : Type} (xs : List α) (hx : xs.Nodup)
    (f : α → ℕ) (hf : Function.Injective f) (s : Fin xs.length → ℕ)
    (i : Fin xs.length) :
    value (f (xs.get i),xs.map f,List.ofFn s)=s i := by
  have hi : i.val < (xs.map f).length := by simpa only [List.length_map] using i.isLt
  have he : (xs.map f)[i.val]'hi = f (xs.get i) := by
    simp only [List.getElem_map,List.get_eq_getElem]
  have hind := (hx.map hf).idxOf_getElem i.val hi
  rw [he] at hind
  unfold value
  rw [hind,List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_not_mem (xs ys : List ℕ) (q : ℕ)
    (hq : q ∉ xs) (hy : ys.length ≤ xs.length) : value (q,xs,ys)=0 := by
  unfold value
  rw [List.idxOf_of_notMem hq,List.drop_eq_nil_of_le hy]
  rfl

open QuantumOrderedSupport
open scoped Classical

private theorem extend_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∈ S) :
    qmaSupportExtend S u q = u ⟨q,hq⟩ :=
  dite_eq_left hq

private theorem extend_not_mem {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : QMASupportBasis S) (q : α) (hq : q ∉ S) :
    qmaSupportExtend S u q = 0 :=
  dite_eq_right hq

theorem support_value (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      (qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q).val := by
  by_cases hq : q ∈ (qmaOrderedHistoryModel c hT).sites a
  · let i := (supportEquiv c hT a).symm ⟨q,hq⟩
    have hi : (sites c hT a).get i=q := by
      have h := congrArg Subtype.val ((supportEquiv c hT a).apply_symm_apply ⟨q,hq⟩)
      exact h
    have hlookup := value_map_get (sites c hT a) (sites_nodup c hT a)
      (siteNumber c) (siteNumber_injective c) (fun j => (s j).val) i
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
        (s i).val := by
      simpa only [encodedSites,supportBits,hi] using hlookup
    exact hv.trans (congrArg Fin.val (extend_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm
  · have hn : siteNumber c q ∉ encodedSites c hT a := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := siteNumber_injective c he
      subst p
      apply hq
      rw [← sites_finset c hT a]
      exact List.mem_toFinset.mpr hp
    have hzero := value_not_mem (encodedSites c hT a) (supportBits c hT a s)
      (siteNumber c q) hn (by simp only [supportBits,List.length_ofFn,
        encodedSites,List.length_map,le_refl])
    have hv : value (siteNumber c q,encodedSites c hT a,supportBits c hT a s) = 0 := by
      exact hzero
    exact hv.trans (congrArg Fin.val (extend_not_mem
      ((qmaOrderedHistoryModel c hT).sites a)
      (fun j => s ((supportEquiv c hT a).symm j)) q hq)).symm

theorem support_readBit (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (sites c hT a).length → Fin 2) (q : Qubit c) :
    readBit (siteNumber c q,encodedSites c hT a,supportBits c hT a s) =
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun i => s ((supportEquiv c hT a).symm i)) q := by
  apply Fin.ext
  change value _ % 2 = _
  rw [support_value]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumSupportLookup

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryBitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal bit reads for the small history tables, and a bounded Boolean
scan.  The register bound is unary; this scan has no spin-configuration loop. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryBitProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar

theorem row_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    row (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a s q

theorem column_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c) :
    column (QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t)
      (QuantumOrderedSupport.siteNumber c q) =
    qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
      (fun i => t ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) q :=
  QuantumSupportLookup.support_readBit c hT a t q

end ContinuumCoulomb.QuantumHistoryBitProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

theorem distributed_entry (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : (encode c a).1<4) (d : Data) :
    QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c) a
      (readRow c d) (readColumn c d) =
    if readRow c d=readColumn c d then rat (weight c (encode c a) d) else rat 0 := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;> rfl
  · change (if readRow c d=readColumn c d then rat
        (if qmaClockAt c.gates.length (qmaFirstUseTime c i) (readRow c d ∘ Sum.inl) ∧
          qmaInputCheck c i (readRow c d ∘ Sum.inr) then 14 else 0) else rat 0) =
      if readRow c d=readColumn c d then rat
        (if clockRow c d (QuantumFirstUseProgram.value (c,i.val))=1 ∧
          clockRow c d (QuantumFirstUseProgram.value (c,i.val)+1)=0 ∧
          c.witness ≤ i.val ∧ workRow c d i.val≠0 then 14 else 0) else rat 0
    simp only [QuantumFirstUseProgram.value_eq]
    unfold qmaClockAt qmaInputCheck
    have he : (clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0) ∧
        (c.witness ≤ i.val ∧ workRow c d i.val≠0) ↔
      clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0 ∧
        c.witness ≤ i.val ∧ workRow c d i.val≠0 := by tauto
    simp only [readRow,clockRow,workRow,referenceWork_eq,
      QuantumOrderedSupport.siteNumber,Function.comp_apply,Fin.val_castSucc,Fin.val_succ] at *
    simp only [he]
    rfl
  · cases u
    rfl
  · norm_num [encode] at ha

theorem readRow_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readRow c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.row_actual c hT a s t (.inr q)

theorem readColumn_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readColumn c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => t ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.column_actual c hT a s t (.inr q)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitDiagonal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_imaginary _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.realHeight_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real diagonal term remains diagonal under the reference-spin rebit
construction.  These entry identities avoid any sum over spectators. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumAlgebraicHistory QuantumAlgebraicScalar
open scoped Classical

theorem rebit_rat_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=rat q) :
    rebit n i A s t = if s ∘ Sum.inl=t ∘ Sum.inl then rat q else rat 0 := by
  by_cases h : s ∘ Sum.inl=t ∘ Sum.inl
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]
  · simp [rebit,hA,identity,h,rat,realRat,QuantumAlgebraicScalar.realPart,imagPart,mul,add,neg,
      realAdd,realSub,realNeg,realMul,imaginary]

theorem rebit_diagonal_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (q : ℚ)
    (hA : A (s ∘ Sum.inr) (t ∘ Sum.inr)=
      if s ∘ Sum.inr=t ∘ Sum.inr then rat q else rat 0) :
    rebit n i A s t = if s=t then rat q else rat 0 := by
  by_cases hb : s ∘ Sum.inr=t ∘ Sum.inr
  · rw [ite_eq_left hb] at hA
    rw [rebit_rat_entry n i A s t q hA]
    have he : (s ∘ Sum.inl=t ∘ Sum.inl) ↔ s=t := by
      constructor
      · intro hr
        funext a
        cases a with
        | inl a => exact congrFun hr a
        | inr a => exact congrFun hb a
      · intro h
        exact congrArg (fun f => f ∘ Sum.inl) h
    simp only [he]
  · rw [ite_eq_right hb] at hA
    rw [rebit_rat_entry n i A s t 0 hA]
    have hne : s≠t := fun h => hb (congrArg (fun f => f ∘ Sum.inr) h)
    simp [hne]

theorem orderedExtend_at (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
    (i : Fin (QuantumOrderedSupport.sites c hT a).length) :
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val)=s i := by
  calc
    orderedExtend c hT a s ((QuantumOrderedSupport.supportEquiv c hT a i).val) =
      s ((QuantumOrderedSupport.supportEquiv c hT a).symm
        (QuantumOrderedSupport.supportEquiv c hT a i)) :=
      dite_eq_left (QuantumOrderedSupport.supportEquiv c hT a i).property
    _ = s i := congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).symm_apply_apply i)

theorem orderedExtend_injective (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Function.Injective (orderedExtend c hT a) := by
  intro s t h
  funext i
  have he := congrFun h (QuantumOrderedSupport.supportEquiv c hT a i).val
  simpa only [orderedExtend_at] using he

theorem ordered_diagonal_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (QuantumHistoryDescriptors.encode c
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4)
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    orderedTable c hT (.inl i) s t = if s=t then rat (weight c
      (QuantumHistoryDescriptors.encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i))
      (supportData c hT (.inl i) s t)) else rat 0 := by
  let S := orderedExtend c hT (.inl i) s
  let T := orderedExtend c hT (.inl i) t
  let a := qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i
  have hd := distributed_entry c a ha (supportData c hT (.inl i) s t)
  rw [readRow_actual,readColumn_actual] at hd
  have he := rebit_diagonal_entry (qmaHistoryReferenceWork c+1) i
    (distributed c (qmaFirstUseTime c) a) S T
    (weight c (QuantumHistoryDescriptors.encode c a) (supportData c hT (.inl i) s t)) hd
  have hs : S=T ↔ s=t := (orderedExtend_injective c hT (.inl i)).eq_iff
  change rebit (qmaHistoryReferenceWork c+1) i (distributed c (qmaFirstUseTime c) a) S T = _
  rw [he]
  simp only [hs]
  rfl

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumDiagonalTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    table (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      QuantumAlgebraicHistory.orderedTable c hT (.inl i) := by
  funext s t
  exact (ordered_diagonal_entry c hT i ha s t).symm

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) :=
  congrArg matrixData (table_actual c hT i ha)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryXZPromise
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit inverse-polynomial thresholds for the actual two-local X/Z
history output. The precision is a fixed linear unary function of clock length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory

theorem xz_threshold_gap (c : QMACircuit) :
    xzNoThreshold c-xzYesThreshold c = 1/(30*(c.gates.length+1:ℚ)) := by
  have ht : (c.gates.length+1:ℚ) ≠ 0 := by positivity
  unfold xzNoThreshold xzYesThreshold
  field_simp
  ring

theorem xz_threshold_lt (c : QMACircuit) : xzYesThreshold c < xzNoThreshold c := by
  have h := xz_threshold_gap c
  have hp : (0:ℚ) < 1/(30*(c.gates.length+1:ℚ)) := by positivity
  linarith

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.qmaApplyMatrix_one _root_.OAI.ContinuumCoulomb.qmaHistoryFromVector_fin _root_.OAI.ContinuumCoulomb.qmaMask_apply _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_length _root_.OAI.ContinuumCoulomb.qmaPrefixMatrix_zero _root_.OAI.ContinuumCoulomb.qmaUnaryExtend_valid _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the encoded source's original swap-form variational
energy with the complete finite matrix used by all mediator stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

theorem sourceSpinMass_norm_sq {n : ℕ} (p : MediatorLowSpace n) :
    sourceSpinMass (fun s => p s) = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sourceSpinMass, Complex.normSq_eq_norm_sq]

theorem sourceGraphMatrix_action (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    d.bonds.matrix *ᵥ u = sourceHamiltonian d u := by
  unfold MediatorIteration.Bonds.matrix SquareLatticeHeisenberg.bonds sourceGraphMatrix
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, sourceHeisenbergMatrix_mulVec,
    ]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_ratCast]
  rfl

theorem sourceGraphMatrix_form (d : SquareLatticeHeisenberg)
    (p : MediatorLowSpace d.vertices) :
    ⟪p, spinMatrixOperator d.bonds.matrix p⟫_ℝ = sourceHamiltonianForm d (fun s => p s) := by
  rw [HubbardGlobal.euclidean_real_inner, sourceHamiltonianForm_eq_expectation]
  have hact : spinMatrixOperator d.bonds.matrix p =
      WithLp.toLp 2 (sourceHamiltonian d (fun s => p s)) := by
    ext s
    exact congrFun (sourceGraphMatrix_action d (fun s => p s)) s
  rw [hact, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [RCLike.inner_apply, mul_comm]
  rfl

/-- The mediator input is the actual source energy in the published promise. -/
theorem sourceMatrixBottom_eq_realSource (d : SquareLatticeHeisenberg) :
    sourceMatrixBottom d.vertices d.bonds.matrix = realSourceGroundEnergy d := by
  obtain ⟨p, hp, hb, hmin⟩ := sourceMatrixBottom_minimizer d.vertices d.bonds.matrix
  have hmass : sourceSpinMass (fun s => p s) = 1 := by rw [sourceSpinMass_norm_sq, hp]; norm_num
  apply le_antisymm
  · apply realSourceGroundEnergy_lower_of_forall
    intro u hu
    let q : MediatorLowSpace d.vertices := WithLp.toLp 2 u
    have hq : ‖q‖ = 1 := by
      have hs : ‖q‖ ^ 2 = 1 := (sourceSpinMass_norm_sq q).symm.trans hu
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hs)
    rw [hb]
    simpa only [sourceGraphMatrix_form, q] using hmin q hq
  · rw [hb, sourceGraphMatrix_form]
    exact realSourceGroundEnergy_le_trial d (fun s => p s) hmass

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticeEncoding
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite source objects serialize to valid binary instances with canonical
rational coefficients and the same physical sites and thresholds. -/

namespace ContinuumCoulomb.SquareLatticeHeisenberg

private theorem ext_data {d e : SquareLatticeHeisenberg}
    (hn : d.vertices = e.vertices) (hc : HEq d.coordinate e.coordinate)
    (hm : d.edges = e.edges) (hl : HEq d.left e.left) (hr : HEq d.right e.right)
    (hJ : HEq d.coefficient e.coefficient) (ha : d.lower = e.lower) (hb : d.upper = e.upper) : d = e := by
  cases d
  cases e
  cases hn
  cases hm
  cases hc
  cases hl
  cases hr
  cases hJ
  cases ha
  cases hb
  rfl

theorem binary_toSource (d : SquareLatticeHeisenberg) :
    d.binary.toSource d.binary_valid = d := by
  apply ext_data (d.binary_vertices) ?_ (d.binary_edges) ?_ ?_ ?_ (binary_lower d) (binary_upper d)
  · apply (Fin.heq_fun_iff d.binary_vertices).mpr
    intro i
    exact get_ofFn_value d.coordinate i.val (by simpa using i.isLt)
  · apply Function.hfunext (congrArg Fin d.binary_edges)
    intro i j hij
    apply (Fin.heq_ext_iff d.binary_vertices).mpr
    change (d.binary.edges.get i).left = (d.left j).val
    rw [d.binary_getEdge i]
    dsimp only [binaryEdge]
    have hval := Fin.val_eq_val_of_heq hij
    exact congrArg (fun e : Fin d.edges => (d.left e).val) (Fin.ext hval)
  · apply Function.hfunext (congrArg Fin d.binary_edges)
    intro i j hij
    apply (Fin.heq_ext_iff d.binary_vertices).mpr
    change (d.binary.edges.get i).right = (d.right j).val
    rw [d.binary_getEdge i]
    dsimp only [binaryEdge]
    have hval := Fin.val_eq_val_of_heq hij
    exact congrArg (fun e : Fin d.edges => (d.right e).val) (Fin.ext hval)
  · apply (Fin.heq_fun_iff d.binary_edges).mpr
    intro i
    change (d.binary.edges.get i).coefficient.value = _
    rw [d.binary_getEdge i]
    exact BinaryRational.value_ofRat _

end ContinuumCoulomb.SquareLatticeHeisenberg

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumLatticePromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual lattice serialization preserves the source energy promise.
Numerical envelopes may be measured against any retained input size; the
output bit length is at least the number of physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

namespace SquareLatticeHeisenberg

theorem binary_mem_yes (d : SquareLatticeHeisenberg) {k : ℕ}
    (hp : d.binary.PolynomialPromise k) (he : realSourceGroundEnergy d ≤ (d.lower:ℝ)) :
    d.binary ∈ (sourceHeisenbergPromise k).yes := by
  refine ⟨d.binary_valid,hp,?_⟩
  rw [d.binary_toSource,← realSourceGroundEnergy_coe,d.binary_lower]
  exact EReal.coe_le_coe he

theorem binary_mem_no (d : SquareLatticeHeisenberg) {k : ℕ}
    (hp : d.binary.PolynomialPromise k) (he : (d.upper:ℝ) ≤ realSourceGroundEnergy d) :
    d.binary ∈ (sourceHeisenbergPromise k).no := by
  refine ⟨d.binary_valid,hp,?_⟩
  rw [d.binary_toSource,← realSourceGroundEnergy_coe,d.binary_upper]
  exact EReal.coe_le_coe he

end SquareLatticeHeisenberg

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceBondLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete matrix semantics for the literal bond registers. Removing zero
terms preserves the actual Hamiltonian, while valid bounded indices give
the exact finite family used in the mediator comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceBondLists
open Matrix MediatorIteration MediatorListProgram
open scoped BigOperators

theorem bondMatrix_zero (n : ℕ) (e : _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (he : e.2.2 = 0) : bondMatrix n e = 0 := by
  unfold bondMatrix
  split <;> simp only [he, Rat.cast_zero, zero_smul]

theorem matrix_bonds (n : ℕ) (xs : List _root_.OAI.ContinuumCoulomb.MediatorListProgram.Bond) (h : bounded n xs) :
    matrix n xs = (bonds n xs h).matrix := by
  have hlist : xs.map (bondMatrix n) = List.ofFn (fun i : Fin xs.length => bondMatrix n (xs.get i)) := by
    simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map xs (bondMatrix n)).symm
  rw [matrix, hlist, List.sum_ofFn]
  unfold Bonds.matrix sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro i _
  rw [bondMatrix, dite_eq_left (h _ (List.get_mem xs i))]
  simp only [bonds, Complex.ofReal_ratCast]

end ContinuumCoulomb.SourceBondLists

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListMergeMatrix
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical bond merging preserves the complete exchange matrix exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open MediatorListProgram
open scoped BigOperators Classical

private theorem sum_indicator {M : Type} [AddCommMonoid M] (ps : List Pair)
    (hn : ps.Nodup) (p : Pair) (hp : p ∈ ps) (z : M) :
    (ps.map (fun q => if p=q then z else 0)).sum=z := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨hq,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hp
    · have hz : (qs.map (fun q => if p=q then z else 0)).sum=0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨q,hq',rfl⟩ := List.mem_map.mp ha
        have hne : p≠q := by
          intro he
          subst q
          exact hq hq'
        exact ite_eq_right hne
      simp [hz]
    · have hne : p≠q := fun he => hq (he ▸ hp)
      simpa only [List.map_cons,List.sum_cons,ite_eq_right hne,zero_add] using ih ht hp

private theorem sum_swap {α β M : Type} [AddCommMonoid M]
    (xs : List α) (ys : List β) (f : α → β → M) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.sum_map_add] using
      (congrArg (fun z => (ys.map (f x)).sum+z) ih)

theorem ordered_matrix (n : ℕ) (e : Bond) (he : e.1<n ∧ e.2.1<n) :
    SourceBondLists.bondMatrix n ((ordered e).1,(ordered e).2,e.2.2) =
      SourceBondLists.bondMatrix n e := by
  by_cases h : e.1 ≤ e.2.1
  · simp only [ordered,min_eq_left h,max_eq_right h]
  · have h' : e.2.1 ≤ e.1 := by omega
    simp only [ordered,min_eq_right h',max_eq_left h']
    rw [SourceBondLists.bondMatrix,dite_eq_left ⟨he.2,he.1⟩,
      SourceBondLists.bondMatrix,dite_eq_left he]
    exact congrArg (fun a => (e.2.2:ℂ) • a)
      (qmaHeisenberg_symm n ⟨e.2.1,he.2⟩ ⟨e.1,he.1⟩)

private theorem pairMatrix_add (n : ℕ) (p : Pair) (a b : ℚ) :
    SourceBondLists.bondMatrix n (p.1,p.2,a+b) =
      SourceBondLists.bondMatrix n (p.1,p.2,a)+SourceBondLists.bondMatrix n (p.1,p.2,b) := by
  unfold SourceBondLists.bondMatrix
  split_ifs <;> simp only [Rat.cast_add,add_smul,zero_add]

private theorem pairMatrix_contribution (n : ℕ) (p : Pair) (e : Bond)
    (he : e.1<n ∧ e.2.1<n) :
    SourceBondLists.bondMatrix n (p.1,p.2,if ordered e=p then e.2.2 else 0) =
      if ordered e=p then SourceBondLists.bondMatrix n e else 0 := by
  by_cases h : ordered e=p
  · rw [ite_eq_left h,ite_eq_left h,← h]
    exact ordered_matrix n e he
  · rw [ite_eq_right h,ite_eq_right h]
    exact SourceBondLists.bondMatrix_zero n _ rfl

theorem matrix_row (n : ℕ) (xs : List Bond) (hb : SourceBondLists.bounded n xs) (p : Pair) :
    SourceBondLists.bondMatrix n (p.1,p.2,weight xs p) =
      (xs.map (fun e => if ordered e=p then SourceBondLists.bondMatrix n e else 0)).sum := by
  induction xs with
  | nil => exact SourceBondLists.bondMatrix_zero n _ rfl
  | cons e xs ih =>
    have he := hb e (List.mem_cons_self)
    have ht : SourceBondLists.bounded n xs := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    change SourceBondLists.bondMatrix n
      (p.1,p.2,(if ordered e=p then e.2.2 else 0)+weight xs p) = _
    rw [pairMatrix_add,pairMatrix_contribution n p e he,ih ht]
    rfl

theorem matrix_eq (n : ℕ) (xs : List Bond) (hb : SourceBondLists.bounded n xs) :
    SourceBondLists.matrix n (value n xs)=SourceBondLists.matrix n xs := by
  have hm : (support n xs).map (fun p => SourceBondLists.bondMatrix n (p.1,p.2,weight xs p)) =
      (support n xs).map (fun p => (xs.map
        (fun e => if ordered e=p then SourceBondLists.bondMatrix n e else 0)).sum) := by
    apply List.map_congr_left
    intro p _
    exact matrix_row n xs hb p
  simp only [SourceBondLists.matrix,value,List.map_map,Function.comp_def]
  rw [hm,sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact sum_indicator (support n xs) (support_nodup n xs) (ordered e)
    ((mem_support hb _).mpr (List.mem_map.mpr ⟨e,he,rfl⟩)) _

end ContinuumCoulomb.QuantumListMerge

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed coordinate and bond tapes define a valid lattice
source. Canonical merging preserves its full matrix and scalar threshold shift. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open MediatorListProgram
open QuantumListMerge

theorem source_matrix (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    (source ps xs hp hn hb hl ha a b c hab).bonds.matrix = SourceBondLists.matrix ps.length xs :=
  (SourceBondLists.matrix_bonds ps.length (_root_.OAI.ContinuumCoulomb.QuantumListMerge.value ps.length xs) (bounded ps.length xs)).symm.trans
    (matrix_eq ps.length xs hb)

theorem source_energy (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) =
      sourceMatrixBottom ps.length (SourceBondLists.matrix ps.length xs) := by
  rw [← sourceMatrixBottom_eq_realSource,source_matrix]
  rfl

theorem source_energy_shift (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) =
      sourceMatrixBottom ps.length
        (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)-(c:ℝ) := by
  rw [source_energy]
  simpa only [Complex.ofReal_ratCast,add_sub_cancel_right] using
    sourceMatrixBottom_shift ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) (c:ℝ)

theorem source_yes (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b)
    (he : sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) ≤ (a:ℝ)) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) ≤
      ((source ps xs hp hn hb hl ha a b c hab).lower:ℝ) := by
  rw [source_energy_shift]
  change _ ≤ ((a-c:ℚ):ℝ)
  simpa only [Rat.cast_sub] using sub_le_sub_right he (c:ℝ)

theorem source_no (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b)
    (he : (b:ℝ) ≤ sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)) :
    ((source ps xs hp hn hb hl ha a b c hab).upper:ℝ) ≤
      realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) := by
  rw [source_energy_shift]
  change ((b-c:ℚ):ℝ) ≤ _
  simpa only [Rat.cast_sub] using sub_le_sub_right he (c:ℝ)

end ContinuumCoulomb.QuantumListLattice

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListLatticeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source serialization from the computed coordinate and bond tapes. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

theorem value_source (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    value (ps,xs,a,b,c)=(source ps xs hp hn hb hl ha a b c hab).binary := by
  have hp' : List.ofFn (fun i : Fin ps.length => qmaGridCoordinate (ps.get i)) =
      ps.map qmaGridCoordinate := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map ps qmaGridCoordinate
  have he' : List.ofFn (fun i : Fin (QuantumListMerge.value ps.length xs).length =>
      QuantumLatticeSerialization.edge ((QuantumListMerge.value ps.length xs).get i)) =
      (QuantumListMerge.value ps.length xs).map QuantumLatticeSerialization.edge := by
    simpa only [List.get_eq_getElem] using
      List.ofFn_getElem_eq_map (QuantumListMerge.value ps.length xs) QuantumLatticeSerialization.edge
  change BinaryHeisenberg.mk _ _ _ _ = BinaryHeisenberg.mk _ _ _ _
  exact congrArg₂ (fun p e => BinaryHeisenberg.mk p e
    (BinaryRational.ofRat (a-c)) (BinaryRational.ofRat (b-c))) hp'.symm he'.symm

theorem value_mem_yes (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) {k : ℕ}
    (hpoly : (value (ps,xs,a,b,c)).PolynomialPromise k)
    (he : sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) ≤ (a:ℝ)) :
    value (ps,xs,a,b,c) ∈ (sourceHeisenbergPromise k).yes := by
  rw [value_source ps xs hp hn hb hl ha a b c hab] at hpoly ⊢
  exact SquareLatticeHeisenberg.binary_mem_yes _ hpoly
    (source_yes ps xs hp hn hb hl ha a b c hab he)

theorem value_mem_no (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) {k : ℕ}
    (hpoly : (value (ps,xs,a,b,c)).PolynomialPromise k)
    (he : (b:ℝ) ≤ sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)) :
    value (ps,xs,a,b,c) ∈ (sourceHeisenbergPromise k).no := by
  rw [value_source ps xs hp hn hb hl ha a b c hab] at hpoly ⊢
  exact SquareLatticeHeisenberg.binary_mem_no _ hpoly
    (source_no ps xs hp hn hb hl ha a b c hab he)

end ContinuumCoulomb.QuantumListLattice

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRoutePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of the exact finite coordinate/route representation by one
round, and hence by the fixed number of rounds of the literal compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode
open scoped Classical

variable {Γ : SimpleGraph Pair}

theorem iterate_state (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1=QuantumListSchedule.iterate N k s.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change QuantumListSchedule.value (N,(iterate N k s).1)=_
    rw [ih]
    rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumListRouteLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final literal route tape is itself the serialized lattice source.
Its coordinate and edge order are the computed orders, and its exact scalar
offset is removed from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode MediatorListProgram
open ExactQuantumFactoring.BitStackProgram

private theorem get_of_eq_ofFn {α : Type} {n : ℕ} {xs : List α} {f : Fin n → α}
    (h : xs=List.ofFn f) (i : Fin xs.length) :
    xs.get i=f ⟨i.val,by simpa only [h,List.length_ofFn] using i.isLt⟩ := by
  subst xs
  simp only [List.get_eq_getElem,List.getElem_ofFn]

theorem represented_nodup (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P) :
    s.2.1.Nodup := by
  rw [hP.1]
  exact List.nodup_ofFn.mpr P.position_injective

theorem represented_adjacent (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e))) :
    QuantumListLattice.Adjacent s.2.1 (erase s.1.2.2) (represented_bounded s hs P hP) := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hw
  rw [get_of_eq_ofFn hP.1,get_of_eq_ofFn hP.1]
  exact ha i

theorem latticeOutput_yes (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) {k : ℕ}
    (hp : (latticeOutput s a b).PolynomialPromise k)
    (he : QuantumListSchedule.energy s.1 ≤ (a:ℝ)) :
    latticeOutput s a b ∈ (sourceHeisenbergPromise k).yes := by
  apply QuantumListLattice.value_mem_yes _ _
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab hp
  rw [represented_length s hs P hP]
  exact he

theorem latticeOutput_no (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    (ha : ∀ e, qmaSquareGrid.Adj (P.position ((schedule s.1 hs).graph.left e))
      (P.position ((schedule s.1 hs).graph.right e)))
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b) {k : ℕ}
    (hp : (latticeOutput s a b).PolynomialPromise k)
    (he : (b:ℝ) ≤ QuantumListSchedule.energy s.1) :
    latticeOutput s a b ∈ (sourceHeisenbergPromise k).no := by
  apply QuantumListLattice.value_mem_no _ _
    (by rw [represented_length s hs P hP]; exact hn)
    (represented_nodup s hs P hP) (represented_bounded s hs P hP) hs.2
    (represented_adjacent s hs P hP ha) a b s.1.2.1 hab hp
  rw [represented_length s hs P hP]
  exact he

theorem iterate_count_le (N : ℚ) (s : State) (k : ℕ) :
    s.1.1 ≤ (iterate N k s).1.1 := by
  rw [iterate_state]
  suffices ∀ k, s.1.1 ≤ (QuantumListSchedule.iterate N k s.1).1 from this k
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change s.1.1 ≤ (QuantumListSchedule.value (N,QuantumListSchedule.iterate N k s.1)).1
    rw [value_count]
    exact ih.trans (Nat.le_add_right _ _)

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumFinalPrecision
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision for all nine early simulation errors and the subsequent
routing errors, retaining the exact final inverse-polynomial promise gap. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram

theorem finalPrecision_pos (rounds : ℕ) (c : QMACircuit) :
    0 < finalPrecision rounds c := by
  unfold finalPrecision
  positivity

theorem final_error_budget (rounds : ℕ) (c : QMACircuit) :
    ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      1/(60*(c.gates.length+1:ℝ)) := by
  have hr : (rounds:ℝ)+9 ≠ 0 := by positivity
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [finalPrecision,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  field_simp

theorem final_yes_budget (rounds : ℕ) (c : QMACircuit) :
    1/(3*(c.gates.length+1:ℝ))+((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      (xzYesThreshold c:ℝ) := by
  rw [final_error_budget]
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzYesThreshold,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

theorem final_no_budget (rounds : ℕ) (c : QMACircuit) :
    2/(5*(c.gates.length+1:ℝ))-((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ) =
      (xzNoThreshold c:ℝ) := by
  rw [final_error_budget]
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzNoThreshold,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

theorem final_accepting (rounds : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (hc : c.WellFormed) {E : ℝ}
    (herr : |E-(qmaOrderedHistoryModel c hT).energy| ≤
      ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ))
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) : E ≤ (xzYesThreshold c:ℝ) := by
  have he := (abs_le.mp herr).2
  have hh := qmaOrderedHistoryModel_yes c hT hc psi hpsi hacc
  rw [← final_yes_budget rounds c]
  linarith

theorem final_rejecting (rounds : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (hc : c.WellFormed) {E : ℝ}
    (herr : |E-(qmaOrderedHistoryModel c hT).energy| ≤
      ((rounds:ℝ)+9)/(finalPrecision rounds c:ℝ))
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) : (xzNoThreshold c:ℝ) ≤ E := by
  have he := (abs_le.mp herr).1
  have hh := qmaOrderedHistoryModel_no c hT hc hsound
  rw [← final_no_budget rounds c]
  linarith

theorem final_threshold_gap_bound (c : QMACircuit) {n k : ℕ}
    (hn : 0 < n) (hT : c.gates.length ≤ n) (hk : 6 ≤ k) :
    ((n+1:ℝ)^k)⁻¹ ≤ (xzNoThreshold c:ℝ)-xzYesThreshold c := by
  have hbase : (2:ℝ) ≤ n+1 := by exact_mod_cast (show 2 ≤ n+1 by omega)
  have ht : (c.gates.length+1:ℝ) ≤ n+1 := by exact_mod_cast Nat.add_le_add_right hT 1
  have hp : (32:ℝ) ≤ (n+1:ℝ)^5 := by
    simpa only [show (2:ℝ)^5=32 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hbase 5
  have hd : 30*(c.gates.length+1:ℝ) ≤ (n+1:ℝ)^k := by
    calc
      _ ≤ 32*(n+1:ℝ) := by nlinarith
      _ ≤ (n+1:ℝ)^5*(n+1) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (n+1:ℝ)^6 := (pow_succ _ 5).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ n+1) hk
  have hg : (xzNoThreshold c:ℝ)-xzYesThreshold c = 1/(30*(c.gates.length+1:ℝ)) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (xz_threshold_gap c)
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,Rat.cast_ofNat] using h
  rw [hg,one_div]
  exact inv_anti₀ (by positivity) hd

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkListInitialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the literal initial ports recovers the two physical end
couplings of each input edge. The regrouping uses its actual endpoint table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialBond_mem (bs : List Bond) (j : ℕ) (hj : j < 2*bs.length) :
    initialBond bs j ∈ bs := by
  have hi : j/2 < bs.length := by omega
  simp only [initialBond,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem initialEndpoint_bound (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (j : ℕ) (hj : j < 2*bs.length) : initialEndpoint bs j < n := by
  have h := hb _ (initialBond_mem bs j hj)
  unfold initialEndpoint
  split
  · exact h.1
  · exact h.2

end ContinuumCoulomb.QuantumForkList

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrdinalProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal ordinal-slot program. For an encoded cell list and a unary
label it counts earlier labels in the same cell; the result agrees with the
bounded injective slots used by the spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem value_eq_card (x : Input) :
    value x = ((Finset.range x.1).filter (fun i =>
      QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)).card := by
  unfold value sameCell
  rw [List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_range,Function.comp_apply,id_eq] using
    (List.nodup_range (n := x.1)).card_eq_countP
      (P := fun i => QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)

theorem lookup_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    QuantumPathVisitProgram.lookup (List.ofFn cells) q.val = cells q := by
  unfold QuantumPathVisitProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    value (q.val,List.ofFn cells) = QuantumOrdinalSlots.rank cells q := by
  rw [value_eq_card]
  unfold QuantumOrdinalSlots.rank
  symm
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    obtain ⟨_,hlt,hcell⟩ := Finset.mem_filter.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlt,?_⟩
    simpa only [lookup_ofFn] using hcell
  · intro r hr s hs h
    exact Fin.ext h
  · intro i hi
    obtain ⟨hi,hcell⟩ := Finset.mem_filter.mp hi
    have hiq : i < q.val := Finset.mem_range.mp hi
    let r : Fin n := ⟨i,hiq.trans q.isLt⟩
    refine ⟨r,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hiq,?_⟩
    simpa only [← show r.val=i from rfl,lookup_ofFn] using hcell

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialSlotProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fine-grid positions and lane colors of the ordinal-slot model
are computed directly from encoded lists of cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialSlotProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

theorem colorEquiv_val {B : ℕ} (c : Fin 3 × Fin 3 × Fin B) :
    (qmaGridColorEquiv B c).val = c.2.2.val+B*c.2.1.val+(3*B)*c.1.val := by
  rfl

theorem fineSite_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fineSite A (q.val,List.ofFn (QuantumOrdinalPlacement.coordinates M.cell)) =
      (M.withOrdinalSlots labels).routeVertex q := by
  unfold fineSite
  rw [lookup_ofFn,value_ofFn]
  rfl

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,
      List.ofFn (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))) =
      ((M.withOrdinalSlots labels).laneColor e).val := by
  unfold lane
  rw [lookup_ofFn,value_ofFn]
  change _ = (qmaGridColorEquiv B ((M.withOrdinalSlots labels).termSlots.color e)).val
  rw [colorEquiv_val]
  simp only [QMASpatialExchangeModel.withOrdinalSlots,QMACellSlots.color,
    QMACellSlots.transport,QuantumOrdinalPlacement.slots,QuantumOrdinalPlacement.coordinates,
    Function.comp_apply,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumSpatialSlotProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint arm assigned to an incident interaction is the number of
incident lane colors below it. This exposes the finite count used by the
literal route evaluator. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPort_orderRank {C : ℕ} (s : Finset (Fin C)) (x : s) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun y => y < x.val)).card := by
  let E := s.orderIsoOfFin rfl
  have h : (Finset.Iio (E.symm x)).card = (s.filter (fun y => y < x.val)).card := by
    apply Finset.card_bij (fun i _ => (E i).val)
    · intro i hi
      refine Finset.mem_filter.mpr ⟨(E i).property,?_⟩
      have hh := E.strictMono (Finset.mem_Iio.mp hi)
      change (E i).val < (E (E.symm x)).val at hh
      simpa only [E.apply_symm_apply] using hh
    · intro i hi j hj hij
      exact E.injective (Subtype.ext hij)
    · intro y hy
      obtain ⟨hys,hyx⟩ := Finset.mem_filter.mp hy
      refine ⟨E.symm ⟨y,hys⟩,Finset.mem_Iio.mpr ?_,?_⟩
      · exact E.symm.strictMono hyx
      · exact congrArg Subtype.val (E.apply_symm_apply ⟨y,hys⟩)
  simpa only [Fin.card_Iio] using h

theorem qmaCanonicalSortedPorts_assign_rank {κ : Type} [Fintype κ] {C : ℕ}
    (color : κ → Fin C) (hc : Fintype.card κ ≤ 3) (hi : Function.Injective color) (e : κ) :
    ((qmaCanonicalSortedPorts color hc).assign e).val =
      (Finset.univ.filter (fun f => color f < color e)).card := by
  let s := Finset.univ.image color
  have he : color e ∈ s := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
  change ((s.orderIsoOfFin rfl).symm ⟨color e,he⟩).val = _
  rw [qmaPort_orderRank]
  symm
  apply Finset.card_bij (fun f _ => color f)
  · intro f hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨f,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hf).2⟩
  · intro f hf g hg h
    exact hi h
  · intro y hy
    obtain ⟨hys,hy⟩ := Finset.mem_filter.mp hy
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hys
    exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,rfl⟩

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointPorts_assign_rank (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) (e : M.Incident v) :
    ((M.endpointPorts hd v).assign e).val =
      (Finset.univ.filter (fun f : M.Incident v => M.laneColor f.val < M.laneColor e.val)).card :=
  qmaCanonicalSortedPorts_assign_rank _ _ (M.incident_color_injective hA v) e

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sorted endpoint port is evaluated by counting incident edges whose
lane color is smaller. Each record contains the two endpoints and lane color. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem count_ofFn {n : ℕ} (entries : Fin n → Entry) (vc : Pair) :
    value (vc,List.ofFn entries) =
      (Finset.univ.filter (fun i =>
        ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)).card := by
  unfold value below
  rw [List.ofFn_eq_map,List.map_map,List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_finRange] using (List.nodup_finRange n).card_eq_countP
    (P := fun i => ((entries i).1=vc.1 ∨ (entries i).2.1=vc.1) ∧ (entries i).2.2<vc.2)

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortRankActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal incidence count computes the very arm assignment used by the
spatial routing proof, for any explicit enumeration of the interaction labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open scoped Classical

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    value ((v.val,(M.laneColor e.val).val),List.ofFn (entries M labels)) =
      ((M.endpointPorts hd v).assign e).val := by
  rw [count_ofFn,M.endpointPorts_assign_rank hA]
  symm
  apply Finset.card_bij (fun f _ => labels f.val)
  · intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [entries,labels.symm_apply_apply]
    refine ⟨?_,(Finset.mem_filter.mp hf).2⟩
    rcases f.property with hl | hr
    · exact Or.inl (congrArg Fin.val hl)
    · exact Or.inr (congrArg Fin.val hr)
  · intro f hf g hg h
    exact Subtype.ext (labels.injective h)
  · intro i hi
    obtain ⟨_,hinc,hlt⟩ := Finset.mem_filter.mp hi
    dsimp only [entries] at hinc hlt
    have hmember : M.left (labels.symm i)=v ∨ M.right (labels.symm i)=v :=
      hinc.imp Fin.ext Fin.ext
    let f : M.Incident v := ⟨labels.symm i,hmember⟩
    refine ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,?_⟩
    exact labels.apply_symm_apply i

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell arrays follow the same term-major order as the literal local-word
compiler. Each new mediator inherits its term's cell; each output word retains
that cell as its anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem cells_ofFn {n m : ℕ} (d : ℕ) (cell : Fin n → Pair) (anchor : Fin m → Pair) :
    (value d (List.ofFn cell,List.ofFn anchor)).1=List.ofFn (Fin.append cell anchor) :=
  (List.ofFn_fin_append cell anchor).symm

theorem anchors_ofFn {m : ℕ} (d : ℕ) (anchor : Fin m → Pair) :
    anchors d (List.ofFn anchor)=
      (List.ofFn (fun i : Fin m => List.ofFn (fun _ : Fin d => anchor i))).flatten := by
  simp only [anchors,List.map_ofFn,List.ofFn_const,Function.comp_def]

end ContinuumCoulomb.QuantumOrderedCellProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedCellTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.allRouted_length _root_.OAI.ContinuumCoulomb.QuantumPortChainProgram.value_length _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed spatial arrays use exactly the same sum/product enumeration
as the actual ordered Hamiltonian compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedCellTable
open QuantumOrderedCellProgram QuantumOrderedLabelTable QuantumOrderedSpatialComplete
open ExactQuantumFactoring.BitStackProgram
open QuantumRouteCode
variable {ι κ : Type} {n m : ℕ}

theorem value_table (d : ℕ) (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value d (table q e cell anchor)=
      table (nextQubit q e) (nextTerm e d) (extendCell cell anchor) (extendAnchor d anchor) := by
  apply Prod.ext
  · rw [show (value d (table q e cell anchor)).1=
        List.ofFn (Fin.append (fun i => cell (q i)) (fun i => anchor (e i))) from cells_ofFn d _ _]
    apply congrArg List.ofFn
    funext i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)).surjective i
    cases i <;> simp [nextQubit,extendCell,Fin.append]
  · change anchors d (List.ofFn (fun i => anchor (e i)))=List.ofFn _
    rw [anchors_ofFn]
    rw [← product_table (fun p : Fin m × Fin d => anchor (e p.1))]
    apply congrArg List.ofFn
    funext i
    rfl

theorem complete_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    complete (table q e cell anchor)=
      table (QuantumOrderedLabelTable.qubits6 q e) (QuantumOrderedLabelTable.terms6 e)
        (cell6 cell anchor) (anchor6 anchor) := by
  unfold complete
  rw [value_table,value_table,value_table,value_table,value_table,value_table]
  rfl

end ContinuumCoulomb.QuantumOrderedCellTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumOrderedRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw four-spin compiler repeats each computed logical cell four times,
in exactly the order of its physical spin indices. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawCells
open QuantumOrderedCellProgram QuantumOrderedCellTable QuantumOrderedSpatialComplete
open QuantumOrderedLabelTable QuantumRouteCode
open ExactQuantumFactoring.BitStackProgram

theorem four_ofFn {n : ℕ} (cell : Fin n → Pair) :
    anchors 4 (List.ofFn cell)=
      List.ofFn (fun i : Fin (n*4) => cell (finProdFinEquiv.symm i).1) := by
  rw [anchors_ofFn,← product_table (fun p : Fin n × Fin 4 => cell p.1)]

theorem value_table {ι κ : Type} {n m : ℕ} (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (cell : ι → Pair) (anchor : κ → Pair) :
    value (table q e cell anchor)=
      List.ofFn (fun i : Fin (finalCount n m*4) =>
        cell6 cell anchor (qubits6 q e (finProdFinEquiv.symm i).1)) := by
  unfold value
  rw [complete_table]
  exact four_ofFn _

end ContinuumCoulomb.QuantumOrderedRawCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual row/column arrays for the fork compiler. The scale remains an
input register; only the number of fork rounds is fixed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList ExactQuantumFactoring.BitStackProgram QuantumRouteCode

theorem run_state (k : ℕ) (x : Input) : (run k x).1=iterate x.1 k x.2.1 := by
  induction k with
  | zero => rfl
  | succ k ih => change next x.1 (run k x).1=next x.1 (iterate x.1 k x.2.1); rw [ih]

theorem run_length (k : ℕ) (x : Input) (h : x.2.2.length=x.2.1.1) :
    (run k x).2.length=(run k x).1.1 := by
  cases k with
  | zero => exact h
  | succ k => simp only [run,step,nextCells,List.length_map,List.length_range,next]

theorem lookup_nextCells (x : Cells) (v : ℕ) (hv : v<x.1.1+2*pairCount x.1.2.2.2) :
    lookup (nextCells x) v=nextCell x.1 (lookup x.2) v := by
  simp only [lookup,nextCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextCell_congr (s : QuantumForkList.State) (hs : ValidPorts s.1 s.2.2.2)
    (f g : ℕ → QuantumRouteCode.Pair) (h : ∀ v, v < s.1 → f v=g v) (v : ℕ)
    (hv : v<(next 0 s).1) : nextCell s f v=nextCell s g v := by
  by_cases ho : v < s.1
  · simpa only [nextCell,ite_eq_left ho] using h v ho
  have hi : (v-s.1)/2<pairCount s.2.2.2 := by
    change v < s.1+2*pairCount s.2.2.2 at hv
    omega
  simp only [nextCell,ite_eq_right ho]
  rw [catalog_actualSite hs ⟨(v-s.1)/2,hi⟩]
  exact h _ (actualSite hs ⟨(v-s.1)/2,hi⟩ 0).isLt

theorem step_represents (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (step x) (nextCell x.2.1 cell) := by
  intro v hv
  change lookup (nextCells x.2) v=nextCell x.2.1 cell v
  rw [lookup_nextCells x.2 v hv]
  exact nextCell_congr x.2.1 hs _ _ h v hv

theorem run_represents (k : ℕ) (x : Input) (hs : ValidPorts x.2.1.1 x.2.1.2.2.2)
    (cell : ℕ → QuantumRouteCode.Pair) (h : Represents x.2 cell) :
    Represents (run k x) (iterateCell x.1 k x.2.1 cell) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hi : ValidPorts (run k x).1.1 (run k x).1.2.2.2 := by
      rw [run_state]
      exact iterate_validPorts x.1 x.2.1 hs k
    have hn := step_represents (x.1,run k x) hi _ ih
    simpa only [run_state,run,iterateCell] using hn

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkGridInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial subdivision computes its row/column array from the actual
endpoint list, before the same fixed-round grid program is applied. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList MediatorListProgram ExactQuantumFactoring.BitStackProgram

theorem lookup_initialCells (x : InitialCells) (v : ℕ) (hv : v<x.1+2*x.2.1.length) :
    lookup (initialCells x) v=initialCell x.1 x.2.1 (lookup x.2.2) v := by
  simp only [lookup,initialCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem output_state (k : ℕ) (x : PreparedInput) :
    (output k x).1=iterate x.1.1 k
      (initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1) := run_state k (prepare x)

theorem output_length (k : ℕ) (x : PreparedInput) :
    (output k x).2.length=(output k x).1.1 := by
  apply run_length
  simp only [prepare,initialCells,List.length_map,List.length_range,initial]

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingInputActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The encoded cell/edge arrays evaluate to the actual buffered path of the
ordinal-slot spatial model. No arbitrary finite-fiber choice remains in this
part of the routing compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open QuantumRouteCode

theorem edge_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    edge (actualData M labels) (labels e).val = ((M.left e).val,(M.right e).val) := by
  unfold edge actualData
  rw [QuantumOrdinalProgram.lookup_ofFn]
  simp only [Equiv.symm_apply_apply]

theorem fine_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fine A (actualData M labels) q.val = (M.withOrdinalSlots labels).routeVertex q := by
  unfold fine actualData
  simp only [List.length_ofFn,Nat.min_eq_right q.isLt.le]
  exact QuantumSpatialSlotProgram.fineSite_actual M labels q

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,actualData M labels) = ((M.withOrdinalSlots labels).laneColor e).val :=
  QuantumSpatialSlotProgram.lane_actual M labels e

theorem entry_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (e : M.Term) :
    entry B (actualData M labels) (labels e).val =
      QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels (labels e) := by
  unfold entry
  rw [edge_actual,lane_actual]
  exact (congrArg (fun t : M.Term => ((M.left t).val,(M.right t).val,
    ((M.withOrdinalSlots labels).laneColor t).val)) (labels.symm_apply_apply e)).symm

private theorem entries_ofFn (B : ℕ) (d : Data) {m : ℕ}
    (f : Fin m → QuantumPortRankProgram.Entry) (hlen : d.2.length = m)
    (h : ∀ i : Fin m, entry B d i.val = f i) : entries B d = List.ofFn f := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn,hlen]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simpa only [entries,List.getElem_map,List.getElem_range,List.getElem_ofFn] using h ⟨i,hi'⟩

theorem entries_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) :
    entries B (actualData M labels) =
      List.ofFn (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels) := by
  apply entries_ofFn B (actualData M labels)
    (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
    (by simp only [actualData,List.length_ofFn])
  intro j
  calc
    entry B (actualData M labels) j.val =
        entry B (actualData M labels) (labels (labels.symm j)).val :=
      congrArg (fun k : Fin m => entry B (actualData M labels) k.val)
        (labels.apply_symm_apply j).symm
    _ = QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels
        (labels (labels.symm j)) := entry_actual M labels (labels.symm j)
    _ = _ := congrArg (QuantumPortRankProgram.entries (M.withOrdinalSlots labels) labels)
      (labels.apply_symm_apply j)

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B ((labels e).val,actualData M labels) =
      QuantumBufferedListProgram.actualInput (M.withOrdinalSlots labels) hd e := by
  unfold value
  rw [edge_actual,lane_actual,entries_actual]
  dsimp only
  exact congrArg₂ Prod.mk
    (congrArg₂ Prod.mk (fine_actual M labels (M.left e)) (fine_actual M labels (M.right e)))
    (congrArg (Prod.mk ((M.withOrdinalSlots labels).laneColor e).val)
      (congrArg₂ Prod.mk
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.left e) ⟨e,Or.inl rfl⟩)
        (QuantumPortRankProgram.value_actual (M.withOrdinalSlots labels) labels hA hd
          (M.right e) ⟨e,Or.inr rfl⟩)))

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    QuantumBufferedListProgram.path A B (value A B ((labels e).val,actualData M labels)) =
      ((M.withOrdinalSlots labels).bufferedPath hd e).val.support := by
  exact (congrArg (QuantumBufferedListProgram.path A B)
    (value_actual M labels hA hd e)).trans
    (QuantumBufferedListProgram.path_actual (M.withOrdinalSlots labels) hd e)

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumForkRoutingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal routing-input tape from the full fork state. Active-star bonds
are retained, and each anchor is the integer midpoint of its endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingData
open ExactQuantumFactoring.BitStackProgram QuantumForkList MediatorListProgram

private theorem lookup_ofFn {n : ℕ} (f : Fin n → QuantumRouteCode.Pair) (i : Fin n) :
    QuantumForkGridProgram.lookup (List.ofFn f) i.val=f i :=
  QuantumOrdinalProgram.lookup_ofFn f i

theorem value_spatialModel {rows width : ℕ} (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) :
    value (s,List.ofFn (fun v : Fin s.1 => ((cell v.val).1.val,(cell v.val).2.val))) =
      QuantumRoutingInputProgram.actualData (spatialModel s hs hb hn cell A hc hd hl)
        (Equiv.refl _) := by
  let G := fullGraph s hs hb hn
  let cells : Fin s.1 → QuantumRouteCode.Pair :=
    fun v => ((cell v.val).1.val,(cell v.val).2.val)
  have endpoints : (fullList s).map endpoint =
      List.ofFn (fun i : Fin (fullList s).length => endpoint ((fullList s).get i)) := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map (fullList s) endpoint).symm
  have anchors : (fullList s).map (fun b => anchor (b,List.ofFn cells)) =
      List.ofFn (fun i : Fin (fullList s).length =>
        QuantumGridMidpoint.value (cells (G.left i),cells (G.right i))) := by
    rw [← List.ofFn_getElem_eq_map (fullList s) (fun b => anchor (b,List.ofFn cells))]
    apply congrArg List.ofFn
    funext i
    change QuantumGridMidpoint.value
      (QuantumForkGridProgram.lookup (List.ofFn cells) (G.left i).val,
        QuantumForkGridProgram.lookup (List.ofFn cells) (G.right i).val) = _
    dsimp only [G,fullGraph,QuantumListGraph.ofBonds]
    rw [lookup_ofFn,lookup_ofFn]
  unfold value QuantumRoutingInputProgram.actualData
  apply congrArg₂ Prod.mk
  · apply congrArg₂ Prod.mk
    · rfl
    · exact anchors
  · exact endpoints

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateScalarReduction
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar reduction of a one-site gate tensor to its active entry
and spectator equality test. This avoids an ambient spin-basis sum in the
literal history-matrix evaluator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateScalarReduction
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped Classical

theorem listProduct_single {α : Type} [DecidableEq α] (i : α) (z : Scalar)
    (xs : List α) (hx : xs.Nodup) :
    product (xs.map (fun j => if j=i then z else rat 1)) =
      if i ∈ xs then z else rat 1 := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    by_cases ha : a=i
    · subst a
      have hn : i ∉ xs := (List.nodup_cons.mp hx).1
      simp [product,ih (List.nodup_cons.mp hx).2,hn]
    · simp [product,ha,ih (List.nodup_cons.mp hx).2,Ne.symm ha]

theorem listProduct_zero (xs : List Scalar) (h : rat 0 ∈ xs) : product xs=rat 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with ha | hx
    · subst a
      simp [product]
    · simp [product,ih hx]

theorem finiteProduct_single {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (z : Scalar) :
    finiteProduct (fun j => if j=i then z else rat 1)=z := by
  have hn : (enumerate α).Nodup :=
    List.nodup_ofFn.mpr (Fintype.equivFin α).symm.injective
  have hi : i ∈ enumerate α :=
    List.mem_ofFn.mpr ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩
  rw [finiteProduct,listProduct_single i z _ hn,ite_eq_left hi]

theorem finiteProduct_zero {α : Type} [Fintype α] (f : α → Scalar)
    (i : α) (hi : f i=rat 0) : finiteProduct f=rat 0 := by
  apply listProduct_zero
  apply List.mem_map.mpr
  refine ⟨i,?_,hi⟩
  exact List.mem_ofFn.mpr
    ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩

theorem finiteProduct_sparse {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) :
    finiteProduct (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
      sparseEntry i A s t := by
  by_cases h : ∀ j, j ≠ i → s j=t j
  · have he : (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
        (fun j => if j=i then A (s i) (t i) else rat 1) := by
      funext j
      by_cases hj : j=i
      · simp [hj]
      · simp [hj,identity,h j hj]
    rw [he,finiteProduct_single]
    exact (ite_eq_left h).symm
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hji : j ≠ i := fun he => hj (by simp [he])
    have hst : s j ≠ t j := fun he => hj (fun _ => he)
    rw [finiteProduct_zero _ j (by simp [hji,identity,hst])]
    exact (ite_eq_right h).symm

theorem hadamard_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.hadamard j) s t=sparseEntry (qmaQubit work j) hadamard s t :=
  finiteProduct_sparse _ _ _ _

theorem phaseT_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.phaseT j) s t=sparseEntry (qmaQubit work j) phaseT s t :=
  finiteProduct_sparse _ _ _ _

end ContinuumCoulomb.QuantumGateScalarReduction

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumGateEntryProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

theorem allWork_iff (x : Input) : allWork x = true ↔
    ∀ i : Fin (x.1+1), point x i.val = true := by
  simp only [allWork,List.all_map,List.all_eq_true,List.mem_range,Function.comp_apply,id_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem allWork_single (x : Input) (hg : gateTag x.2.2.1 ≠ 2) :
    allWork x = true ↔ ∀ i : Fin (x.1+1),
      i ≠ qmaQubit x.1 (gateLeft x.2.2.1) → row x i.val=column x i.val := by
  rw [allWork_iff]
  simp only [point,ite_eq_right hg,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h i hi
    rcases h i with he | he
    · exact False.elim (hi (Fin.ext he))
    · exact Fin.ext he
  · intro h i
    by_cases hi : i=qmaQubit x.1 (gateLeft x.2.2.1)
    · exact Or.inl (congrArg Fin.val hi)
    · exact Or.inr (congrArg Fin.val (h i hi))

private theorem swap_val (b : Fin 2) : (Equiv.swap (0 : Fin 2) 1 b).val = 1-b.val := by
  fin_cases b <;> decide

theorem allWork_cnot (work base a b : ℕ) (d : QuantumHistoryBitProgram.Data) :
    allWork (work,base,.controlledNot a b,d) = true ↔
      (fun i : Fin (work+1) => row (work,base,.controlledNot a b,d) i.val) =
      qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun i => column (work,base,.controlledNot a b,d) i.val) := by
  rw [allWork_iff,funext_iff]
  apply forall_congr'
  intro i
  change decide ((row (work,base,.controlledNot a b,d) i.val).val =
    if i.val=b%(work+1) ∧ (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 then
      1-(column (work,base,.controlledNot a b,d) i.val).val
    else (column (work,base,.controlledNot a b,d) i.val).val)=true ↔ _
  rw [decide_eq_true_eq]
  have ht : (i.val=b%(work+1)) ↔ i=qmaQubit work b :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have hc : (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 ↔
      column (work,base,.controlledNot a b,d) (a%(work+1))=1 :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have he : (i.val=b%(work+1) ∧
      (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1) ↔
      (i=qmaQubit work b ∧
        column (work,base,.controlledNot a b,d) (a%(work+1))=1) := and_congr ht hc
  by_cases h : i=qmaQubit work b ∧
      column (work,base,.controlledNot a b,d) (a%(work+1))=1
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        Equiv.swap (0:Fin 2) 1 (column (work,base,.controlledNot a b,d) i.val) :=
      ite_eq_left h
    rw [ite_eq_left (he.mpr h),hr,Fin.ext_iff,swap_val]
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        column (work,base,.controlledNot a b,d) i.val := ite_eq_right h
    rw [ite_eq_right (mt he.mp h),hr,Fin.ext_iff]

theorem entry_eq (work base : ℕ) (g : QMAGate) (d : QuantumHistoryBitProgram.Data) :
    entry (work,base,g,d) = QuantumAlgebraicHistory.gate work g
      (fun i => row (work,base,g,d) i.val) (fun i => column (work,base,g,d) i.val) := by
  cases g with
  | hadamard j =>
    rw [QuantumGateScalarReduction.hadamard_entry]
    have hh := allWork_single (work,base,.hadamard j,d) (by change (0 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.hadamard j,d)=true
    · have hv : entry (work,base,.hadamard j,d) = QuantumAlgebraicHistory.hadamard
          (row (work,base,.hadamard j,d) (left (work,base,.hadamard j,d)))
          (column (work,base,.hadamard j,d) (left (work,base,.hadamard j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.hadamard j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | phaseT j =>
    rw [QuantumGateScalarReduction.phaseT_entry]
    have hh := allWork_single (work,base,.phaseT j,d) (by change (1 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.phaseT j,d)=true
    · have hv : entry (work,base,.phaseT j,d) = QuantumAlgebraicHistory.phaseT
          (row (work,base,.phaseT j,d) (left (work,base,.phaseT j,d)))
          (column (work,base,.phaseT j,d) (left (work,base,.phaseT j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        rw [ite_eq_right (by change (1 : ℕ) ≠ 0; decide)]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.phaseT j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | controlledNot a b =>
    have hh := allWork_cnot work base a b d
    unfold entry QuantumAlgebraicHistory.gate
    simp only [gateTag]
    by_cases h : allWork (work,base,.controlledNot a b,d)=true
    · simp [h,hh.mp h]
    · have hn := mt hh.mpr h
      simp [h,hn]

end ContinuumCoulomb.QuantumGateEntryProgram

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

theorem sourceEntries_length (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    (sourceEntries k c hT).length = QuantumOrderedSourceIndex.termCount c := by
  rw [sourceEntries_table]
  simp only [QuantumOrderedLabelTable.table,List.length_ofFn,
    QuantumOrderedSourceIndex.termCount]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSweepCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal natural row/column tags for the sparse sweep.  The
three gates of each wire transfer carry the same column; the original gate
keeps its proved arrival column. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSweepCells
open QuantumCircuitCode

theorem transfer_columns {width work : ℕ}
    (l r : Fin (width+1) → Fin (work+1)) (xs : List (Fin (width+1))) :
    (qmaColumnTransfer l r xs).map (fun p => p.2.val)=
      repeatColumns (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [qmaColumnTransfer,List.flatMap_cons,List.map_append,
      qmaWireSwapGates,List.map_cons,List.map_nil,repeatColumns]
    simpa only [repeatColumns,qmaColumnTransfer,qmaWireSwapGates,List.map_cons,List.map_nil]
      using congrArg (fun ys => [j.val,j.val,j.val]++ys) ih

theorem columns_actual (width order : ℕ) :
    (List.ofFn (qmaSweepOrder width order)).map Fin.val=columns width order := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,columns,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,columns,List.getElem_range,
      sweepIndex_value]

theorem arrival_actual (width order : ℕ) (g : QMAGate) :
    (qmaGateArrivalColumn width (qmaSweepOrder width order) g).val=
      sweepIndex width order (rowCut width order g-1) := by
  rw [qmaGateArrivalColumn,sweepIndex_value]
  simp only [qmaGateArrivalIndex,rowCut_eq]

theorem rowColumns_actual (width work order : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (g : QMAGate) :
    (qmaTaggedRowStage width work l r (qmaSweepOrder width order) g).map
        (fun p => p.2.val)=rowColumns width order g := by
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    transfer_columns,List.map_take,List.map_drop,columns_actual,rowCut_eq,
    arrival_actual,rowColumns]

theorem rowCells_actual (rows width start : ℕ) (hs : start < rows) (g : QMAGate) :
    ((qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g).map
        (fun p => (p.1,((⟨start,by omega⟩ : Fin (rows+1)),p.2)))).map
        (fun p => (p.2.1.val,p.2.2.val))=rowCells rows width start g := by
  simpa only [List.map_map,Function.comp_def,rowCells] using
    congrArg (List.map (fun j => (start,j)))
      (rowColumns_actual width (qmaGridWork rows width) (rows-1-start)
        (qmaGridQubit rows width ⟨start,by omega⟩)
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)

theorem sweepCells_cons (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate) :
    sweepCells rows width start (g::gs)=
      rowCells rows width start g++sweepCells rows width (start+1) gs := by
  simp only [sweepCells,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
    List.flatMap_map,readGate,List.drop_zero,List.headD_cons,Nat.add_zero,List.drop_succ_cons]
  congr 1
  have h : (fun i => rowCells rows width (start+Nat.succ i)
      ((gs.drop i).headD (.hadamard 0)))=
      (fun i => rowCells rows width (start+1+i) ((gs.drop i).headD (.hadamard 0))) := by
    funext i
    congr 1
    omega
  rw [h]

theorem sweepCells_actual (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map
      (fun p => (p.2.1.val,p.2.2.val))=sweepCells rows width start gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    rw [sweepCells_cons]
    simp only [qmaTaggedSweepFrom,List.map_append]
    rw [rowCells_actual rows width start hs g,ih]

theorem value_actual (c : QMACircuit) :
    value c=(qmaSparseTags c).map (fun p => (p.2.1.val,p.2.2.val)) :=
  (sweepCells_actual _ _ _ _ _).symm

theorem value_length (c : QMACircuit) :
    (value c).length=(qmaSparseCircuit c).gates.length := by
  rw [value_actual,List.length_map,qmaSparseTags_length]

end ContinuumCoulomb.QuantumSweepCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Natural cell lookups for the actual sparse history.  The reference
lookup uses the same time-grouped descriptors as the sampled Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open QuantumHistoryDescriptors QuantumOrderedSourceIndex

theorem gateCell_actual (c : QMACircuit) (t : Fin (qmaSparseCircuit c).gates.length) :
    gateCell c t.val=encodeCell (qmaSparseGateCell c t) := by
  unfold gateCell
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [QuantumSweepCells.value_length]; exact t.isLt)]
  simp only [QuantumSweepCells.value_actual,List.getElem_map,encodeCell,
    qmaSparseGateCell,qmaSparseCell,Fin.val_cast,Option.getD_some]

theorem referenceCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (i : Fin (qmaHistoryReferenceWork (qmaSparseCircuit c)+1)) :
    referenceCell c i.val=encodeCell (qmaOrderedSparseReferenceCell c hT i) := by
  unfold referenceCell
  rw [orderedAt_actual _ hT i,time_encode _ hT]
  exact gateCell_actual c _

theorem qubitCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (q : QuantumOrderedSupport.Qubit (qmaSparseCircuit c)) :
    qubitCell c (QuantumOrderedSupport.siteNumber (qmaSparseCircuit c) q)=
      encodeCell (qmaOrderedQubitCell c hT q) := by
  rcases q with i | (b | w)
  · have hi : i.val < referenceWork (qmaSparseCircuit c)+1 := by
      simpa only [referenceWork_eq] using i.isLt
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hi,ite_true, if_true,
      qmaOrderedQubitCell,Sum.elim_inl]
    exact referenceCell_actual c hT i
  · change (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+b.val<
        qmaHistoryReferenceWork (qmaSparseCircuit c)+1 then _ else _)=_
    rw [ite_eq_right (by omega)]
    simp only [QuantumOrderedSupport.siteNumber,referenceWork_eq,Nat.add_sub_cancel_left]
    change (if b.val<(qmaSparseCircuit c).gates.length+2 then _ else _)=_
    rw [ite_eq_left b.isLt]
    exact gateCell_actual c (qmaClockAnchorIndex _ hT b)
  · have hnot : ¬qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val<
        referenceWork (qmaSparseCircuit c)+1 := by rw [referenceWork_eq]; omega
    have hd : qmaHistoryReferenceWork (qmaSparseCircuit c)+1+
        ((qmaSparseCircuit c).gates.length+2)+w.val-
        (referenceWork (qmaSparseCircuit c)+1)=
        (qmaSparseCircuit c).gates.length+2+w.val := by rw [referenceWork_eq]; omega
    simp only [qubitCell,QuantumOrderedSupport.siteNumber,hnot,ite_false, if_false,hd]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rfl

theorem termCell_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork (qmaSparseCircuit c))) :
    termCell c ((reference (qmaSparseCircuit c)).symm a).val=
      encodeCell (qmaOrderedTermCell c hT a) := by
  cases a with
  | inl i =>
    change referenceCell c (if i.val < referenceWork (qmaSparseCircuit c)+1
      then i.val else _)=_
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact referenceCell_actual c hT i
  | inr i =>
    change referenceCell c (if qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val<
      qmaHistoryReferenceWork (qmaSparseCircuit c)+1
      then qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val
      else qmaHistoryReferenceWork (qmaSparseCircuit c)+1+i.val-
        (qmaHistoryReferenceWork (qmaSparseCircuit c)+1))=_
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
    exact referenceCell_actual c hT i.castSucc

theorem qubitCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    qubitCells c=List.ofFn (fun i : Fin (qubitCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedQubitCell c hT (qubits (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [qubitCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [qubitCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (qubitCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    have he := congrFun (qubits_index (qmaSparseCircuit c)) (qubits (qmaSparseCircuit c) j)
    simp only [QuantumOrderedLabelTable.index,Equiv.symm_apply_apply] at he
    simpa only [←he] using qubitCell_actual c hT (qubits (qmaSparseCircuit c) j)

theorem referenceCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    referenceCells c=List.ofFn (fun i : Fin (referenceCount (qmaSparseCircuit c)) =>
      encodeCell (qmaOrderedTermCell c hT (reference (qmaSparseCircuit c) i))) := by
  apply List.ext_getElem
  · simp only [referenceCells,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [referenceCells,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    let j : Fin (referenceCount (qmaSparseCircuit c)) := ⟨i,by
      simpa only [List.length_ofFn] using hj⟩
    simpa only [Equiv.symm_apply_apply] using
      termCell_actual c hT (reference (qmaSparseCircuit c) j)

private theorem sourceTerms_first (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (referenceCount c*patternCount)) :
    (QuantumPaddedLabelProgram.sourceTerms c hT i).1=
      reference c (finProdFinEquiv.symm i).1 := by
  simp only [QuantumPaddedLabelProgram.sourceTerms,Equiv.trans_apply,
    Equiv.prodShear_apply]

private theorem anchors_source (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c) → ℕ × ℕ) :
    QuantumOrderedCellProgram.anchors patternCount
      (List.ofFn (fun i : Fin (referenceCount c) => a (reference c i)))=
      List.ofFn (fun i : Fin (referenceCount c*patternCount) =>
        a (QuantumPaddedLabelProgram.sourceTerms c hT i).1) := by
  rw [QuantumOrderedCellProgram.anchors_ofFn]
  rw [←QuantumOrderedLabelTable.product_table (fun p :
    Fin (referenceCount c) × Fin patternCount => a (reference c p.1))]
  apply congrArg List.ofFn
  funext i
  rw [sourceTerms_first]

theorem value_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    value c=QuantumOrderedCellTable.table (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (fun q => encodeCell (qmaOrderedQubitCell c hT q))
      (fun a => encodeCell (qmaOrderedTermCell c hT a.1)) := by
  apply Prod.ext
  · exact qubitCells_actual c hT
  · change QuantumOrderedCellProgram.anchors patternCount (referenceCells c)=_
    rw [referenceCells_actual c hT]
    dsimp only [QuantumOrderedCellTable.table]
    exact anchors_source (qmaSparseCircuit c) hT (fun a => encodeCell (qmaOrderedTermCell c hT a))

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryComparison
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

theorem value_iff (x : Input) : value x=true ↔
    ∀ i : Fin x.1, row x.2.2.2.2 (x.2.1+i.val) =
      if x.2.2.1=true ∧ x.2.1+i.val=x.2.2.2.1 then
        Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+i.val))
      else column x.2.2.2.2 (x.2.1+i.val) := by
  simp only [value,List.all_map,List.all_eq_true,List.mem_range,
    Function.comp_apply,id_eq,point,decide_eq_true_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem no_flip_iff (count base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      ∀ i : Fin count, row d (base+i.val)=column d (base+i.val) := by
  rw [value_iff]
  simp only [Bool.false_eq_true,false_and,ite_false, if_false]

theorem value_equiv_iff {ι : Type} {count : ℕ} (e : ι ≃ Fin count)
    (base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      (fun i => row d (base+(e i).val))=(fun i => column d (base+(e i).val)) := by
  rw [no_flip_iff,funext_iff]
  constructor
  · intro h i
    exact h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact h j

theorem value_flip_iff {ι : Type} [DecidableEq ι] {count : ℕ} (e : ι ≃ Fin count)
    (base : ℕ) (q : ι) (d : Data) :
    value (count,base,true,base+(e q).val,d)=true ↔
      (fun i => row d (base+(e i).val))=
        qmaBitFlip q (fun i => column d (base+(e i).val)) := by
  rw [value_iff,funext_iff]
  have hv (i : ι) (hi : i≠q) : (e i).val≠(e q).val :=
    fun h => hi (e.injective (Fin.ext h))
  constructor
  · intro h i
    by_cases hi : i=q
    · subst i
      simpa [qmaBitFlip] using h (e q)
    · simpa [qmaBitFlip,hi,hv i hi] using h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    by_cases hj : j=q
    · subst j
      simpa [qmaBitFlip] using h q
    · simpa [qmaBitFlip,hj,hv j hj] using h j

end ContinuumCoulomb.QuantumHistoryComparison

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact register evaluation of the propagation delta.  The equality scans
are bounded by the unary circuit size; every bit is read from the supplied
local support table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open QuantumAlgebraicScalar QuantumHistoryDescriptors QuantumHistoryBitProgram
open QuantumHistoryDiagonal QuantumHistorySiteProgram

theorem qubitEquiv_val (c : QMACircuit) (q : QMACircuitQubit c) :
    (qubitEquiv c q).val=distributedNumber c q := by
  cases q <;> rfl

theorem readRow_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readRow c d q=row d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (row d) (number_inr c q)

theorem readColumn_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readColumn c d q=column d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (column d) (number_inr c q)

theorem guard_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    guard c t.val d=true ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
  have he : (clockRow c d t.val=1 ∧ clockRow c d (t.val+2)=0 ∧
      clockRow c d (t.val+1)=0) ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
    simp only [QMAClockGuard,Function.comp_apply,readRow,QuantumOrderedSupport.siteNumber,
      clockRow,referenceWork_eq,qmaClockLeft,qmaClockRight,qmaClockMiddle,and_assoc]
  exact ⟨fun h => he.mp (of_decide_eq_true h),fun h => decide_eq_true (he.mpr h)⟩

theorem flipped_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    flipped c t.val d=true ↔ readRow c d=
      qmaBitFlip (.inl (qmaClockMiddle c.gates.length t)) (readColumn c d) := by
  have h := QuantumHistoryComparison.value_flip_iff (qubitEquiv c)
    (referenceWork c+1) (.inl (qmaClockMiddle c.gates.length t)) d
  have he : (qubitEquiv c (.inl (qmaClockMiddle c.gates.length t))).val=t.val+1 := rfl
  change QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t.val+1),d)=true ↔ _
  simpa only [he,← readRow_eq,← readColumn_eq] using h

theorem sameClock_iff (c : QMACircuit) (d : Data) :
    sameClock c d=true ↔ readRow c d ∘ Sum.inl=readColumn c d ∘ Sum.inl := by
  have h := QuantumHistoryComparison.value_equiv_iff
    (Equiv.refl (Fin (c.gates.length+2))) (referenceWork c+1) 0 d
  simpa only [sameClock,Equiv.refl_apply,readRow,readColumn,
    QuantumOrderedSupport.siteNumber,referenceWork_eq,Function.comp_def] using h

theorem gate_entry (c : QMACircuit) (t : ℕ) (d : Data) :
    QuantumGateEntryProgram.entry
      (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)=
      QuantumAlgebraicHistory.gate c.work (gateAt (c,t))
        (readRow c d ∘ Sum.inr) (readColumn c d ∘ Sum.inr) := by
  rw [QuantumGateEntryProgram.entry_eq]
  rfl

theorem entry_actual (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    entry c t.val d=QuantumAlgebraicHistory.delta c t (readRow c d) (readColumn c d) := by
  unfold entry QuantumAlgebraicHistory.delta QuantumAlgebraicHistory.identity
  rw [gate_entry]
  simp only [flipped_iff c t d,sameClock_iff c d,gateAt]
  by_cases hg : guard c t.val d=true
  · have hh := (guard_iff c t d).mp hg
    simp only [hg,hh,and_self,ite_true, if_true]
  · have hh := mt (guard_iff c t d).mpr hg
    simp only [hg,hh,Bool.false_eq_true,ite_false, if_false]

end ContinuumCoulomb.QuantumHistoryDelta

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

theorem historyQubits_eq (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    historyQubits c hT N=4*(qubitCount c+3717*termCount c) := by
  unfold historyQubits historyInput QuantumOrderedLabelCompile.qubitCount
  rw [QuantumOrderedLabelPipeline.output_qubits,sourceEntries_length]

end ContinuumCoulomb.QuantumPaddedLabelProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier history has a fixed-density, degree-three
spatial exchange output. Its energy is that of the literal fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedHistory QuantumOrderedSourceIndex QuantumPaddedLabelProgram
open QuantumForkList
open scoped Classical

theorem input_state (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).state=forkState (qmaSparseCircuit c) hT N historyDegree := by
  unfold SpatialInput.state forkState historyQubits historyOutput historyInput
  rw [sourceEntries_table]
  rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sparse verifier compiler, through the specified planar lattice.
The final precision pays for every early and routing error; the scalar offset
is removed from both thresholds exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumForkList QuantumAlgebraicHistory
open scoped Classical

-- Keep the fixed density symbolic; expanding it as a numeral is unnecessary.
attribute [local irreducible] spatialDensity

theorem iterate_count_ge (N : ℚ) (s : State) (k : ℕ) : s.1 ≤ (iterate N k s).1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change s.1 ≤ (iterate N k s).1+2*pairCount (iterate N k s).2.2.2
    exact ih.trans (Nat.le_add_right _ _)

theorem model_vertices_ge (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    historyQubits (qmaSparseCircuit c) hT N ≤ (model c hc hT hne N).n := by
  change _ ≤ (input c hc hT hne N).state.1
  rw [input_state]
  let s := initial (historyQubits (qmaSparseCircuit c) hT N)
    (historyOutput (qmaSparseCircuit c) hT N).1 (historyOutput (qmaSparseCircuit c) hT N).2 (N:ℚ)
  exact (show historyQubits (qmaSparseCircuit c) hT N ≤ s.1 from Nat.le_add_right _ _).trans
    (iterate_count_ge (N:ℚ) s historyDegree)

theorem model_vertices_pos (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    0 < (model c hc hT hne N).n := by
  have hp : 0 < historyQubits (qmaSparseCircuit c) hT N := by
    rw [historyQubits_eq,QuantumOrderedSourceIndex.qubitCount_eq]
    omega
  exact hp.trans_le (model_vertices_ge c hc hT hne N)

theorem routeRounds_eq : QMASpatialExchangeModel.routeLengthBound
    (spatialDensity rawDensity historyDegree) (27*spatialDensity rawDensity historyDegree) =
      routeRounds := routeRoundValue.property

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRoutingFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal enumeration of every coarse route and source center. These are
the exact lists consumed by the finite crossing and permission tables. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingFamily
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumRoutingInputProgram

theorem coarse_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    coarse A B (actualData M labels) = List.ofFn (fun e : Fin m =>
      ((M.withOrdinalSlots labels).bufferedPath hd (labels.symm e)).val.support) := by
  apply List.ext_getElem
  · simp only [coarse,actualData,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    have h := path_actual M labels hA hd (labels.symm ⟨i,hi'⟩)
    simpa only [coarse,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      Equiv.apply_symm_apply] using h

end ContinuumCoulomb.QuantumRoutingFamily

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialInputTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed fork-state/cell tape is exactly the array of the spatial
model. Only cells at actual spin indices are read. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialInputTape
open QuantumForkList QuantumForkGridProgram QuantumRouteCode

private theorem iterate_coordinates {rows width : ℕ} (N : ℚ) (s : State)
    (cell : ℕ → QMAGridCell rows width) (k : ℕ) :
    iterateCell N k s (coordinates ∘ cell) = coordinates ∘ iterateCell N k s cell := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext v
    simp only [iterateCell,nextCell,Function.comp_apply]
    split <;> exact congrFun ih _

theorem state_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    (output D (input I)).1 = I.state := output_state D (input I)

private theorem prepare_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (prepare (input I)).2 (coordinates ∘ initialCell I.n I.bonds I.cell) := by
  intro v hv
  change v < I.n+2*I.bonds.length at hv
  change lookup (initialCells (I.n,I.bonds,
    List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  rw [lookup_initialCells _ v hv]
  change initialCell I.n I.bonds
    (lookup (List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  by_cases h : v < I.n
  · simp only [Function.comp_apply,initialCell,h,ite_true, if_true]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨v,h⟩
  · have hb : v-I.n < 2*I.bonds.length := by
      change v < I.n+2*I.bonds.length at hv
      omega
    have he := initialEndpoint_bound I.n I.bonds I.bounded (v-I.n) hb
    simp only [initialCell,h,ite_false, if_false,Function.comp_apply]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨_,he⟩

theorem output_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (output D (input I)) (coordinates ∘ I.cells) := by
  have h := run_represents D (prepare (input I)) (initial_validPorts _ _ _ _)
    (coordinates ∘ initialCell I.n I.bonds I.cell) (prepare_represents_input I)
  change Represents (output D (input I))
    (iterateCell I.precision D (initial I.n I.bonds I.constant I.precision)
      (coordinates ∘ initialCell I.n I.bonds I.cell)) at h
  rw [iterate_coordinates] at h
  exact h

theorem output_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    output D (input I) =
      (I.state,List.ofFn (fun v : Fin I.state.1 => coordinates (I.cells v.val))) := by
  apply Prod.ext
  · exact state_eq I
  · apply List.ext_getElem
    · rw [List.length_ofFn,output_length,state_eq]
    · intro i hi hj
      have hi' : i < I.state.1 := by simpa only [List.length_ofFn] using hj
      have h := output_represents_input I i (by rwa [state_eq])
      simpa only [lookup,List.headD_eq_head?_getD,List.head?_drop,
        List.getElem?_eq_getElem hi,Option.getD_some,Function.comp_apply,
        List.getElem_ofFn] using h

theorem routing_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    QuantumForkRoutingData.value (output D (input I)) =
      QuantumRoutingInputProgram.actualData I.model (Equiv.refl _) := by
  rw [output_eq]
  exact QuantumForkRoutingData.value_spatialModel I.state I.validPorts I.state_bounded
    I.state_noLoops I.cells (spatialDensity A D) I.state_density I.state_degree I.state_locality

end ContinuumCoulomb.QuantumSpatialInputTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed port paths decorate the actual full bond list with its
remaining subdivision work. Erasing that work leaves the same Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleTape
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

theorem entries_ofFn {m : ℕ} (bs : Fin m → Bond) (ps : Fin m → List Pair) :
    entries (List.ofFn bs,List.ofFn ps) = List.ofFn (fun i => ((ps i).length-1,bs i)) := by
  apply List.ext_getElem
  · simp only [entries,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hi' : i < m := by simpa only [List.length_ofFn] using hj
    simp only [entries,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      entry,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
      dite_eq_left hi',Option.getD_some]

end ContinuumCoulomb.QuantumPortScheduleTape

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortScheduleActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed schedule has precisely the coefficients, work counts and
physical port paths of the proved spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortScheduleActual
open QuantumForkList QuantumRouteCode QuantumPortScheduleTape

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)

theorem bonds_ofFn : fullList I.state = List.ofFn (fun e : I.model.Term =>
    ((I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change fullList I.state = List.ofFn (fun i => (fullList I.state).get i)
  exact (List.ofFn_get (fullList I.state)).symm

include hA in
theorem entries_actual :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1.2.2 =
      List.ofFn (fun e : I.model.Term =>
        (I.model.coarseLength I.model_degree e,
          (I.model.left e).val,(I.model.right e).val,I.model.weight e)) := by
  change entries (fullList (tape I).1,
    QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumForkRoutingData.value (tape I))) = _
  rw [QuantumSpatialInputTape.state_eq,QuantumSpatialInputTape.routing_eq]
  have hp : QuantumRoutingFamily.coarse (spatialDensity A D) (27*spatialDensity A D)
      (QuantumRoutingInputProgram.actualData I.model (Equiv.refl _)) =
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support) :=
    QuantumRoutingFamily.coarse_actual I.model (Equiv.refl _) hA I.model_degree
  rw [hp]
  calc
    _ = entries (List.ofFn (fun e : I.model.Term =>
        ((I.model.left e).val,(I.model.right e).val,I.model.weight e)),
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)) :=
      congrArg (fun bs => entries (bs,
        List.ofFn (fun e : I.model.Term => (I.model.bufferedPath I.model_degree e).val.support)))
        (bonds_ofFn I)
    _ = _ := by
      refine (entries_ofFn (m := (fullList I.state).length)
        (fun e => ((I.model.left e).val,(I.model.right e).val,I.model.weight e))
        (fun e => (I.model.bufferedPath I.model_degree e).val.support)).trans ?_
      apply congrArg List.ofFn
      funext e
      apply Prod.ext
      · simp only [SimpleGraph.Walk.length_support,Nat.add_sub_cancel]
        rfl
      · rfl

end ContinuumCoulomb.QuantumPortScheduleActual

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPortSchedulePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual computed scheduler begins with the exact spatial exchange
graph, with one work counter for each of its enumerated interactions. -/

noncomputable section

namespace ContinuumCoulomb.QuantumPortSchedulePacking
open QuantumForkList QuantumPortScheduleTape QuantumPortScheduleActual

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
variable (hA : 0 < spatialDensity A D)
include hA

theorem state_eq :
    (value (spatialDensity A D) (27*spatialDensity A D) (tape I)).1 =
      QuantumPackedSchedule.state I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree) := by
  apply Prod.ext
  · change (tape I).1.1=I.model.n
    rw [QuantumSpatialInputTape.state_eq]
    rfl
  · apply Prod.ext
    · change (tape I).1.2.2.1=I.model.constant
      rw [QuantumSpatialInputTape.state_eq]
      rfl
    · exact entries_actual I hA

end ContinuumCoulomb.QuantumPortSchedulePacking

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the four-rational local-core sums.  This lets the
literal support-list coordinates evaluate the propagation Gram matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators

private theorem scalar_add_eq (x y : Scalar) : add x y=x+y := rfl
theorem scalar_sum_eq (xs : List Scalar) : QuantumAlgebraicScalar.sum xs=xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [QuantumAlgebraicScalar.sum,ih,List.sum_cons,scalar_add_eq]

theorem scalar_finiteSum_eq {α : Type} [Fintype α] (f : α → Scalar) :
    finiteSum f=∑ a,f a := by
  rw [finiteSum,scalar_sum_eq]
  simp only [enumerate,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin α).symm.sum_comp f

theorem scalar_finiteSum_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → Scalar) :
    finiteSum (fun a => f (e a))=finiteSum f := by
  rw [scalar_finiteSum_eq,scalar_finiteSum_eq]
  exact e.sum_comp f

theorem matMul_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix β β Scalar) :
    matMul (reindex e A) (reindex e B)=reindex e (matMul A B) := by
  funext s t
  exact scalar_finiteSum_reindex e (fun u => mul (A (e s) u) (B u (e t)))

theorem adjoint_reindex {α β : Type} (e : α ≃ β) (A : Matrix β β Scalar) :
    adjoint (reindex e A)=reindex e (adjoint A) := rfl

theorem gram_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix β β Scalar) :
    matMul (adjoint (reindex e A)) (reindex e A)=
      reindex e (matMul (adjoint A) A) := by
  rw [adjoint_reindex,matMul_reindex]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal, duplicate-free five-site propagation support.  Lookup in its
encoded labels agrees with the zero extension used by the actual local core. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSupport
open QuantumHistoryBitProgram QuantumHistoryDiagonal QuantumOrderedSupport
open scoped Classical

theorem supportEquiv_apply (c : QMACircuit) (t : Fin c.gates.length)
    (i : Fin (sites c t).length) : (supportEquiv c t i).val=(sites c t).get i := rfl

theorem lookup_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s : Fin (sites c t).length → Fin 2) (q : QMACircuitQubit c) :
    QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
      List.ofFn (fun i => (s i).val))=
      (qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q).val := by
  have hf : Function.Injective (fun q : QMACircuitQubit c => siteNumber c (.inr q)) := by
    intro a b h
    exact Sum.inr_injective (siteNumber_injective c h)
  by_cases hq : q∈qmaPropagationSites c t
  · let i := (supportEquiv c t).symm ⟨q,hq⟩
    have hi : (sites c t).get i=q :=
      congrArg Subtype.val ((supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumSupportLookup.value_map_get (sites c t) (sites_nodup c t)
      (fun q => siteNumber c (.inr q)) hf (fun j => (s j).val) i
    have hv : QuantumSupportLookup.value (siteNumber c (.inr q),labels c t,
        List.ofFn (fun j => (s j).val))=(s i).val := by
      simpa only [hi,labels] using he
    exact hv.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=s i from dite_eq_left hq)).symm
  · have hn : siteNumber c (.inr q)∉labels c t := by
      intro h
      obtain ⟨p,hp,he⟩ := List.mem_map.mp h
      have hpq := hf he
      subst p
      exact hq (by rw [← sites_finset]; exact List.mem_toFinset.mpr hp)
    have he := QuantumSupportLookup.value_not_mem (labels c t)
      (List.ofFn (fun i => (s i).val)) (siteNumber c (.inr q)) hn
      (by simp only [List.length_ofFn,labels,List.length_map,le_refl])
    exact he.trans (congrArg Fin.val (show
      qmaSupportExtend (qmaPropagationSites c t)
        (fun j => s ((supportEquiv c t).symm j)) q=0 from dite_eq_right hq)).symm

theorem readRow_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readRow c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => s ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

theorem readColumn_actual (c : QMACircuit) (t : Fin c.gates.length)
    (s r : Fin (sites c t).length → Fin 2) :
    readColumn c (data c t s r)=qmaSupportExtend (qmaPropagationSites c t)
      (fun j => r ((supportEquiv c t).symm j)) := by
  funext q
  apply Fin.ext
  change QuantumSupportLookup.value _ % 2 = _
  dsimp only [data]
  rw [lookup_actual]
  exact Nat.mod_eq_of_lt (Fin.isLt _)

end ContinuumCoulomb.QuantumPropagationSupport

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

theorem table_actual (c : QMACircuit) (t : Fin c.gates.length) :
    table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)=
      reindex (supportBasisEquiv c t) (deltaCore c t) := by
  funext s r
  change QuantumHistoryDelta.entry c t.val (QuantumPropagationSupport.data c t s r)=_
  rw [QuantumHistoryDelta.entry_actual,QuantumPropagationSupport.readRow_actual,
    QuantumPropagationSupport.readColumn_actual]
  rfl

theorem gram_actual (c : QMACircuit) (t : Fin c.gates.length) :
    matMul (adjoint (table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)))
      (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t))=
      reindex (supportBasisEquiv c t) (propagationCore c t) := by
  rw [table_actual,gram_reindex]
  rfl

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumScalarFaithful
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four rational registers faithfully represent their complex value.
This permits exact local-table identities to reuse the established complex
matrix identities, without changing the arithmetic program. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

theorem sqrtHalf_irrational : Irrational (Real.sqrt (1/2 : ℝ)) := by
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,one_div]
  exact irrational_sqrt_two.inv

theorem realValue_injective : Function.Injective realValue := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : b=d := by
    by_contra hbd
    have hi := (sqrtHalf_irrational.ratCast_mul (sub_ne_zero.mpr hbd)).ratCast_add (a-c)
    have hz : ((a-c : ℚ) : ℝ)+((b-d : ℚ) : ℝ)*Real.sqrt (1/2 : ℝ)=0 := by
      dsimp only [realValue] at h
      push_cast
      nlinarith [h]
    rw [hz] at hi
    exact not_irrational_zero hi
  have ha : a=c := by
    subst d
    have he : (a:ℝ)=(c:ℝ) := by
      dsimp only [realValue] at h
      linarith
    exact_mod_cast he
  exact Prod.ext ha hb

theorem value_injective : Function.Injective value := by
  intro x y h
  apply Prod.ext
  · apply realValue_injective
    simpa only [value_re] using congrArg Complex.re h
  · apply realValue_injective
    simpa only [value_im] using congrArg Complex.im h

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumRebitLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact scalar core of a lifted term with one active reference qubit.
Spectator reference bits are zero in the local core and contribute identities. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical BigOperators

theorem referenceState_eq_iff (n : ℕ) (i : Fin n) (a b : Fin 2) :
    referenceState n i a=referenceState n i b ↔ a=b := by
  constructor
  · intro h
    simpa only [referenceState,ite_true, if_true] using congrFun h i
  · rintro rfl
    rfl

theorem reference_identity (n : ℕ) (i : Fin n) (a b : Fin 2) :
    identity (referenceState n i a) (referenceState n i b)=identity a b := by
  simp only [identity,referenceState_eq_iff]

theorem localY_referenceState (n : ℕ) (i : Fin n) (a b : Fin 2) :
    localY n i (referenceState n i a) (referenceState n i b)=
      QuantumFixedPauli.pauli 2 a b := by
  apply value_injective
  rw [value_localY,value_pauli]
  change sourceLocalPauli n i 1 (referenceState n i a) (referenceState n i b)=
    ContinuumCoulomb.pauli 1 a b
  unfold sourceLocalPauli sourceTensor
  rw [Finset.prod_eq_single i]
  · simp only [ite_true, if_true,referenceState,ite_true]
  · intro j _ hji
    simp only [hji,ite_false, if_false,referenceState,Matrix.one_apply,ite_true, if_true]
  · simp

theorem lift_extend {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (u v : QMASupportBasis S) :
    lift S A (qmaSupportExtend S u) (qmaSupportExtend S v)=A u v := by
  have hu : (fun j : {j // j∈S} => qmaSupportExtend S u j.val)=u := by
    funext j
    exact dite_eq_left j.property
  have hv : (fun j : {j // j∈S} => qmaSupportExtend S v j.val)=v := by
    funext j
    exact dite_eq_left j.property
  have he : (fun j : {j // j∉S} => qmaSupportExtend S u j.val)=
      (fun j : {j // j∉S} => qmaSupportExtend S v j.val) := by
    funext j
    have hu0 : qmaSupportExtend S u j.val=0 := dite_eq_right j.property
    have hv0 : qmaSupportExtend S v j.val=0 := dite_eq_right j.property
    exact hu0.trans hv0.symm
  simp only [lift,hu,hv,identity,ite_eq_left he]
  apply value_injective
  simp only [value_mul,value_rat,Rat.cast_one,mul_one]

theorem rebit_entry_of_references {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (a b : Fin 2)
    (hs : s ∘ Sum.inl=referenceState n i a)
    (ht : t ∘ Sum.inl=referenceState n i b) :
    rebit n i A s t=oneReference a b (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  simp only [rebit,hs,ht,reference_identity,localY_referenceState,oneReference]

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationOrder
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open QuantumOrderedSupport
open scoped Classical

theorem firstIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (supportEquiv c hT (.inl i) (firstIndex c hT i t ht)).val=.inl i := by
  rw [supportEquiv_apply]
  change (sites c hT (.inl i))[0]'(firstIndex c hT i t ht).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_zero]

theorem nextIndex_site (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    (supportEquiv c hT (.inl i) (nextIndex c hT i t ht j)).val=
      .inr (QuantumPropagationSupport.supportEquiv c t j).val := by
  rw [supportEquiv_apply,QuantumPropagationSupport.supportEquiv_apply]
  change (sites c hT (.inl i))[j.val+1]'(nextIndex c hT i t ht j).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_succ,List.getElem_map,
    List.get_eq_getElem]

theorem extend_reference (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inl=
      QuantumAlgebraicHistory.referenceState (qmaHistoryReferenceWork c+1) i
        (referenceBit c hT i t ht s) := by
  funext j
  by_cases hj : j=i
  · subst j
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (firstIndex c hT i t ht)
    rw [firstIndex_site c hT i t ht] at he
    simpa [QuantumAlgebraicHistory.referenceState,referenceBit] using he
  · have hn : Sum.inl j ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      rw [← rawSites_finset] at hm
      have hl := List.mem_toFinset.mp hm
      change Sum.inl j ∈ Sum.inl i :: _ at hl
      rcases List.mem_cons.mp hl with he | he
      · exact hj (Sum.inl_injective he)
      · obtain ⟨q,_,he⟩ := List.mem_map.mp he
        cases he
    have hz : QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inl j)=0 :=
      dite_eq_right hn
    simpa only [Function.comp_apply,QuantumAlgebraicHistory.referenceState,
      ite_eq_right hj] using hz

theorem extend_data (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inr=
      qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) := by
  funext q
  by_cases hq : q∈qmaPropagationSites c t
  · let j := (QuantumPropagationSupport.supportEquiv c t).symm ⟨q,hq⟩
    have hj : (QuantumPropagationSupport.supportEquiv c t j).val=q :=
      congrArg Subtype.val ((QuantumPropagationSupport.supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (nextIndex c hT i t ht j)
    rw [nextIndex_site c hT i t ht,hj] at he
    exact he.trans (show qmaSupportExtend (qmaPropagationSites c t)
      (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=
      s (nextIndex c hT i t ht j) from dite_eq_left hq).symm
  · have hn : Sum.inr q ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      have hl : Sum.inr q ∈ (sites c hT (.inl i)).toFinset := by
        rw [sites_finset]
        exact hm
      have hx := List.mem_toFinset.mp hl
      rw [sites_eq c hT i t ht] at hx
      rcases List.mem_cons.mp hx with he | he
      · cases he
      · obtain ⟨r,hr,he⟩ := List.mem_map.mp he
        have hrq : r=q := Sum.inr_injective he
        subst r
        apply hq
        rw [← QuantumPropagationSupport.sites_finset]
        exact List.mem_toFinset.mpr hr
    have hz : qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=0 :=
      dite_eq_right hq
    exact (show QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inr q)=0 from
      dite_eq_right hn).trans hz.symm

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.propagationCore c t
            (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q))
            (fun q => localBits c hT i t ht r ((QuantumPropagationSupport.supportEquiv c t).symm q)))) := by
  let S := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s
  let R := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) r
  change QuantumAlgebraicHistory.rebit (qmaHistoryReferenceWork c+1) i
    (QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c)
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)) S R=_
  rw [QuantumAlgebraicHistory.rebit_entry_of_references _ _ _ _ _ _ _
    (extend_reference c hT i t ht s) (extend_reference c hT i t ht r)]
  rw [ht]
  change QuantumAlgebraicHistory.oneReference _ _
    (QuantumAlgebraicScalar.mul _ (QuantumAlgebraicHistory.lift _ _
      (S ∘ Sum.inr) (R ∘ Sum.inr)))=_
  have hs := extend_data c hT i t ht s
  have hr := extend_data c hT i t ht r
  change S ∘ Sum.inr=_ at hs
  change R ∘ Sum.inr=_ at hr
  rw [hs,hr,QuantumAlgebraicHistory.lift_extend]

theorem ordered_gram_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.matMul
            (QuantumAlgebraicHistory.adjoint
              (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
                (c,t.val,QuantumPropagationSupport.labels c t)))
            (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
              (c,t.val,QuantumPropagationSupport.labels c t))
            (localBits c hT i t ht s) (localBits c hT i t ht r))) := by
  rw [ordered_entry c hT i t ht]
  have hg := congrFun (congrFun (QuantumPropagationTable.gram_actual c t)
    (localBits c hT i t ht s)) (localBits c hT i t ht r)
  exact congrArg (fun z => QuantumAlgebraicHistory.oneReference
    (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
    (QuantumAlgebraicScalar.mul
      (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ)) z)) hg.symm

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPropagationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

theorem matrixData_cast {n m : ℕ} (h : n=m)
    (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) Scalar) :
    matrixData (reindex ((finCongr h).arrowCongr (Equiv.refl (Fin 2))) A)=matrixData A := by
  subst m
  rfl

theorem basisEquiv_zero (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    basisEquiv c hT i t ht s 0=QuantumPropagationOrder.referenceBit c hT i t ht s := by
  rfl

theorem basisEquiv_succ (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    (fun j => basisEquiv c hT i t ht s j.succ)=
      QuantumPropagationOrder.localBits c hT i t ht s := by
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i)=
      reindex (basisEquiv c hT i t ht)
        (table (QuantumPropagationSupport.sites c t).length
          (c,t.val,QuantumPropagationSupport.labels c t)) := by
  funext s r
  rw [QuantumPropagationOrder.ordered_gram_entry c hT i t ht]
  simp only [reindex,table,basisEquiv_zero,basisEquiv_succ,coefficient]

theorem tableList_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
        (c,t.val,QuantumPropagationSupport.labels c t)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) := by
  calc
    _ = tableList ((QuantumPropagationSupport.sites c t).length+1)
        (c,t.val,QuantumPropagationSupport.labels c t) :=
      congrArg (fun n => tableList n (c,t.val,QuantumPropagationSupport.labels c t))
        (QuantumPropagationOrder.length_eq c hT i t ht)
    _ = matrixData (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t)) := rfl
    _ = _ := (matrixData_cast (QuantumPropagationOrder.length_eq c hT i t ht) _).symm.trans
      (congrArg matrixData (table_actual c hT i t ht).symm)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumReferenceEdgeTable
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_rat _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_one _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.mul_zero _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.one_mul _root_.OAI.ContinuumCoulomb.QuantumGateScalarReduction.zero_mul _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local tables for the reference-chain edges.  Their only nontrivial
entry is the fixed two-spin expression (I-Y tensor Y)/2. -/

noncomputable section
namespace ContinuumCoulomb.QuantumReferenceEdgeTable
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumHistoryDiagonal
open QuantumHistoryBitProgram QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

theorem inactive (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
    (q : QuantumOrderedSupport.Qubit c)
    (hq : q≠.inl i.castSucc ∧ q≠.inl i.succ) :
    orderedExtend c hT (.inr i) s q=0 := by
  have hn : q∉(qmaOrderedHistoryModel c hT).sites (.inr i) := by
    change q∉{Sum.inl i.castSucc,Sum.inl i.succ}
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hq.1 h
    · exact hq.2 (Finset.mem_singleton.mp h)
  exact dite_eq_right hn

theorem ordered_entry (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2) :
    orderedTable c hT (.inr i) s t=
      table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i)) s t := by
  let S := orderedExtend c hT (.inr i) s
  let T := orderedExtend c hT (.inr i) t
  have hd : S ∘ Sum.inr=T ∘ Sum.inr := by
    funext q
    exact (inactive c hT i s (.inr q) (by simp)).trans
      (inactive c hT i t (.inr q) (by simp)).symm
  have hr : S ∘ Sum.inl=T ∘ Sum.inl ↔ s=t := by
    constructor
    · intro h
      apply orderedExtend_injective c hT (.inr i)
      funext q
      cases q with
      | inl j => exact congrFun h j
      | inr j => exact congrFun hd j
    · rintro rfl
      rfl
  have hs : ∀ k, k≠i.castSucc → k≠i.succ → S (.inl k)=T (.inl k) := by
    intro k hk hl
    exact (inactive c hT i s (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).trans
      (inactive c hT i t (.inl k) (by simpa only [ne_eq,Sum.inl.injEq] using And.intro hk hl)).symm
  have hb (u : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (v : Fin (QuantumOrderedSupport.sites c hT (.inr i)).length → Fin 2)
      (j : Fin (qmaHistoryReferenceWork c+1)) :
      row (data _ u v (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        orderedExtend c hT (.inr i) u (.inl j) :=
    QuantumHistoryBitProgram.row_actual c hT (.inr i) u v (.inl j)
  have hc (j : Fin (qmaHistoryReferenceWork c+1)) :
      column (data _ s t (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))) j.val=
        T (.inl j) :=
    QuantumHistoryBitProgram.column_actual c hT (.inr i) s t (.inl j)
  change referenceEdge (qmaHistoryReferenceWork c) i S T=_
  unfold referenceEdge pairY
  simp only [identity,hd,hr,Function.comp_apply,ite_true, if_true]
  rw [ite_eq_left hs]
  unfold table
  have hbl := hb s t i.castSucc
  have hbr := hb s t i.succ
  have hcl := hc i.castSucc
  have hcr := hc i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hbl hbr hcl hcr
  dsimp only [Prod.fst]
  rw [hbl,hcl,hbr,hcr]
  apply value_injective
  simp only [identity,value_mul,value_sub,value_rat,Rat.cast_one,mul_one]
  rfl

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c)) :
    table (QuantumOrderedSupport.sites c hT (.inr i)).length
        (i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=
      orderedTable c hT (.inr i) := by
  funext s t
  exact (ordered_entry c hT i s t).symm

end ContinuumCoulomb.QuantumReferenceEdgeTable

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_conj _root_.OAI.ContinuumCoulomb.QuantumAlgebraicScalar.height_neg _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem table_eq (x : Input) (h : x.2.2.length≤6) : table x=localTable x.2.2.length x := by
  generalize hn : x.2.2.length=n at *
  interval_cases n <;> simp only [table,hn] <;> norm_num

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryTableCorrectness
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total table dispatcher agrees with the actual ordered history core,
including its canonical finite enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open QuantumHistoryDescriptors QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem nondiagonal_term (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : ¬(encode c a).1<4) :
    ∃ t : Fin c.gates.length, a=QuantumPropagationOrder.term c t := by
  rcases a with i | (b | (i | (u | t)))
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · exact ⟨t,rfl⟩

theorem propagationLabels_tail (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (QuantumOrderedSupport.encodedSites c hT (.inl i)).tail=
      QuantumPropagationSupport.labels c t := by
  simp only [QuantumOrderedSupport.encodedSites,QuantumPropagationOrder.sites_eq c hT i t ht,
    List.map_cons,List.tail_cons,List.map_map,Function.comp_def,QuantumPropagationSupport.labels]

theorem localTable_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    localTable (QuantumOrderedSupport.sites c hT a).length
      (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  cases a with
  | inl i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,i.val,QuantumOrderedSupport.encodedSites c hT (.inl i))=_
    have hi : i.val < referenceWork c+1 := i.isLt
    simp only [localTable,hi,ite_true, if_true,orderedAt_actual c hT i]
    by_cases ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4
    · rw [ite_eq_left ha]
      exact QuantumHistoryDiagonal.tableList_actual c hT i ha
    · rw [ite_eq_right ha]
      obtain ⟨t,ht⟩ := nondiagonal_term c
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) ha
      rw [ht,propagationLabels_tail c hT i t ht]
      exact QuantumPropagationSampler.tableList_actual c hT i t ht
  | inr i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inr i)).length
      (c,qmaHistoryReferenceWork c+1+i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=_
    have hi : ¬qmaHistoryReferenceWork c+1+i.val<qmaHistoryReferenceWork c+1 := by
      omega
    simp only [localTable,referenceWork_eq,hi,ite_false, if_false,Nat.add_sub_cancel_left]
    exact congrArg matrixData (QuantumReferenceEdgeTable.table_actual c hT i)

theorem table_actual (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    table (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  rw [table_eq _ (by
    simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using
      QuantumOrderedSupport.sites_length c hT a)]
  simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using localTable_actual c hT a

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySamplerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

attribute [local instance] OAI.ContinuumCoulomb.QuantumHistorySamplerProgram.finDecision
private theorem matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) : @matrixData β F A=@matrixData β G A := by
  cases Subsingleton.elim F G
  rfl

private theorem pair_matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) (xs : List ℕ) :
    (xs,@matrixData β F A)=(xs,@matrixData β G A) :=
  congrArg (fun ys : List Scalar => (xs,ys)) (matrixData_instances F G A)

theorem packet_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (i : Fin (QuantumOrderedSourceIndex.referenceCount c)) :
    packet (k,c) i.val=QuantumPaddedLabelProgram.uniformPacket
      (QuantumPaddedLabelProgram.sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)) := by
  let a := QuantumOrderedSourceIndex.reference c i
  have hi : ((QuantumOrderedSourceIndex.reference c).symm a).val=i.val :=
    congrArg Fin.val ((QuantumOrderedSourceIndex.reference c).symm_apply_apply i)
  have hl := supportLabels_actual c hT a
  rw [hi] at hl
  have hm := QuantumHistoryTableProgram.table_actual c hT a
  rw [hi] at hm
  have hp : (supportLabels c i.val,
      QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val))=
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) := by
    rw [hl,hm]
    exact pair_matrixData_instances
      (β := Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) _ _
      (QuantumAlgebraicHistory.orderedTable c hT a) (QuantumOrderedSupport.encodedSites c hT a)
  change QuantumPaddedLabelProgram.uniformPacket (k,
      (supportLabels c i.val,QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val)))=
    QuantumPaddedLabelProgram.uniformPacket (k,
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)))
  exact congrArg (fun p => QuantumPaddedLabelProgram.uniformPacket (k,p)) hp

theorem entries_actual (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    entries (k,c)=QuantumPaddedLabelProgram.sourceEntries k c hT := by
  unfold entries QuantumPaddedLabelProgram.sourceEntries
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact packet_actual k c hT i

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPrecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

theorem prepare_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    prepare (N,c)=QuantumPaddedLabelProgram.historyInput c hT N := by
  change (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumHistorySamplerProgram.entries (samplePrecision c N,c))=
    (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumPaddedLabelProgram.sourceEntries (samplePrecision c N) c hT)
  rw [QuantumHistorySamplerProgram.entries_actual _ c hT]

theorem output_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    output (N,c)=QuantumPaddedLabelProgram.historyOutput c hT N :=
  congrArg QuantumOrderedLabelCompile.output (prepare_actual N c hT)

theorem physicalQubits_actual (N : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    physicalQubits (N,c)=QuantumPaddedLabelProgram.historyQubits c hT N :=
  congrArg QuantumOrderedLabelCompile.qubitCount (prepare_actual N c hT)

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryOutputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient envelopes for the actual sparse-history and degree-three
spatial output, preserving the exact numeric output order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumPaddedHistory QuantumOrderedSourceIndex
open QuantumForkList
open scoped Classical

theorem input_bonds (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).bonds=(historyOutput (qmaSparseCircuit c) hT N).1 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_constant (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).constant=(historyOutput (qmaSparseCircuit c) hT N).2 := by
  unfold historyOutput historyInput
  rw [sourceEntries_table]
  rfl

theorem input_n (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    (input c hc hT hne N).n=historyQubits (qmaSparseCircuit c) hT N := by
  unfold historyQubits historyInput
  rw [sourceEntries_table]
  rfl

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRawCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed cell array has the exact physical-spin order of the raw
history compiler, including all six mediator layers and the four-spin blocks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryCells
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumOrderedSourceIndex
open QuantumOrderedLabelTable QuantumOrderedSpatialComplete

theorem map_cell6 {ι κ C D : Type} (f : C → D) (cell : ι → C) (anchor : κ → C) :
    cell6 (f ∘ cell) (f ∘ anchor)=f ∘ cell6 cell anchor := by
  funext q
  rcases q with q | q
  · rcases q with q | q
    · rcases q with q | q
      · rcases q with q | q
        · rcases q with q | q
          · rcases q with q | q <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem rawCells_actual (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) :
    rawCells c=List.ofFn (fun i : Fin
      (finalCount (qubitCount (qmaSparseCircuit c))
        (referenceCount (qmaSparseCircuit c)*patternCount)*4) =>
      encodeCell (QuantumOrderedOutputSpatial.physicalCell
        (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) i.val)) := by
  rw [rawCells,value_actual c hT,QuantumOrderedRawCells.value_table]
  apply congrArg List.ofFn
  funext i
  rw [QuantumOrderedOutputSpatial.physicalCell,
    QuantumRawCellLocality.blockCell_fin]
  change cell6 (encodeCell ∘ qmaOrderedQubitCell c hT)
      (encodeCell ∘ (fun p => qmaOrderedTermCell c hT p.1))
      (qubits6 (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (finProdFinEquiv.symm i).1)=_
  rw [map_cell6]
  simp only [Function.comp_apply,QuantumOrderedOutputSpatial.logicalCell,qmaFourBlockCell]

theorem rawCells_length (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (N : ℕ) :
    (rawCells c).length=QuantumPaddedLabelProgram.historyQubits
      (qmaSparseCircuit c) hT N := by
  rw [rawCells_actual c hT,List.length_ofFn,
    QuantumPaddedLabelProgram.historyQubits_eq,finalCount_eq]
  simp only [termCount]
  omega

theorem rawCells_get (c : QMACircuit)
    (hT : 0<(qmaSparseCircuit c).gates.length) (j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell (QuantumOrderedOutputSpatial.physicalCell
      (qubits (qmaSparseCircuit c))
      (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
      (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j) := by
  simp only [rawCells_actual c hT,List.getElem_ofFn]

theorem input_cell (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ) :
    (QuantumHistorySpatial.input c hc hT hne N).cell j=
      QuantumOrderedOutputSpatial.physicalCell (qubits (qmaSparseCircuit c))
        (QuantumPaddedLabelProgram.sourceTerms (qmaSparseCircuit c) hT)
        (qmaOrderedQubitCell c hT) (fun p => qmaOrderedTermCell c hT p.1) j := by
  simp only [QuantumHistorySpatial.input,QuantumOrderedOutputSpatial.input,id]

theorem rawCells_input_length (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    (rawCells c).length=(QuantumHistorySpatial.input c hc hT hne N).n := by
  rw [QuantumHistorySpatial.input_n]
  exact rawCells_length c hT N

theorem rawCells_input_get (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N j : ℕ)
    (hj : j<(rawCells c).length) :
    (rawCells c)[j]=encodeCell ((QuantumHistorySpatial.input c hc hT hne N).cell j) := by
  rw [input_cell]
  exact rawCells_get c hT j hj

end ContinuumCoulomb.QuantumHistoryCells

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySpatialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal sampled history and its row/column labels are combined into
the exact prepared input of the fixed-round fork compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatialProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open QuantumHistoryPrecisionProgram

theorem rawCells_input (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    QuantumHistoryCells.rawCells c=List.ofFn
      (fun i : Fin (QuantumHistorySpatial.input c hc hT hne N).n =>
        QuantumSpatialInputTape.coordinates
          ((QuantumHistorySpatial.input c hc hT hne N).cell i.val)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact QuantumHistoryCells.rawCells_input_length c hc hT hne N
  · intro j hj _
    rw [List.getElem_ofFn]
    simpa only [QuantumSpatialInputTape.coordinates,QuantumHistoryCells.encodeCell] using
      QuantumHistoryCells.rawCells_input_get c hc hT hne N j hj

theorem initialInput_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    initialInput (N,c)=
      ((QuantumHistorySpatial.input c hc hT hne N).precision,
        (QuantumHistorySpatial.input c hc hT hne N).n,
        (QuantumHistorySpatial.input c hc hT hne N).bonds,
        (QuantumHistorySpatial.input c hc hT hne N).constant) := by
  rw [initialInput,sparseInput,physicalQubits_actual N (qmaSparseCircuit c) hT,
    output_actual N (qmaSparseCircuit c) hT,QuantumHistorySpatial.input_n,
    QuantumHistorySpatial.input_bonds,QuantumHistorySpatial.input_constant]
  rfl

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0<(qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates≠[]) (N : ℕ) :
    prepared (N,c)=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input c hc hT hne N) := by
  unfold prepared QuantumSpatialInputTape.input
  rw [initialInput_actual c hc hT hne N,rawCells_input c hc hT hne N]

end ContinuumCoulomb.QuantumHistorySpatialProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPreparedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The particular sparse, nonempty circuit used by the history reduction,
with its literal program and unchanged verifier acceptance probability. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram
open BinaryEncoding

theorem qmaPreparedCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaPreparedCircuit c) (qmaPreparedCircuit_wellFormed c hc) psi=
      qmaAcceptance c hc psi := by
  exact (qmaSparseCircuit_acceptance (qmaNonemptyCircuit c)
    (qmaNonemptyCircuit_wellFormed c hc) psi).trans
      (qmaNonemptyCircuit_acceptance c hc psi)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryPreparedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty circuit, final unary precision, exact history cells and
rational promise thresholds are assembled without semantic input oracles. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPreparedProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

theorem precision_pos (c : QMACircuit) : 0<precision c :=
  QuantumAlgebraicHistory.finalPrecision_pos _ _

theorem thresholds_lt (c : QMACircuit) : (thresholds c).1<(thresholds c).2 :=
  QuantumAlgebraicHistory.xz_threshold_lt _

theorem prepared_actual (c : QMACircuit) (hc : c.WellFormed) :
    prepared c=QuantumSpatialInputTape.input
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)) :=
  QuantumHistorySpatialProgram.prepared_actual _ (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)

theorem finalInput_actual (c : QMACircuit) (hc : c.WellFormed) :
    finalInput c=
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) := by
  rw [finalInput,prepared_actual c hc]
  rfl

end ContinuumCoulomb.QuantumHistoryPreparedProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistorySourceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete literal circuit-to-source map, including nonempty padding,
sampling precision, fork and route programs, and rational thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode BinaryEncoding

theorem value_actual (c : QMACircuit) (hc : c.WellFormed) :
    value c=QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
      QuantumPaddedLabelProgram.historyDegree
      (((QuantumHistoryPreparedProgram.precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c)
          (QuantumHistoryPreparedProgram.precision c))),
        (QuantumAlgebraicHistory.xzYesThreshold (qmaPreparedCircuit c),
          QuantumAlgebraicHistory.xzNoThreshold (qmaPreparedCircuit c))) :=
  congrArg (QuantumFinalRoutingProgram.value QuantumHistorySpatial.rawDensity
    QuantumPaddedLabelProgram.historyDegree) (QuantumHistoryPreparedProgram.finalInput_actual c hc)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryRoutedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-space history comparison and verifier implications for the
literal circuit-to-lattice output, including empty-circuit preparation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

theorem routedState_actual (c : QMACircuit) (hc : c.WellFormed) :
    routedState c = QuantumFinalRoutingProgram.routed rawDensity historyDegree
      (((precision c:ℚ),QuantumSpatialInputTape.input
        (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
          (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))),
        thresholds c) :=
  congrArg (QuantumFinalRoutingProgram.routed rawDensity historyDegree) (finalInput_actual c hc)

theorem route_rounds_eq : QuantumSpatialPortProgram.rounds rawDensity historyDegree = routeRounds :=
  (QuantumSpatialPortProgram.rounds_eq rawDensity historyDegree).symm.trans routeRounds_eq

theorem routed_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖=1)
    (ha : 2/3 ≤ qmaAcceptance c hc psi) :
    QuantumListSchedule.energy (routedState c).1 ≤ ((thresholds c).1:ℝ) := by
  exact final_accepting totalRounds (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)
    (qmaPreparedCircuit_wellFormed c hc) (history_error c hc) psi hpsi
    ((qmaPreparedCircuit_acceptance c hc psi).symm ▸ ha)

theorem routed_rejecting (c : QMACircuit) (hc : c.WellFormed)
    (ha : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖=1 → qmaAcceptance c hc psi ≤ 1/3) :
    ((thresholds c).2:ℝ) ≤ QuantumListSchedule.energy (routedState c).1 := by
  apply final_rejecting totalRounds (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)
    (qmaPreparedCircuit_wellFormed c hc) (history_error c hc)
  intro psi hpsi
  exact (qmaPreparedCircuit_acceptance c hc psi).symm ▸ ha psi hpsi

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumSpatialFinalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Routing retains every original spin. This supplies positivity of the
emitted lattice size and its comparison with the history input size. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList

theorem crossing_count_le (A D : ℕ) (x : QuantumSpatialPortProgram.Input) :
    (QuantumSpatialPortProgram.value A D x).1.1 ≤
      (QuantumSpatialCrossingProgram.value A D x).1.1.1 := by
  change (QuantumSpatialPortProgram.value A D x).1.1 ≤
    (QuantumSpatialPortProgram.value A D x).1.1+_
  exact Nat.le_add_right _ _

theorem even_count_le (A D : ℕ) (x : Input) :
    (QuantumSpatialCrossingProgram.value A D x.1).1.1.1 ≤ (even A D x).1.1 := by
  change (QuantumSpatialCrossingProgram.value A D x.1).1.1.1 ≤
    (QuantumSpatialCrossingProgram.value A D x.1).1.1.1+_
  exact Nat.le_add_right _ _

theorem initial_count_le (A D : ℕ) (x : Input) :
    (QuantumSpatialPortProgram.initial A D x.1.2).1.1 ≤ (routed A D x).1.1 := by
  have hp := QuantumListRouteProgram.iterate_count_le x.1.1
    (QuantumSpatialPortProgram.initial A D x.1.2) (QuantumSpatialPortProgram.rounds A D)
  have hf := QuantumListRouteProgram.iterate_count_le x.1.1 (even A D x) rounds
  exact hp.trans ((crossing_count_le A D x.1).trans ((even_count_le A D x).trans hf))

theorem spatial_count_le {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) (N a b : ℚ) :
    I.model.n ≤ (routed A D ((N,QuantumSpatialInputTape.input I),a,b)).1.1 := by
  have h := initial_count_le A D ((N,QuantumSpatialInputTape.input I),a,b)
  have hi := congrArg (fun s : QuantumListSchedule.State => s.1)
    (QuantumPortSchedulePacking.state_eq I hA)
  have hh : (QuantumSpatialPortProgram.initial A D (QuantumSpatialInputTape.input I)).1.1 =
      I.model.n := hi
  exact hh ▸ h

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLiteralCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal circuit compiler satisfies the original Heisenberg yes/no
promise. Its scalar shift and finite edge order are those of the emitted tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram

theorem value_eq_latticeOutput (c : QMACircuit) :
    value c = QuantumListRouteProgram.latticeOutput (routedState c)
      (thresholds c).1 (thresholds c).2 := rfl

theorem routed_vertices_pos (c : QMACircuit) (hc : c.WellFormed) :
    0 < (routedState c).1.1 := by
  rw [routedState_actual c hc]
  exact (model_vertices_pos (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c)).trans_le
    (QuantumFinalRoutingProgram.spatial_count_le
      (QuantumHistorySpatial.input (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
        (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c) (precision c))
      finalDensity_pos (precision c) (thresholds c).1 (thresholds c).2)

theorem literal_accepting (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (value c).PolynomialPromise k)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (ha : 2/3 ≤ qmaAcceptance c hc psi) :
    value c ∈ (sourceHeisenbergPromise k).yes := by
  rw [value_eq_latticeOutput] at hp ⊢
  obtain ⟨hs,Q,hQ,hgrid⟩ := routed_realization c hc
  exact QuantumListRouteProgram.latticeOutput_yes _ hs Q hQ hgrid
    (routed_vertices_pos c hc) _ _ (thresholds_lt c) hp
    (routed_accepting c hc psi hpsi ha)

theorem literal_rejecting (c : QMACircuit) (hc : c.WellFormed) {k : ℕ}
    (hp : (value c).PolynomialPromise k)
    (ha : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    value c ∈ (sourceHeisenbergPromise k).no := by
  rw [value_eq_latticeOutput] at hp ⊢
  obtain ⟨hs,Q,hQ,hgrid⟩ := routed_realization c hc
  exact QuantumListRouteProgram.latticeOutput_no _ hs Q hQ hgrid
    (routed_vertices_pos c hc) _ _ (thresholds_lt c) hp
    (routed_rejecting c hc ha)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumPromisePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small power bounds for the unary tuples used by the actual coefficient
programs. The exponent is independent of the particular verifier. -/

namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

theorem power_base_change {n k : ℕ} (hn : 0 < n) : (n+2)^k ≤ (n+1)^(2*k) := by
  have h : n+2 ≤ (n+1)^2 := by nlinarith
  calc
    _ ≤ ((n+1)^2)^k := Nat.pow_le_pow_left h k
    _ = _ := (pow_mul _ _ _).symm

end ContinuumCoulomb.QuantumCoefficientPrograms

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial powers for the actual history coefficients. These
bounds are in the retained history-qubit count, not in an auxiliary circuit. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory
open QuantumCoefficientPrograms

theorem qubitCount_positive (c : QMACircuit) : 0 < qubitCount c := by
  rw [qubitCount_eq]
  omega

theorem time_le_qubitCount (c : QMACircuit) : c.gates.length ≤ qubitCount c := by
  rw [qubitCount_eq]
  omega

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Quantum_QuantumHistoryLiteralPromise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One polynomial promise exponent for the literal circuit-to-source
program, with the original verifier's empty circuits prepared explicitly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory QuantumOrderedSourceIndex QuantumCoefficientPrograms

theorem circuit_polynomialPromise : ∃ k : ℕ, 0 < k ∧
    ∀ (c : QMACircuit) (_hc : c.WellFormed), (value c).PolynomialPromise k := by
  obtain ⟨a,ha⟩ := source_data_power
  refine ⟨2*a+6,by omega,fun c hc => ?_⟩
  let d := qmaNonemptyCircuit c
  let hd := qmaNonemptyCircuit_wellFormed c hc
  let ht := qmaNonemptyCircuit_sparse_pos c
  let he := qmaNonemptyCircuit_nearest c
  let I := QuantumHistorySpatial.input d hd ht he (precision c)
  let n := qubitCount (qmaPreparedCircuit c)
  have hn : 0 < n := qubitCount_positive _
  obtain ⟨L,hL,hC,hx,hy,hw⟩ := ha d hd ht he
  have lift (m : ℕ) (hm : m ≤ (n+2)^a) : (m:ℝ) ≤ (n+1:ℝ)^(2*a+6) := by
    have hb : m ≤ (n+1)^(2*a+6) := hm.trans
      ((power_base_change hn).trans (pow_le_pow_right₀ (by omega : 1 ≤ n+1) (by omega)))
    exact_mod_cast hb
  have hsize : n ≤ I.model.n := by
    have h := model_vertices_ge d hd ht he (precision c)
    rw [QuantumPaddedLabelProgram.historyQubits_eq] at h
    have hn' : n ≤ 4*(qubitCount (qmaSparseCircuit d)+3717*termCount (qmaSparseCircuit d)) := by
      change n ≤ 4*(n+_)
      omega
    exact hn'.trans h
  rw [value_actual c hc]
  apply QuantumFinalRoutingProgram.spatial_polynomialPromise I finalDensity_pos
    (N := (precision c:ℚ)) (T := precision c) (n := n)
    (by exact_mod_cast precision_pos c) (model_vertices_pos d hd ht he (precision c)) hsize
    hL (by simp only [Rat.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ precision c)]; exact le_rfl)
    hC _ _ (xz_threshold_lt (qmaPreparedCircuit c)) (lift _ hx) (lift _ hy)
  · rw [route_rounds_eq]
    exact lift _ hw
  · exact final_threshold_gap_bound (qmaPreparedCircuit c) hn (time_le_qubitCount _) (by omega)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Reduction_SourceHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
QMA hardness of the field-free signed square-lattice Heisenberg
problem through a polynomial circuit compiler and full-space energy bounds.
-/

noncomputable section
namespace ContinuumCoulomb

theorem publishedCMPHardness_oai : PublishedCMPHardness := by
  obtain ⟨k,hk,hpromise⟩ := QuantumHistorySourceProgram.circuit_polynomialPromise
  refine ⟨k,hk,?_⟩
  intro P hP
  obtain ⟨V,hyes,hno⟩ := hP
  refine ⟨{
    map := QuantumHistorySourceProgram.fromVerifier V
    polynomialTime := QuantumHistorySourceProgram.fromVerifier_uniform V
    maps_yes := ?_
    maps_no := ?_
  }⟩
  · intro x hx
    obtain ⟨psi,hpsi,ha⟩ := hyes x hx
    exact QuantumHistorySourceProgram.literal_accepting (V.generate x) (V.wellFormed x)
      (hpromise _ (V.wellFormed x)) psi hpsi ha
  · intro x hx
    exact QuantumHistorySourceProgram.literal_rejecting (V.generate x) (V.wellFormed x)
      (hpromise _ (V.wellFormed x)) (hno x hx)

end ContinuumCoulomb

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.publishedCMPHardness_oai := @OAI.ContinuumCoulomb.publishedCMPHardness_oai
