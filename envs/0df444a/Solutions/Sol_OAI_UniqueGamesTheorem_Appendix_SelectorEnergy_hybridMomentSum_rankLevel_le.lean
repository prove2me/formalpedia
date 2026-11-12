-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:58.79153+00:00
-- url     : https://prove2.me/submissions/75c52283-4b17-46f9-8322-04bbc03678f4

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_RankLevelFilter_hybridDerivative_rankLevel_energy_le_strong

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K]

theorem natCard_linearMap [FiniteDimensional F2 C] : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

end UniqueGamesTheorem.Appendix.CompressionCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.evaluationCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

/-- The actual trace pairing is nondegenerate in its dual-map argument. -/
theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Exact trace-character orthogonality with the frequency sum unnormalized. -/
theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

/-- Fourier inversion obtained directly from the finite trace orthogonality sum. -/
theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

/-- Mixed Parseval with normalized primal expectation and unnormalized frequency sum. -/
theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

/-- Parseval for real functions and the real binary trace coefficients. -/
theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.evaluationCharacter_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

noncomputable section

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (rankLevel d f) S = if frequencyRank S = d then linearCoeff f S else 0 := by
  classical
  unfold rankLevel
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- The selected rank mass equals the normalized squared norm of the actual
rank projection. -/
theorem rankLevel_energy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) =
      ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  classical
  rw [← linear_parseval]
  simp only [linearCoeff_rankLevel]
  simp [Finset.sum_filter]

/-- Rank projection contracts the normalized L2 norm. -/
theorem rankLevel_energy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankLevel_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => sq_nonneg _)

theorem rankLevel_degree_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : d < frequencyRank S) :
    linearCoeff (rankLevel d f) S = 0 := by
  rw [linearCoeff_rankLevel, ite_eq_right (Nat.ne_of_gt hS)]

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Appendix.Restriction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

/-- Averaging any real observable over translates of any finite parametrized
perturbation preserves its normalized mean. -/
theorem real_translation_average {G N : Type*} [AddCommGroup G] [Fintype G]
    [Fintype N] [Nonempty N] (embed : N → G) (observable : G → ℝ) :
    (𝔼 t, 𝔼 n, observable (t + embed n)) = 𝔼 t, observable t := by
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 _n : N, 𝔼 t, observable t := by
      apply Finset.expect_congr rfl
      intro n _
      exact Fintype.expect_equiv (Equiv.addRight (embed n)) _ _ (fun _ => rfl)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

end UniqueGamesTheorem.Appendix.Restriction

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem spectralProjector_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) = ∑ Y with P Y, linearCoeff f Y ^ 2 := by
  classical
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_spectralProjector]
  split_ifs <;> simp

theorem selector_energy_sum {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) =
      ∑ Y : F →ₗ[F2] E, (selectorMultiplicity P Y : ℝ) * linearCoeff f Y ^ 2 := by
  classical
  simp_rw [spectralProjector_energy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    (∑ i : I, if P i Y then linearCoeff f Y ^ 2 else 0) =
        ∑ i : I with P i Y, linearCoeff f Y ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [selectorMultiplicity]

theorem selector_energy_sum_le {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) (M : ℝ)
    (hcount : ∀ Y : F →ₗ[F2] E, linearCoeff f Y ≠ 0 →
      (selectorMultiplicity P Y : ℝ) ≤ M) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) ≤ M * (𝔼 X, f X ^ 2) := by
  classical
  rw [selector_energy_sum, ← linear_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : linearCoeff f Y = 0
  · simp [hY]
  · exact mul_le_mul_of_nonneg_right (hcount Y hY) (sq_nonneg _)

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridMomentSum_le_of_uniform_energy (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (ζ : ℝ)
    (hζ : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
        (𝔼 N, hybridDerivative A B T f N ^ 2) ≤ ζ) :
    hybridMomentSum d f ≤ ζ * hybridSelectorEnergy d f := by
  classical
  unfold hybridMomentSum hybridSelectorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2) ≤
        𝔼 T, ζ * (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) := by
      apply Finset.expect_le_expect
      intro T _
      have hn : 0 ≤ 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2 :=
        Finset.expect_nonneg (fun N _ => sq_nonneg _)
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hζ s.val.1 s.val.2 T s.property) hn
    _ = ζ * (𝔼 T, 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) :=
      (Finset.mul_expect _ _ _).symm
    _ = ζ * (𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2) := by
      rw [hybridDerivative_energy_average]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixSubspaceCount
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace UniqueGamesTheorem.Fourier.MatrixSubspaceCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section GeneralField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Taking the image of an endomorphism reaches every actual subspace. -/
theorem endomorphism_range_surjective :
    Function.Surjective (fun f : V →ₗ[K] V => LinearMap.range f) := by
  intro S
  obtain ⟨T, hT⟩ := S.exists_isCompl
  exact ⟨S.projection T hT, Submodule.range_projection hT⟩

theorem card_subspaces_le_endomorphisms [Finite V] :
    Nat.card (Submodule K V) ≤ Nat.card (V →ₗ[K] V) := by
  let : Finite (V →ₗ[K] V) := Finite.of_injective
    (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Nat.card_le_card_of_surjective _ endomorphism_range_surjective

end GeneralField

section BinaryField

variable {C : Type*} [AddCommGroup C] [Module F2 C] [Module.Finite F2 C]

private theorem finite_color_space : Finite C :=
  Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective

theorem card_binary_subspaces_le :
    Nat.card (Submodule F2 C) ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite C := finite_color_space
  calc
    _ ≤ Nat.card (C →ₗ[F2] C) := card_subspaces_le_endomorphisms
    _ = _ := UniqueGamesTheorem.Appendix.CompressionCount.natCard_linearMap

theorem card_binary_subspaces_le_of_finrank_le (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (Submodule F2 C) ≤ 2 ^ (s * s) := by
  exact card_binary_subspaces_le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs))

end BinaryField

end UniqueGamesTheorem.Fourier.MatrixSubspaceCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCounting
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Frequency-conditioned counts of actual Hybrid pairs and derivative indices. -/
namespace UniqueGamesTheorem.Appendix.HybridCounting

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

private theorem comap_subtype_injective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (I A B : Submodule K V) (hA : A ≤ I) (hB : B ≤ I)
    (h : A.comap I.subtype = B.comap I.subtype) : A = B := by
  apply le_antisymm
  · intro x hx
    have hv : (⟨x, hA hx⟩ : I) ∈ A.comap I.subtype := hx
    rw [h] at hv
    exact hv
  · intro x hx
    have hv : (⟨x, hB hx⟩ : I) ∈ B.comap I.subtype := hx
    rw [← h] at hv
    exact hv

private theorem map_quotient_injective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (N A B : Submodule K V) (hA : N ≤ A) (hB : N ≤ B)
    (h : A.map N.mkQ = B.map N.mkQ) : A = B := by
  have aux (P Q : Submodule K V) (hQ : N ≤ Q)
      (he : P.map N.mkQ = Q.map N.mkQ) : P ≤ Q := by
    intro x hx
    have hm : N.mkQ x ∈ P.map N.mkQ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [he] at hm
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hm
    have hk : x - y ∈ N := by
      have hzero : x - y ∈ LinearMap.ker N.mkQ := by
        change N.mkQ (x - y) = 0
        rw [map_sub, heq, sub_self]
      simpa only [Submodule.ker_mkQ] using hzero
    have hz := Q.add_mem (hQ hk) hy
    simpa only [sub_add_cancel] using hz
  exact le_antisymm (aux A B hB h) (aux B A hA h.symm)

private theorem finite_submodules (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Finite (Submodule F2 V) := by
  let : Finite V := Finite.of_injective (Module.finBasis F2 V).equivFun
    (Module.finBasis F2 V).equivFun.injective
  exact Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]
  [Module F2 E] [Module F2 F] [FiniteDimensional F2 F]

/-- All actual Hybrid pairs for this frequency, with no ambient-dimension factor. -/
theorem card_hybrid_pairs_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {p : Submodule F2 E × Submodule F2 F //
      LinearIdentities.Hybrid Y p.1 p.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let P := {p : Submodule F2 E × Submodule F2 F //
    LinearIdentities.Hybrid Y p.1 p.2}
  let : Finite (Submodule F2 Y.range) := finite_submodules _
  let : Finite (Submodule F2 (F ⧸ Y.ker)) := finite_submodules _
  have hk (p : P) : Y.ker ≤ p.1.2 := by
    intro x hx
    apply p.2.2
    change Y x ∈ p.1.1
    rw [show Y x = 0 from hx]
    exact Submodule.zero_mem _
  let code (p : P) : Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker) :=
    ((p.1.1).comap Y.range.subtype, (p.1.2).map Y.ker.mkQ)
  have hi : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact comap_subtype_injective Y.range p.1.1 q.1.1 p.2.1 q.2.1
        (congrArg Prod.fst h)
    · exact map_quotient_injective Y.ker p.1.2 q.1.2 (hk p) (hk q)
        (congrArg Prod.snd h)
  have hq : finrank F2 (F ⧸ Y.ker) = finrank F2 Y.range := by
    have hquot := Y.ker.finrank_quotient_add_finrank
    have hrank := Y.finrank_range_add_finrank_ker
    omega
  have hleft := UniqueGamesTheorem.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := Y.range) d hY
  have hright := UniqueGamesTheorem.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := F ⧸ Y.ker) d (hq.trans_le hY)
  calc
    _ ≤ Nat.card (Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_le_card_of_injective code hi
    _ = Nat.card (Submodule F2 Y.range) * Nat.card (Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_prod _ _
    _ ≤ 2 ^ (d * d) * 2 ^ (d * d) := Nat.mul_le_mul hleft hright
    _ = _ := by rw [← pow_add]; congr 1; ring

variable [FiniteDimensional F2 E]

/-- The actual order-bounded index subtype injects into the conditioned pairs. -/
theorem card_hybridIndex_le_two (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let : Finite (Submodule F2 E) := finite_submodules _
  let : Finite (Submodule F2 F) := finite_submodules _
  let code (s : {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2}) :
      {p : Submodule F2 E × Submodule F2 F // LinearIdentities.Hybrid Y p.1 p.2} :=
    ⟨s.1.1, s.2⟩
  have hi : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    change (code s).1 = (code t).1
    exact congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective code hi).trans (card_hybrid_pairs_le Y d hY)

theorem card_hybridIndex_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (3 * d * d) := by
  apply (card_hybridIndex_le_two Y d hY).trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (d * d) (by decide : 2 ≤ 3)

end UniqueGamesTheorem.Appendix.HybridCounting

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.Globality

theorem energy_nonnegative {N : Type*} [Fintype N] (f : N → ℝ) :
    0 ≤ energy f := by
  exact Finset.expect_nonneg fun n _ => sq_nonneg (f n)

end UniqueGamesTheorem.Appendix.Globality

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality
open UniqueGamesTheorem.Appendix.Globality

namespace UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] Classical.propDecidable

section ActualLinearMaps

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] in
theorem global_nonneg (d : ℕ) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : 0 ≤ η := by
  have hord : order (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) ≤ d := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    simp only [finrank_top] at hq
    have hz : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by omega
    simp [order, hz]
  exact (energy_nonnegative _).trans (hf ⊥ ⊤ hord 0)

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem hybridDerivative_rankLevel_energy_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F)
    (hord : order A B ≤ d) :
    (𝔼 N, Derivatives.hybridDerivative A B T (rankLevel d f) N ^ 2) ≤
      (2 : ℝ) ^ (10 * d * d) * η := by
  have hglobal : RestrictionGlobal d η f := by
    intro A' B' horder T'
    exact hf A' B' T' horder
  have he : 2 * d * (d + 1) ≤ 10 * d * d := by
    nlinarith [Nat.le_mul_self d]
  exact (hybridDerivative_rankLevel_energy_le_strong d η f hf A B T hord).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he)
      (global_nonneg d η f hglobal))

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

namespace UniqueGamesTheorem.Appendix.SelectorEnergy

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem hybridSelectorEnergy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y, d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    Derivatives.hybridSelectorEnergy d f ≤
      (2 : ℝ) ^ (3 * d * d) * (𝔼 X, f X ^ 2) := by
  classical
  unfold Derivatives.hybridSelectorEnergy Derivatives.hybridProjector
  apply Derivatives.selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hdegree Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : Derivatives.selectorMultiplicity
      (fun s : Derivatives.HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [Derivatives.selectorMultiplicity, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

theorem hybridMomentSum_rankLevel_le_oai (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : LevelInequality.IsRestrictionGlobal f d η) :
    Derivatives.hybridMomentSum d (LevelInequality.rankLevel d f) ≤
      (2 : ℝ) ^ (13 * d * d) * η * (𝔼 X, f X ^ 2) := by
  have hglobal : Globality.RestrictionGlobal d η f := by
    intro A B hord T
    exact hf A B T hord
  have hη : 0 ≤ η := RankLevelFilter.global_nonneg d η f hglobal
  have hu := Derivatives.hybridMomentSum_le_of_uniform_energy d
    (LevelInequality.rankLevel d f) ((2 : ℝ) ^ (10 * d * d) * η)
    (fun A B T h => RankLevelFilter.hybridDerivative_rankLevel_energy_le d η f hf A B T h)
  have hs := hybridSelectorEnergy_le d (LevelInequality.rankLevel d f)
    (fun Y hY => LevelInequality.rankLevel_degree_le d f Y hY)
  have hc := LevelInequality.rankLevel_energy_le d f
  have hζ : 0 ≤ (2 : ℝ) ^ (10 * d * d) * η := mul_nonneg (by positivity) hη
  have hp : (2 : ℝ) ^ (10 * d * d) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (13 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * Derivatives.hybridSelectorEnergy d
        (LevelInequality.rankLevel d f) := hu
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * ((2 : ℝ) ^ (3 * d * d) *
        (𝔼 X, LevelInequality.rankLevel d f X ^ 2)) :=
      mul_le_mul_of_nonneg_left hs hζ
    _ ≤ ((2 : ℝ) ^ (10 * d * d) * η) * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, f X ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (by positivity)) hζ
    _ = ((2 : ℝ) ^ (10 * d * d) * (2 : ℝ) ^ (3 * d * d)) * η * (𝔼 X, f X ^ 2) := by
      ring
    _ = _ := by rw [hp]

end UniqueGamesTheorem.Appendix.SelectorEnergy

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le_oai.{u_1, u_2}
