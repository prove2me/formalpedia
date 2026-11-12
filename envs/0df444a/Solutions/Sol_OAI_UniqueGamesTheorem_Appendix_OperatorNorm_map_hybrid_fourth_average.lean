-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.OperatorNorm.map_hybrid_fourth_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:17:01.297596+00:00
-- url     : https://prove2.me/submissions/50841510-5a90-4597-b7e2-68eebb7acaa3

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P004
import Definitions.Def_OAIQ252P006

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.evaluationCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

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
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

section ActualRestrictions

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair UniqueGamesTheorem.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end ActualRestrictions

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

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

theorem spectralProjector_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P (spectralProjector Q f) =
      spectralProjector (fun Y => P Y ∧ Q Y) f := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [linearCoeff_spectralProjector]
  by_cases hP : P Y <;> by_cases hQ : Q Y <;> simp [hP, hQ]

variable [Finite E] [Finite F]

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
        (spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f) A B T := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_spectralProjector,
    Restriction.linear_coefficient_merging, Restriction.linear_coefficient_merging]
  by_cases hQ : Q Z
  · simp only [ite_eq_left hQ]
    apply Finset.sum_congr rfl
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]
  · simp only [ite_eq_right hQ]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]

theorem spectralProjector_restriction_moment_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    {N : Type*} [Fintype N] [Nonempty N]
    (θ : N → UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) (p : ℕ) :
    (𝔼 T, 𝔼 n, spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) (θ n) ^ p) =
      𝔼 M, spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p := by
  simp_rw [spectralProjector_restriction]
  exact Restriction.real_translation_average
    (fun n => UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B (θ n))
    (fun M => spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p)

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

namespace UniqueGamesTheorem.Appendix.OperatorNorm

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem compressFrequency_eq_compress (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : Restriction.compressFrequency A B Y = compress Y A B := by
  ext x
  rfl

theorem map_hybrid_fourth_average_oai
    (A0 : Submodule F2 E) (B0 : Submodule F2 F)
    (X : B0 →ₗ[F2] (E ⧸ A0)) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A0 B0 T f) N ^ 4) =
    𝔼 M, spectralProjector
      (fun Y => Hybrid Y A0 B0 ∧ RankBelow X (compress Y A0 B0)) f M ^ 4 := by
  classical
  have hp :
      spectralProjector (fun Y => RankBelow X (Restriction.compressFrequency A0 B0 Y))
        (hybridProjector A0 B0 f) =
      spectralProjector (fun Y => Hybrid Y A0 B0 ∧
        RankBelow X (Restriction.compressFrequency A0 B0 Y)) f := by
    rw [hybridProjector, spectralProjector_comp]
    congr 1
    funext Y
    exact propext and_comm
  have h := Derivatives.spectralProjector_restriction_moment_average A0 B0
    (fun Z => RankBelow X Z) (hybridProjector A0 B0 f)
    (MatrixRestrictions.embed X.range X.ker) 4
  rw [hp] at h
  simpa only [mapDerivative, rankProjector, hybridDerivative,
    MatrixRestrictions.restrict, MatrixRestrictions.translate, zero_add,
    compressFrequency_eq_compress] using h

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.map_hybrid_fourth_average_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.map_hybrid_fourth_average_oai.{u_1, u_2}
