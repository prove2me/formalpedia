-- Prove2me | solution 1 for OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:42.694222+00:00
-- url     : https://prove2.me/submissions/fef6a50e-db1f-44f0-9e7b-ac1ca94f6e37

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
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5Induction_derivative_inequality
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_SelectorEnergy_hybridMomentSum_rankLevel_le

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

section

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParity

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- Generic trace pairing of a rank-one color shift. -/
theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixParity

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
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

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem boolean_nonneg {f : α → ℝ} (hf : IsBoolean f) (x : α) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype α] in
theorem boolean_sq {f : α → ℝ} (hf : IsBoolean f) (x : α) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

theorem boolean_holder_fourth {f : α → ℝ} (hf : IsBoolean f) (h : α → ℝ) :
    (𝔼 x, h x * f x) ^ 4 ≤ (𝔼 x, h x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have hfirst := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x * f x) f
  have eleft : (𝔼 x, (h x * f x) * f x) = 𝔼 x, h x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = h x * (f x ^ 2) := by ring
      _ = _ := by rw [boolean_sq hf]
  have eright : (𝔼 x, (h x * f x) ^ 2) = 𝔼 x, h x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [eleft, eright, boolean_squared_norm_eq_density hf] at hfirst
  have hsecond := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x ^ 2) f
  have epow : (𝔼 x, (h x ^ 2) ^ 2) = 𝔼 x, h x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [epow, boolean_squared_norm_eq_density hf] at hsecond
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hweighted : 0 ≤ 𝔼 x, h x ^ 2 * f x :=
    Finset.expect_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x))
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, h x * f x)) hfirst
  have hscaled := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The fourth-root conversion used in the final displayed inequality.
This is an elementary real estimate, independent of Fourier analysis. -/
theorem fourth_power_le_implies_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hpow : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hba hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) hpow

/-- Once the genuine fourth-moment estimate has been established, this
proves the final Boolean Hölder implication. The fourth-moment estimate is
an explicit hypothesis here; this lemma itself is not Theorem 2.3. -/
theorem boolean_level_bound_of_fourth_moment {f h : α → ℝ}
    (hf : IsBoolean f) (d : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hprojection : (𝔼 x, h x ^ 2) = 𝔼 x, h x * f x)
    (hfourth : (𝔼 x, h x ^ 4) ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x)) :
    (𝔼 x, h x ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 x, f x ^ 2) := by
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hh : 0 ≤ 𝔼 x, h x ^ 2 := Finset.expect_nonneg (fun x _ => sq_nonneg _)
  have hηroot : 0 ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hη _
  have hroot : (η ^ ((1 : ℝ) / 4)) ^ 4 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
    norm_num
  have hslack : 113 * d * d ≤ (30 * d * d) * 4 := by
    calc
      113 * d * d = 113 * (d * d) := by ring
      _ ≤ 120 * (d * d) := Nat.mul_le_mul_right _ (by decide)
      _ = (30 * d * d) * 4 := by ring
  have htwo : (2 : ℝ) ^ (113 * d * d) ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hslack
  have hholder := boolean_holder_fourth hf h
  rw [← hprojection] at hholder
  have hscale := mul_le_mul_of_nonneg_right hfourth (pow_nonneg hμ 3)
  have hlarge := mul_le_mul_of_nonneg_right htwo (mul_nonneg hη (pow_nonneg hμ 4))
  rw [boolean_squared_norm_eq_density hf]
  apply fourth_power_le_implies_le hh
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hηroot) hμ)
  calc
    _ ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hholder, hscale]
    _ ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hlarge]
    _ = _ := by rw [mul_pow, mul_pow, hroot]

end UniqueGamesTheorem.Appendix.LevelInequality

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

/-- Orthogonal-projection identity used in the final Hölder step. -/
theorem rankLevel_inner_self (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) = 𝔼 X, rankLevel d f X * f X := by
  classical
  rw [← linear_parseval, ← linear_parseval_inner]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankLevel]
  split_ifs <;> ring

theorem rankLevel_degree_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : d < frequencyRank S) :
    linearCoeff (rankLevel d f) S = 0 := by
  rw [linearCoeff_rankLevel, ite_eq_right (Nat.ne_of_gt hS)]

theorem rankLevel_bound_of_fourth_moment (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (η : ℝ) (hη : 0 ≤ η)
    (hfourth : (𝔼 X, rankLevel d f X ^ 4) ≤
      (2 : ℝ) ^ (113 * d * d) * η * (𝔼 X, f X)) :
    (𝔼 X, rankLevel d f X ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2) :=
  boolean_level_bound_of_fourth_moment hf d η hη (rankLevel_inner_self d f) hfourth

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (UniqueGamesTheorem.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- On Boolean functions the restriction-global norm bound is exactly the
restriction-density hypothesis in Theorem 2.3. -/
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem evaluationCharacter_eq_zero_iff (w : E) :
    evaluationCharacter w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F2 w).mp
    intro ℓ
    apply binarySign_injective
    have hx := congrArg (fun ψ : AddChar (E →ₗ[F2] F2) ℂ => ψ ℓ) h
    simpa using hx
  · rintro rfl
    ext ℓ
    simp

theorem average_evaluationCharacter [Fintype (E →ₗ[F2] F2)] (w : E) :
    (𝔼 ℓ : E →ₗ[F2] F2, binarySign (ℓ w)) =
      if w = 0 then (1 : ℂ) else 0 := by
  classical
  change (𝔼 ℓ, evaluationCharacter w ℓ) = _
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite]
  simp only [evaluationCharacter_eq_zero_iff]
  split_ifs <;> simp

/-- Basis-independent uniform-functional cancellation in Lemma 5.1. -/
theorem average_smulRight_character [FiniteDimensional F2 F]
    [Fintype (E →ₗ[F2] F2)] (S : F →ₗ[F2] E) (v : F) :
    (𝔼 ℓ : E →ₗ[F2] F2, linearTraceCharacter S (ℓ.smulRight v)) =
      if S v = 0 then (1 : ℂ) else 0 := by
  simp only [linearTraceCharacter_apply, linearTracePair,
    MatrixParity.trace_smulRight_comp]
  exact average_evaluationCharacter _

/-- Equation (5.3), without a choice of bases. -/
theorem linearNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearNoiseOperator weight (linearTraceCharacter S) X =
      (linearNoiseEigenvalue weight S : ℂ) * linearTraceCharacter S X := by
  classical
  unfold linearNoiseOperator linearNoiseEigenvalue
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_expect, average_smulRight_character]
  change _ = Complex.ofRealHom (∑ v, weight v * if S v = 0 then 1 else 0) * _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp [mul_comm]

theorem linearRealNoiseOperator_complex [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    (linearRealNoiseOperator weight f X : ℂ) =
      linearNoiseOperator weight (fun Y => (f Y : ℂ)) X := by
  unfold linearRealNoiseOperator linearNoiseOperator
  change Complex.ofRealHom (∑ v, weight v * _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, complex_ofReal_expect]

theorem linearRealNoiseOperator_sum [Fintype F] [Fintype (E →ₗ[F2] F2)]
    {I : Type*} [Fintype I] (weight : F → ℝ)
    (f : I → (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => ∑ i, f i Y) X =
      ∑ i, linearRealNoiseOperator weight (f i) X := by
  unfold linearRealNoiseOperator
  simp_rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_comm

theorem linearRealNoiseOperator_smul [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => c * f Y) X =
      c * linearRealNoiseOperator weight f X := by
  unfold linearRealNoiseOperator
  simp_rw [← Finset.mul_expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

theorem linearRealNoiseOperator_character [FiniteDimensional F2 F]
    [Fintype F] [Fintype (E →ₗ[F2] F2)] (weight : F → ℝ)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight (fun Y => (linearTraceCharacter S Y).re) X =
      linearNoiseEigenvalue weight S * (linearTraceCharacter S X).re := by
  apply Complex.ofReal_injective
  rw [linearRealNoiseOperator_complex]
  simpa only [Complex.ofReal_mul, linearTraceCharacter_real] using
    (linearNoiseOperator_character weight S X)

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier expansion of the actual noise operator on every real function. -/
theorem linearRealNoiseOperator_expansion (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator weight f X =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S *
        (linearTraceCharacter S X).re := by
  classical
  calc
    linearRealNoiseOperator weight f X = linearRealNoiseOperator weight
        (fun Y => ∑ S : F →ₗ[F2] E,
          linearCoeff f S * (linearTraceCharacter S Y).re) X := by
      congr 1
      funext Y
      exact (linear_fourier_inversion f Y).symm
    _ = ∑ S : F →ₗ[F2] E,
        linearCoeff f S * linearRealNoiseOperator weight
          (fun Y => (linearTraceCharacter S Y).re) X := by
      rw [linearRealNoiseOperator_sum]
      simp_rw [linearRealNoiseOperator_smul]
    _ = _ := by
      simp_rw [linearRealNoiseOperator_character]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl

/-- Exact spectral pairing identity for the actual operator. -/
theorem linearRealNoiseOperator_pairing (weight : F → ℝ)
    (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight g X) =
      ∑ S : F →ₗ[F2] E,
        linearNoiseEigenvalue weight S * linearCoeff f S * linearCoeff g S := by
  simp_rw [linearRealNoiseOperator_expansion, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (𝔼 X, f X * (linearNoiseEigenvalue weight S * linearCoeff g S *
        (linearTraceCharacter S X).re)) =
        linearNoiseEigenvalue weight S * linearCoeff g S *
          (𝔼 X, f X * (linearTraceCharacter S X).re) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro X _
      ac_rfl
    _ = _ := mul_right_comm _ _ _

/-- The actual operator's quadratic form is precisely its weighted Fourier mass. -/
theorem linearRealNoiseOperator_energy (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * linearRealNoiseOperator weight f X) =
      ∑ S : F →ₗ[F2] E, linearNoiseEigenvalue weight S * linearCoeff f S ^ 2 := by
  rw [linearRealNoiseOperator_pairing]
  simp only [pow_two, mul_assoc]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.DerivativeDegree

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem degree_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DegreeAtMost d (LevelInequality.rankLevel d f) :=
  LevelInequality.rankLevel_degree_le d f

end UniqueGamesTheorem.Appendix.DerivativeDegree

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Gadgets_AdaptivePathsLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace UniqueGamesTheorem.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

/-- A finite-dimensional binary vector space has `2^dimension` vectors. -/
theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

/-- Exact cross-multiplied uniform kernel probability: `|ker f| * 2^rank f = |V|`. -/
theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

/-- The kernel formula expressed directly as the cardinality of the zero event. -/
theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

/-- The same exact probability identity for a direct count over a finite universe. -/
theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end UniqueGamesTheorem.Gadget.LinearKernelCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem node_le_one (n : ℕ) : node n ≤ 1 := by
  simpa [node] using node_add_le 0 n

section ActualLinearMaps

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem linearNoiseEigenvalue_uniform [Fintype F] (S : F →ₗ[F2] E) :
    UniqueGamesTheorem.Fourier.MatrixNoise.linearNoiseEigenvalue
      (fun _ : F => (Fintype.card F : ℝ)⁻¹) S =
        ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun v : F => S v = 0).card
  have hs : (∑ v : F, if S v = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 S.range =
      (Fintype.card F : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (UniqueGamesTheorem.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank S)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hn : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 S.range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold UniqueGamesTheorem.Fourier.MatrixNoise.linearNoiseEigenvalue
  rw [← Finset.mul_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card F : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 S.range =
        (Fintype.card F : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 S.range) :=
      mul_assoc _ _ _
    _ = (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 S.range := (inv_mul_cancel₀ hp).symm

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.LevelTheorem
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.LevelInequality

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

section FiniteDimensional
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem rankLevel_fourth_moment_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η) :
    (𝔼 M, rankLevel d f M^4) ≤
      (2:ℝ)^(113*d*d) * η * (𝔼 M, f M^2) := by
  have ha := A5Induction.derivative_inequality d (rankLevel d f)
    (DerivativeDegree.degree_rankLevel d f)
  have hs := SelectorEnergy.hybridMomentSum_rankLevel_le d η f hf
  have hp : (2:ℝ)^(100*d^2) * (2:ℝ)^(13*d*d) = (2:ℝ)^(113*d*d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    _ ≤ (2:ℝ)^(100*d^2) * Derivatives.hybridMomentSum d (rankLevel d f) := ha
    _ ≤ (2:ℝ)^(100*d^2) * ((2:ℝ)^(13*d*d) * η * (𝔼 M, f M^2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((2:ℝ)^(100*d^2) * (2:ℝ)^(13*d*d)) * η * (𝔼 M, f M^2) := by ring
    _ = _ := by rw [hp]

end FiniteDimensional

theorem theorem23 : LevelInequality.Theorem23 (E := E) (F := F) := by
  let : FiniteDimensional F2 E := Module.Finite.of_finite
  let : FiniteDimensional F2 F := Module.Finite.of_finite
  intro d _ ρ hρ _ f hf hrestricted
  have hglobal : IsRestrictionGlobal f d ρ :=
    (boolean_global_iff_density f hf d ρ).mpr hrestricted
  have hfourth := rankLevel_fourth_moment_le d ρ f hglobal
  rw [boolean_squared_norm_eq_density hf] at hfourth
  exact rankLevel_bound_of_fourth_moment d f hf ρ hρ.le hfourth

end UniqueGamesTheorem.Appendix.LevelTheorem

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixLevelBridge

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality

theorem sum_rank_le {ι : Type*} [Fintype ι] (rk : ι → Nat) (w : ι → ℝ) (r : Nat) :
    (∑ i, if rk i ≤ r then w i else 0) =
      ∑ d ∈ Finset.range (r + 1), ∑ i, if rk i = d then w i else 0 := by
  calc
    _ = ∑ i, ∑ d ∈ Finset.range (r + 1), if rk i = d then w i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Finset.mem_range]
    _ = _ := Finset.sum_comm

section Unrestricted

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem order_bot_top : order (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) = 0 := by
  simpa [order] using
    (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem expect_unrestricted [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter (⊥ : Submodule F2 E) (⊤ : Submodule F2 F),
      restrict f ⊥ ⊤ 0 A) = 𝔼 X : E →ₗ[F2] F, f X := by
  apply Finset.expect_equiv (unrestrictedEquiv (E := E) (F := F))
  · intro A
    simp
  · intro A _
    change f (0 + embed ⊥ ⊤ A) = f (embed ⊥ ⊤ A)
    rw [zero_add]

end Unrestricted

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankCutoffEnergy_eq_sum_exactRankMass (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    rankCutoffEnergy r f =
      ∑ d ∈ Finset.range (r + 1), ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  simpa only [rankCutoffEnergy, Finset.sum_filter] using
    sum_rank_le frequencyRank (fun S => linearCoeff f S ^ 2) r

theorem rankCutoffEnergy_eq_sum_rankLevel (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    rankCutoffEnergy r f =
      ∑ d ∈ Finset.range (r + 1), (𝔼 X, rankLevel d f X ^ 2) := by
  simp only [rankLevel_energy, rankCutoffEnergy_eq_sum_exactRankMass]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem frequencyRank_eq_zero_iff (S : F →ₗ[F2] E) : frequencyRank S = 0 ↔ S = 0 := by
  rw [frequencyRank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_zero_frequency (f : (E →ₗ[F2] F) → ℝ) :
    linearCoeff f (0 : F →ₗ[F2] E) = 𝔼 X, f X := by
  simp [linearCoeff, linearTraceCharacter_zero]

theorem rankZero_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel 0 f X ^ 2) = (𝔼 X, f X) ^ 2 := by
  rw [rankLevel_energy]
  simp [Finset.sum_filter, frequencyRank_eq_zero_iff, linearCoeff_zero_frequency]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in

theorem fullSecondMoment_le_of_global (f : (E →ₗ[F2] F) → ℝ) (r : Nat) (ρ : ℝ)
    (hg : IsRestrictionGlobal f r ρ) : (𝔼 X, f X ^ 2) ≤ ρ := by
  rw [← expect_unrestricted (fun X => f X ^ 2)]
  exact hg ⊥ ⊤ 0 (by rw [order_bot_top]; exact Nat.zero_le r)

theorem rankCutoffEnergy_le_of_theorem23 (h23 : Theorem23 (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hf : IsBoolean f) (hg : IsRestrictionGlobal f r ρ) :
    rankCutoffEnergy r f ≤ levelCutoffConstant r ρ * (𝔼 X, f X ^ 2) := by
  let μ := 𝔼 X, f X ^ 2
  have hμ : 0 ≤ μ := Finset.expect_nonneg (fun X _ => sq_nonneg (f X))
  have hμρ : μ ≤ ρ := fullSecondMoment_le_of_global f r ρ hg
  have hzero : (𝔼 X, rankLevel 0 f X ^ 2) ≤ ρ * μ := by
    rw [rankZero_energy, ← boolean_squared_norm_eq_density hf, pow_two]
    exact mul_le_mul_of_nonneg_right hμρ hμ
  rw [rankCutoffEnergy_eq_sum_rankLevel]
  calc
    _ ≤ ∑ d ∈ Finset.range (r + 1),
        (if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)) * μ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        simpa using hzero
      · have hdr : d ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
        have hgd : IsRestrictionGlobal f d ρ := by
          intro A B T horder
          exact hg A B T (horder.trans hdr)
        have hdensity := (boolean_global_iff_density f hf d ρ).mp hgd
        have hpositive := h23 d (Nat.pos_of_ne_zero hd0) ρ hρ hρ1 f hf hdensity
        simpa only [ite_eq_right hd0] using hpositive
    _ = levelCutoffConstant r ρ * μ := by
      simp only [levelCutoffConstant, Finset.sum_mul]

end ActualLinearMaps

end UniqueGamesTheorem.Fourier.MatrixLevelBridge

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Finite E] in
theorem noiseEnergy_eq (f : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy f = ∑ S : F →ₗ[F2] E, node (frequencyRank S) * linearCoeff f S ^ 2 := by
  unfold noiseEnergy
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearNoiseEigenvalue_uniform, node_eq_inv_pow]
  rfl

omit [Finite E] in
theorem noiseEnergy_le_cutoff (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy f ≤ rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) := by
  rw [noiseEnergy_eq]
  calc
    _ ≤ ∑ S : F →ₗ[F2] E,
        ((if frequencyRank S ≤ r then linearCoeff f S ^ 2 else 0) +
          node (r + 1) * linearCoeff f S ^ 2) := by
      apply Finset.sum_le_sum
      intro S _
      by_cases h : frequencyRank S ≤ r
      · rw [ite_eq_left h]
        have h₁ := mul_le_mul_of_nonneg_right (node_le_one (frequencyRank S))
          (sq_nonneg (linearCoeff f S))
        have h₂ := mul_nonneg (node_pos (r + 1)).le (sq_nonneg (linearCoeff f S))
        linarith
      · rw [ite_eq_right h, zero_add]
        exact mul_le_mul_of_nonneg_right
          (node_antitone (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))) (sq_nonneg _)
    _ = rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, linear_parseval]
      simp only [rankCutoffEnergy, Finset.sum_filter]

theorem noiseEnergy_le_of_global_oai (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (hg : IsRestrictionGlobal f r ρ) :
    noiseEnergy f ≤ (levelCutoffConstant r ρ + node (r + 1)) * (𝔼 X, f X ^ 2) := by
  have hcut := rankCutoffEnergy_le_of_theorem23
    (UniqueGamesTheorem.Appendix.LevelTheorem.theorem23 (E := E) (F := F)) f r ρ hρ hρ1 hf hg
  calc
    noiseEnergy f ≤ rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) :=
      noiseEnergy_le_cutoff r f
    _ ≤ levelCutoffConstant r ρ * (𝔼 X, f X ^ 2) +
        node (r + 1) * (𝔼 X, f X ^ 2) := add_le_add hcut (le_refl _)
    _ = _ := (add_mul _ _ _).symm

end
end PerfectCompleteness.MatrixInverse

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global_oai.{u_1, u_2} := @OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global_oai.{u_1, u_2}
