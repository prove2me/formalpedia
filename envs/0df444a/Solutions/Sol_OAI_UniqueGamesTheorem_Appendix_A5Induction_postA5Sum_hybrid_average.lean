-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.A5Induction.postA5Sum_hybrid_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:55.22235+00:00
-- url     : https://prove2.me/submissions/4d87bd19-b110-40a2-a1df-cdb893f7342c

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
import Definitions.Def_OAIQ252P011

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

/-- The exact nested-selector equivalence of (A.3), now using Mathlib's
linear maps, submodules, restriction, and quotient construction. -/
theorem nested_hybrid_iff (Y : W →ₗ[K] V) (A₀ A : Submodule K V)
    (B B₀ : Submodule K W) (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    (Hybrid Y A₀ B₀ ∧
      Hybrid (compress Y A₀ B₀) (A.map A₀.mkQ) (B.comap B₀.subtype)) ↔
    Hybrid Y A B := by
  constructor
  · rintro ⟨inner, outer⟩
    constructor
    · intro a ha
      have hqa : A₀.mkQ a ∈ A.map A₀.mkQ := ⟨a, ha, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y b - a ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb
      rcases inner.1 hdiff with ⟨c, hc⟩
      refine ⟨(b : W) - c, ?_⟩
      rw [map_sub, hc]
      abel
    · intro w hw
      have hqa : A₀.mkQ (Y w) ∈ A.map A₀.mkQ := ⟨Y w, hw, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y w - Y b ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb.symm
      have hwb : w - b ∈ B₀ := inner.2 (by
        change Y (w - b) ∈ A₀
        simpa only [map_sub] using hdiff)
      have hw₀ : w ∈ B₀ := by
        have h := B₀.add_mem hwb b.property
        simpa only [sub_add_cancel] using h
      have hout : (⟨w, hw₀⟩ : B₀) ∈ (A.map A₀.mkQ).comap (compress Y A₀ B₀) := hqa
      exact outer.2 hout
  · intro full
    constructor
    · exact ⟨hA.trans full.1, (Submodule.comap_mono hA).trans (full.2.trans hB)⟩
    · constructor
      · intro q hq
        rcases hq with ⟨a, ha, rfl⟩
        rcases full.1 ha with ⟨w, hw⟩
        have hwB : w ∈ B := full.2 (by
          change Y w ∈ A
          rw [hw]
          exact ha)
        refine ⟨⟨w, hB hwB⟩, ?_⟩
        simp only [compress_apply, hw]
      · intro b hb
        have hYb : Y b ∈ A := (quotient_mem_image_iff A₀ A hA (Y b)).mp hb
        exact full.2 hYb

/-! ## The unique selector in (A.4) -/

end UniqueGamesTheorem.Appendix.LinearIdentities

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_OperatorPartitions
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix.Derivatives

namespace UniqueGamesTheorem.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace Appendix.RestrictionTransport

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

end SameRange

end Appendix.RestrictionTransport

end

end UniqueGamesTheorem

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.HybridComposition

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.LinearIdentities
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
variable [Finite E] [Finite F]

local instance quotientFinite_ra08892_1 (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
local instance compressedDualFintype_ra08892_1 (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem effective_hybrid_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (Y : F →ₗ[F2] E) :
    (Hybrid Y A B ∧ Hybrid (Restriction.compressFrequency A B Y) C D) ↔
      Hybrid Y (C.comap A.mkQ) (D.map B.subtype) := by
  have hA : A ≤ C.comap A.mkQ := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map B.subtype ≤ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hC : (C.comap A.mkQ).map A.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := A.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hD : (D.map B.subtype).comap B.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hh := LinearIdentities.nested_hybrid_iff Y A (C.comap A.mkQ)
    (D.map B.subtype) B hA hB
  rw [hC, hD] at hh
  have hc : Restriction.compressFrequency A B Y = LinearIdentities.compress Y A B := by
    ext x
    rfl
  simpa only [hc] using hh

end UniqueGamesTheorem.Appendix.HybridComposition

end

end

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
theorem nested_projector_restriction_apply
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (P : (F →ₗ[F2] E) → Prop) (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F)
    (S : MatrixRestrictions.Parameter A B) (N : MatrixRestrictions.Parameter C D) :
    MatrixRestrictions.restrict
      (spectralProjector Q (MatrixRestrictions.restrict (spectralProjector P f) A B T))
      C D S N =
    spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
      (T + MatrixRestrictions.embed A B S + RestrictionTransport.nestedEmbedding A B C D N) := by
  classical
  rw [OperatorPartitions.spectralProjector_restriction_projector]
  let g := spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
  change g (T + (MatrixRestrictions.embedding A B)
      (S + MatrixRestrictions.embed C D N)) =
    g ((T + (MatrixRestrictions.embedding A B) S) +
      (MatrixRestrictions.embedding A B) (MatrixRestrictions.embed C D N))
  rw [map_add, add_assoc]

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

section

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.NaturalTransport
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionQuotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionCompressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rank_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F') (L : E →ₗ[F2] F) :
    Module.finrank F2 (LinearEquiv.arrowCongr a b L).range =
      Module.finrank F2 L.range := by
  have hh : LinearEquiv.arrowCongr a b L =
      (b.toLinearMap.comp L).comp a.symm.toLinearMap := by
    ext x
    rfl
  rw [hh, LinearEquiv.range_comp, LinearMap.range_comp]
  exact b.finrank_map_eq L.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rankBelow_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (X Y : F →ₗ[F2] E) :
    RankBelow (LinearEquiv.arrowCongr b a X) (LinearEquiv.arrowCongr b a Y) ↔
      RankBelow X Y := by
  unfold RankBelow
  rw [← map_sub, rank_arrowCongr, rank_arrowCongr, rank_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem trace_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTracePair (LinearEquiv.arrowCongr a b M) (LinearEquiv.arrowCongr b a Z) =
      linearTracePair M Z := by
  unfold linearTracePair
  rw [← LinearEquiv.arrowCongr_comp]
  exact LinearMap.trace_conj' (M.comp Z) b

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem character_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTraceCharacter (LinearEquiv.arrowCongr b a Z) (LinearEquiv.arrowCongr a b M) =
      linearTraceCharacter Z M := by
  simp only [linearTraceCharacter_apply, trace_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem admissible_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) (M : E →ₗ[F2] F) :
    ((LinearEquiv.arrowCongr b a Z).range ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ (LinearEquiv.arrowCongr b a Z).ker) ↔
    (Z.range ≤ M.ker ∧ M.range ≤ Z.ker) := by
  simp [LinearMap.range_le_ker_iff, ← LinearEquiv.arrowCongr_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem derivative_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker)).range =
      (embedding (LinearEquiv.arrowCongr b a Z).range
        (LinearEquiv.arrowCongr b a Z).ker).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  let Z' := LinearEquiv.arrowCongr b a Z
  ext M'
  change (∃ N, e (embed Z.range Z.ker N) = M') ↔
    (∃ N, embed Z'.range Z'.ker N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff Z'.range Z'.ker _).mpr
    apply (admissible_arrowCongr a b Z (embed Z.range Z.ker N)).mpr
    exact (exists_embed_iff Z.range Z.ker _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff Z'.range Z'.ker M').mp hM'
    have hm : Z.range ≤ M.ker ∧ M.range ≤ Z.ker := by
      apply (admissible_arrowCongr a b Z M).mp
      change Z'.range ≤ (e M).ker ∧ (e M).range ≤ Z'.ker
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff Z.range Z.ker M).mpr hm
    refine ⟨N, ?_⟩
    rw [hN]
    exact he

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem linearCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    linearCoeff (fun M => f (LinearEquiv.arrowCongr a b M)) Z =
      linearCoeff f (LinearEquiv.arrowCongr b a Z) := by
  unfold linearCoeff
  exact Fintype.expect_equiv (LinearEquiv.arrowCongr a b).toEquiv _ _
    (fun M => by
      change f (LinearEquiv.arrowCongr a b M) * (linearTraceCharacter Z M).re =
        f (LinearEquiv.arrowCongr a b M) *
          (linearTraceCharacter (LinearEquiv.arrowCongr b a Z)
            (LinearEquiv.arrowCongr a b M)).re
      rw [character_arrowCongr])

theorem rankProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    rankProjector Z (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankProjector, linearCoeff_spectralProjector,
    linearCoeff_pullback, rankBelow_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

theorem mapDerivative_energy_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    (𝔼 N, mapDerivative Z (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, mapDerivative (LinearEquiv.arrowCongr b a Z) f N ^ 2 := by
  simp only [mapDerivative, restrict,
    UniqueGamesTheorem.Fourier.MatrixRestrictions.translate, zero_add]
  rw [rankProjector_pullback]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker))
    (embedding (LinearEquiv.arrowCongr b a Z).range (LinearEquiv.arrowCongr b a Z).ker)
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective Z.range Z.ker))
    (embed_injective _ _) (derivative_embedding_range a b Z)
    (fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f M ^ 2)

end General

section Nested
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionQuotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionCompressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem parameterFactor_embedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (N : Parameter C D) :
    embed (C.comap A.mkQ) (D.map B.subtype) (parameterFactor A B C D N) =
      RestrictionTransport.nestedEmbedding A B C D N := by
  ext x
  change ((outputFactor B D (N (quotientFactor A C ((C.comap A.mkQ).mkQ x)))) : F) =
    ((N (C.mkQ (A.mkQ x)) : B) : F)
  rw [quotientFactor_mkQ]
  rfl

theorem nested_hybridDerivative_function
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B) :
    hybridDerivative C D S (hybridDerivative A B T f) =
      fun N => hybridDerivative (C.comap A.mkQ) (D.map B.subtype)
        (T + embed A B S) f (parameterFactor A B C D N) := by
  funext N
  have hh := OperatorNorm.nested_projector_restriction_apply A B C D
    (fun Y => LinearIdentities.Hybrid Y A B)
    (fun Z => LinearIdentities.Hybrid Z C D) f T S N
  have hp : (fun Y => LinearIdentities.Hybrid Y A B ∧
        LinearIdentities.Hybrid (Restriction.compressFrequency A B Y) C D) =
      (fun Y => LinearIdentities.Hybrid Y (C.comap A.mkQ) (D.map B.subtype)) := by
    funext Y
    exact propext (HybridComposition.effective_hybrid_iff A B C D Y)
  rw [hp] at hh
  change _ = hybridProjector (C.comap A.mkQ) (D.map B.subtype) f
    ((T + embed A B S) + embed (C.comap A.mkQ) (D.map B.subtype)
      (parameterFactor A B C D N))
  rw [parameterFactor_embedding]
  exact hh

theorem nested_mapDerivative_energy
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    (𝔼 N, mapDerivative Z (hybridDerivative C D S (hybridDerivative A B T f)) N ^ 2) =
      𝔼 N, mapDerivative (dualFactor A B C D Z)
        (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) N ^ 2 := by
  rw [nested_hybridDerivative_function]
  exact mapDerivative_energy_pullback (quotientFactor A C).symm (outputFactor B D)
    (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) Z

end Nested
end UniqueGamesTheorem.Appendix.NaturalTransport

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A5FrequencyTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

namespace Appendix.A5Induction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Recombination uses the natural domain and codomain isomorphisms. The
intermediate shifts need only be the actual embedded derivative parameters. -/
theorem postA5Sum_hybrid_average_oai (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, postA5Sum X e (hybridDerivative A B T f)) =
      A5Passage.descendantSum A B X e f := by
  unfold postA5Sum A5Passage.descendantSum
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [NaturalTransport.nested_mapDerivative_energy
    A B q.2.val.1 q.2.val.2 f]
  exact Restriction.real_translation_average
    (fun S : Parameter X.range X.ker => embed A B (embed X.range X.ker S))
    (fun U => (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2)^2)

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.UniqueGamesTheorem.Appendix.A5Induction.postA5Sum_hybrid_average_oai.{u, v} := @OAI.UniqueGamesTheorem.Appendix.A5Induction.postA5Sum_hybrid_average_oai.{u, v}
