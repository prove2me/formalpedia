-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.hybridDerivative_rankLevel_energy_le_strong
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:57.577026+00:00
-- url     : https://prove2.me/submissions/7ecbac70-c94e-45c7-a959-f0aabb13035a

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

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

theorem finrank_comap_subtype_le (A B : Submodule K V) :
    finrank K (A.comap B.subtype) ≤ finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq B (A.comap B.subtype),
    Submodule.map_comap_subtype]
  exact Submodule.finrank_mono inf_le_right

theorem quotient_rank_bounds (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + finrank K A := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ] at h
  have hk := finrank_comap_subtype_le A (range Y)
  omega

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_bounds (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp] at h₁
  have hk := finrank_comap_subtype_le (ker Y) B
  have hr : finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) := by
    apply Submodule.finrank_mono
    exact LinearMap.range_comp_le_range _ _
  omega

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in
theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

/-- Equality in the dimension bound for a subspace intersection forces
the original subspace to lie in the restricting subspace. -/
theorem finrank_comap_subtype_eq_iff (A B : Submodule K V) :
    finrank K (A.comap B.subtype) = finrank K A ↔ A ≤ B := by
  constructor
  · intro h
    have hdim := Submodule.finrank_map_subtype_eq B (A.comap B.subtype)
    rw [Submodule.map_comap_subtype, h] at hdim
    have heq : B ⊓ A = A := Submodule.eq_of_le_of_finrank_eq inf_le_right hdim
    calc
      A = B ⊓ A := heq.symm
      _ ≤ B := inf_le_left
  · intro h
    exact (Submodule.comapSubtypeEquivOfLe h).finrank_eq

theorem quotient_rank_equality_iff (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) ↔
      A ≤ range Y := by
  constructor
  · intro heq
    have hn := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
    have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
      simp only [range_comp, Submodule.range_subtype]
    rw [hr, ker_comp, Submodule.ker_mkQ] at hn
    apply (finrank_comap_subtype_eq_iff A (range Y)).mp
    omega
  · exact quotient_rank_selected A Y

omit [FiniteDimensional K V] in
theorem domain_rank_equality_iff (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ ker Y ≤ B := by
  constructor
  · intro heq
    have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
    have h₂ := Y.finrank_range_add_finrank_ker
    have h₃ := B.finrank_quotient_add_finrank
    rw [ker_comp] at h₁
    apply (finrank_comap_subtype_eq_iff (ker Y) B).mp
    omega
  · exact domain_rank_selected B Y

/-- Every genuine restriction loses at most its order in Fourier rank. -/
theorem compression_rank_bounds (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) := by
  have hq := quotient_rank_bounds A Y
  have hd := domain_rank_bounds B (A.mkQ.comp Y)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hd
  omega

theorem hybrid_rank_loss_iff (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ A ≤ range Y ∧ A.comap Y ≤ B := by
  constructor
  · intro heq
    have hq := quotient_rank_bounds A Y
    have hd := domain_rank_bounds B (A.mkQ.comp Y)
    have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
    rw [hc] at hd
    constructor
    · apply (quotient_rank_equality_iff A Y).mp
      omega
    · have he : finrank K (range ((A.mkQ.comp Y).comp B.subtype)) +
          finrank K (W ⧸ B) = finrank K (range (A.mkQ.comp Y)) := by
        rw [hc]
        omega
      have hk := (domain_rank_equality_iff B (A.mkQ.comp Y)).mp he
      simpa only [ker_comp, Submodule.ker_mkQ] using hk
  · rintro ⟨hA, hB⟩
    exact hybrid_rank_loss A B Y hA hB

end UniqueGamesTheorem.Appendix.Level.LinearRank

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

/-- The actual noise operator multiplies each Fourier coefficient by its
annihilation probability. Uniform outer weights specialize to the kernel-rank
multiplier used in Appendix A. -/
theorem linearRealNoiseOperator_coeff (weight : F → ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (linearRealNoiseOperator weight f) S =
      linearNoiseEigenvalue weight S * linearCoeff f S := by
  classical
  change (𝔼 X, linearRealNoiseOperator weight f X *
    (linearTraceCharacter S X).re) = _
  calc
    (𝔼 X, linearRealNoiseOperator weight f X * (linearTraceCharacter S X).re) =
        𝔼 X, (linearTraceCharacter S X).re * linearRealNoiseOperator weight f X := by
      apply Finset.expect_congr rfl
      intro X _
      exact mul_comm _ _
    _ = ∑ T : F →ₗ[F2] E, linearNoiseEigenvalue weight T *
        linearCoeff (fun X => (linearTraceCharacter S X).re) T * linearCoeff f T :=
      linearRealNoiseOperator_pairing weight _ f
    _ = _ := by
      simp only [linearCoeff_character]
      simp [mul_ite, ite_mul]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

theorem sq_average_le_average_sq {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ) : (𝔼 i, f i) ^ 2 ≤ 𝔼 i, f i ^ 2 := by
  simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))

theorem energy_average_le {I N : Type*} [Fintype I] [Nonempty I] [Fintype N]
    (f : I → N → ℝ) : energy (fun n => 𝔼 i, f i n) ≤ 𝔼 i, energy (f i) := by
  calc
    energy (fun n => 𝔼 i, f i n) ≤ 𝔼 n, 𝔼 i, f i n ^ 2 :=
      Finset.expect_le_expect fun n _ => sq_average_le_average_sq (fun i => f i n)
    _ = 𝔼 i, energy (f i) := Finset.expect_comm _ _ _

theorem energy_average_le_of_bound {I N : Type*} [Fintype I] [Nonempty I]
    [Fintype N] (f : I → N → ℝ) (η : ℝ) (h : ∀ i, energy (f i) ≤ η) :
    energy (fun n => 𝔼 i, f i n) ≤ η :=
  (energy_average_le f).trans (Finset.expect_le Finset.univ_nonempty (fun i _ => h i))

theorem energy_weighted_sum_le {I N : Type*} [Fintype I] [Fintype N]
    (w : I → ℝ) (f : I → N → ℝ) (η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, energy (f i) ≤ η) :
    energy (fun n => ∑ i, w i * f i n) ≤ (∑ i, w i) ^ 2 * η := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  calc
    energy (fun n => ∑ i, w i * f i n) ≤
        𝔼 n, (∑ i, w i) * ∑ i, w i * f i n ^ 2 := by
      apply Finset.expect_le_expect
      intro n _
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · exact fun i _ => hw i
      · exact fun i _ => mul_nonneg (hw i) (sq_nonneg _)
      · intro i _
        exact le_of_eq (by ring)
    _ = (∑ i, w i) * ∑ i, w i * energy (f i) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
      simp_rw [← Finset.mul_expect]
      rfl
    _ ≤ (∑ i, w i) * ∑ i, w i * η := by
      apply mul_le_mul_of_nonneg_left _ hsum
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i))
    _ = (∑ i, w i) ^ 2 * η := by rw [← Finset.sum_mul]; ring

theorem restrictionEnergy_average_translate_le {I M N : Type*}
    [Fintype I] [Nonempty I] [AddCommGroup M] [Fintype N]
    (f : M → ℝ) (ι : N → M) (shifts : I → M) (η : ℝ)
    (h : ∀ T, restrictionEnergy f ι T ≤ η) (T : M) :
    restrictionEnergy (fun x => 𝔼 i, f (x + shifts i)) ι T ≤ η := by
  apply energy_average_le_of_bound (fun i n => f ((T + ι n) + shifts i)) η
  intro i
  simpa only [restrictionEnergy, add_right_comm T] using h (T + shifts i)

section BinaryLinear

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

theorem restrictionGlobal_averageTranslates {I : Type*} [Fintype I] [Nonempty I]
    (shifts : I → (E →ₗ[F2] F)) (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d η (averageTranslates shifts f) := by
  intro A B hord T
  exact restrictionEnergy_average_translate_le f (embed A B) shifts η (hf A B hord) T

theorem restrictionGlobal_neg (d : Nat) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : RestrictionGlobal d η (fun X => -f X) := by
  intro A B hord T
  simpa only [restrictionEnergy, energy, neg_sq] using hf A B hord T

theorem restrictionGlobal_weighted_sum {I : Type*} [Fintype I]
    (w : I → ℝ) (f : I → (E →ₗ[F2] F) → ℝ) (d : Nat) (η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, RestrictionGlobal d η (f i)) :
    RestrictionGlobal d ((∑ i, w i) ^ 2 * η) (fun X => ∑ i, w i * f i X) := by
  intro A B hord T
  exact energy_weighted_sum_le w (fun i n => f i (T + embed A B n)) η hw
    (fun i => hf i A B hord T)

end BinaryLinear

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

theorem node_le_one (n : ℕ) : node n ≤ 1 := by
  simpa [node] using node_add_le 0 n

theorem node_gap {j d : ℕ} (h : j < d) :
    0 < node j - node d ∧ node d ≤ node j - node d := by
  have hm := node_antitone (show j + 1 ≤ d by omega)
  change node d ≤ node j / 2 at hm
  constructor <;> linarith [node_pos d]

theorem step_coefficient_bound {j d : ℕ} (h : j < d) :
    node j / (node j - node d) + (node j - node d)⁻¹ ≤ (2 : ℝ) ^ (d + 1) := by
  have hg := node_gap h
  have he : node j / (node j - node d) + (node j - node d)⁻¹ =
      (node j + 1) / (node j - node d) := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  calc
    _ ≤ 2 / (node j - node d) :=
      div_le_div_of_nonneg_right (by linarith [node_le_one j]) hg.1.le
    _ ≤ 2 / node d := div_le_div_of_nonneg_left (by norm_num) (node_pos d) hg.2
    _ = (2 : ℝ) ^ (d + 1) := by
      rw [node_eq_inv_pow, div_inv_eq_mul, pow_succ]
      ring

theorem multiplier_succ (d k r : ℕ) :
    multiplier d (k + 1) r =
      multiplier d k r * ((node k - node r) / (node k - node d)) := by
  simp only [multiplier, Finset.prod_range_succ]

theorem multiplier_target (d k : ℕ) (hk : k ≤ d) : multiplier d k d = 1 := by
  unfold multiplier
  apply Finset.prod_eq_one
  intro j hj
  have hjd : j < d := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  exact div_self (ne_of_gt (node_gap hjd).1)

theorem multiplier_below (d k r : ℕ) (hr : r < k) : multiplier d k r = 0 := by
  unfold multiplier
  exact Finset.prod_eq_zero_iff.mpr ⟨r, Finset.mem_range.mpr hr, by simp⟩

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

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankNoise_eq_average (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    letI : Fintype F := Fintype.ofFinite F
    letI : Fintype (E →ₗ[F2] F2) := linearMapFintype
    rankNoise f X = 𝔼 v : F, 𝔼 φ : E →ₗ[F2] F2, f (X + φ.smulRight v) := by
  classical
  dsimp [rankNoise, UniqueGamesTheorem.Fourier.MatrixNoise.linearRealNoiseOperator]
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem global_average_family {I : Type*} [Fintype I] [Nonempty I]
    (f : I → (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ)
    (hf : ∀ i, RestrictionGlobal d η (f i)) :
    RestrictionGlobal d η (fun X => 𝔼 i, f i X) := by
  intro A B hord T
  exact energy_average_le_of_bound (fun i N => f i (T + embed A B N)) η
    (fun i => hf i A B hord T)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankNoise_global (d : ℕ) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : RestrictionGlobal d η (rankNoise f) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (E →ₗ[F2] F2) := linearMapFintype
  have he : rankNoise f =
      fun X => 𝔼 v : F, 𝔼 φ : E →ₗ[F2] F2, f (X + φ.smulRight v) := by
    funext X
    exact rankNoise_eq_average f X
  rw [he]
  apply global_average_family _ d η
  intro v
  exact restrictionGlobal_averageTranslates (fun φ : E →ₗ[F2] F2 => φ.smulRight v)
    d η f hf

omit [FiniteDimensional F2 E] in
theorem global_nonneg (d : ℕ) (η : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : RestrictionGlobal d η f) : 0 ≤ η := by
  have hord : order (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) ≤ d := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    simp only [finrank_top] at hq
    have hz : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by omega
    simp [order, hz]
  exact (energy_nonnegative _).trans (hf ⊥ ⊤ hord 0)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem global_mono_bound {d : ℕ} {η ζ : ℝ} {f : (E →ₗ[F2] F) → ℝ}
    (hη : η ≤ ζ) (hf : RestrictionGlobal d η f) : RestrictionGlobal d ζ f := by
  intro A B hord T
  exact (hf A B hord T).trans hη

omit [FiniteDimensional F2 E] in
theorem step_global (d j : ℕ) (hj : j < d) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d ((2 : ℝ) ^ (2 * (d + 1)) * η) (step d j f) := by
  let a := node j / (node j - node d)
  let b := (node j - node d)⁻¹
  have ha : 0 ≤ a := div_nonneg (node_pos j).le (node_gap hj).1.le
  have hb : 0 ≤ b := inv_nonneg.mpr (node_gap hj).1.le
  let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
  let fs : Fin 2 → (E →ₗ[F2] F) → ℝ := fun i =>
    if i = 0 then f else fun X => -rankNoise f X
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simpa [w] using ha
    · simpa [w] using hb
  have hfs : ∀ i, RestrictionGlobal d η (fs i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simpa [fs] using hf
    · simpa [fs] using restrictionGlobal_neg d η (rankNoise f) (rankNoise_global d η f hf)
  have hs := restrictionGlobal_weighted_sum w fs d η hw hfs
  have he : (fun X => ∑ i : Fin 2, w i * fs i X) = step d j f := by
    funext X
    simp [w, fs, Fin.sum_univ_succ, step, a, b, div_eq_mul_inv]
    ring
  have hwSum : (∑ i : Fin 2, w i) = a + b := by simp [w, Fin.sum_univ_succ]
  rw [he, hwSum] at hs
  apply global_mono_bound _ hs
  have hc : a + b ≤ (2 : ℝ) ^ (d + 1) := step_coefficient_bound hj
  have hsq : (a + b) ^ 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (show 0 ≤ (2 : ℝ) ^ (d + 1) + (a + b) by positivity)]
  have hp : ((2 : ℝ) ^ (d + 1)) ^ 2 = (2 : ℝ) ^ (2 * (d + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp] at hsq
  exact mul_le_mul_of_nonneg_right hsq (global_nonneg d η f hf)

omit [FiniteDimensional F2 E] in
theorem iterateFilter_global (d k : ℕ) (hk : k ≤ d) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : RestrictionGlobal d η f) :
    RestrictionGlobal d ((2 : ℝ) ^ (2 * k * (d + 1)) * η) (iterateFilter d k f) := by
  induction k with
  | zero => simpa [iterateFilter] using hf
  | succ k ih =>
    have hk' : k ≤ d := by omega
    have hs := step_global d k (by omega) _ _ (ih hk')
    have hex : 2 * (d + 1) + 2 * k * (d + 1) = 2 * (k + 1) * (d + 1) := by ring
    simpa only [iterateFilter, ← mul_assoc, ← pow_add, hex] using hs

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem rankNoise_coeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (rankNoise f) S = node (frequencyRank S) * linearCoeff f S := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (E →ₗ[F2] F2) := linearMapFintype
  rw [rankNoise, UniqueGamesTheorem.Fourier.MatrixNoise.linearRealNoiseOperator_coeff,
    linearNoiseEigenvalue_uniform, node_eq_inv_pow]
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (F →ₗ[F2] E)] in
theorem coefficient_linearCombination (a b : ℝ) (f g : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (fun X => a * f X + b * g X) S =
      a * linearCoeff f S + b * linearCoeff g S := by
  unfold linearCoeff
  simp_rw [add_mul, mul_assoc, Finset.expect_add_distrib, ← Finset.mul_expect]

theorem step_coeff (d j : ℕ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (step d j f) S =
      ((node j - node (frequencyRank S)) / (node j - node d)) * linearCoeff f S := by
  have he : step d j f = fun X =>
      (node j / (node j - node d)) * f X +
        (-1 / (node j - node d)) * rankNoise f X := by
    funext X
    dsimp [step]
    ring
  rw [he, coefficient_linearCombination, rankNoise_coeff]
  simp only [div_eq_mul_inv]
  ring

theorem iterateFilter_coeff (d k : ℕ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (iterateFilter d k f) S =
      multiplier d k (frequencyRank S) * linearCoeff f S := by
  induction k with
  | zero => simp [iterateFilter, multiplier]
  | succ k ih => rw [iterateFilter, step_coeff, ih, multiplier_succ]; ring

theorem iterateFilter_coeff_low (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : frequencyRank S ≤ d) :
    linearCoeff (iterateFilter d d f) S =
      if frequencyRank S = d then linearCoeff f S else 0 := by
  rw [iterateFilter_coeff]
  by_cases he : frequencyRank S = d
  · rw [he, multiplier_target d d le_rfl]
    simp
  · have hl : frequencyRank S < d := by omega
    rw [multiplier_below d d _ hl]
    simp [he]

omit [Finite E] [Finite F] in
theorem rankLevel_eq_projector (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    rankLevel d f = Derivatives.spectralProjector (fun Y => frequencyRank Y = d) f := by
  apply Derivatives.function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_rankLevel, Derivatives.linearCoeff_spectralProjector]
  by_cases h : frequencyRank Y = d <;> simp [h]

theorem filtered_compression_projector (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (A : Submodule F2 E) (B : Submodule F2 F) (hord : order A B ≤ d) :
    Derivatives.spectralProjector
      (fun Y => frequencyRank (Restriction.compressFrequency A B Y) = d - order A B)
      (iterateFilter d d f) = Derivatives.hybridProjector A B (rankLevel d f) := by
  apply Derivatives.function_eq_of_linearCoeff_eq
  intro Y
  simp only [Derivatives.hybridProjector, Derivatives.linearCoeff_spectralProjector,
    linearCoeff_rankLevel]
  have hb := Level.LinearRank.compression_rank_bounds A B Y
  have hs := Level.LinearRank.hybrid_rank_loss_iff A B Y
  change frequencyRank (Restriction.compressFrequency A B Y) ≤ frequencyRank Y ∧
    frequencyRank Y ≤ frequencyRank (Restriction.compressFrequency A B Y) +
      Module.finrank F2 A + Module.finrank F2 (F ⧸ B) at hb
  change frequencyRank (Restriction.compressFrequency A B Y) + Module.finrank F2 A +
      Module.finrank F2 (F ⧸ B) = frequencyRank Y ↔ LinearIdentities.Hybrid Y A B at hs
  have ho : Module.finrank F2 A + Module.finrank F2 (F ⧸ B) ≤ d := hord
  by_cases hc : frequencyRank (Restriction.compressFrequency A B Y) = d - order A B
  · have hrle : frequencyRank Y ≤ d := by dsimp [order] at hc; omega
    rw [ite_eq_left hc, iterateFilter_coeff_low d f Y hrle]
    by_cases hr : frequencyRank Y = d
    · have hhy : LinearIdentities.Hybrid Y A B := hs.mp (by dsimp [order] at hc; omega)
      simp [hr, hhy]
    · simp [hr]
  · rw [ite_eq_right hc]
    by_cases hhy : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hhy]
      by_cases hr : frequencyRank Y = d
      · have hl := hs.mpr hhy
        have he : frequencyRank (Restriction.compressFrequency A B Y) = d - order A B := by
          dsimp [order]
          omega
        exact (hc he).elim
      · simp [hr]
    · simp [hhy]

theorem hybridDerivative_rankLevel_eq_local_projection (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))] (T : E →ₗ[F2] F) (hord : order A B ≤ d) :
    Derivatives.hybridDerivative A B T (rankLevel d f) =
      rankLevel (d - order A B) (restrict (iterateFilter d d f) A B T) := by
  rw [rankLevel_eq_projector (d - order A B) (restrict (iterateFilter d d f) A B T),
    Derivatives.spectralProjector_restriction,
    filtered_compression_projector d f A B hord]
  rfl

theorem hybridDerivative_rankLevel_energy_le_strong_oai (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsRestrictionGlobal f d η)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F)
    (hord : order A B ≤ d) :
    (𝔼 N, Derivatives.hybridDerivative A B T (rankLevel d f) N ^ 2) ≤
      (2 : ℝ) ^ (2 * d * (d + 1)) * η := by
  classical
  let : Finite (E ⧸ A) := Finite.of_surjective A.mkQ A.mkQ_surjective
  let : Fintype (B →ₗ[F2] (E ⧸ A)) := linearMapFintype
  have hglobal : RestrictionGlobal d η f := by
    intro A' B' horder T'
    exact hf A' B' T' horder
  have hg := iterateFilter_global d d le_rfl η f hglobal
  rw [hybridDerivative_rankLevel_eq_local_projection d f A B T hord]
  exact (rankLevel_energy_le _ _).trans (hg A B hord T)

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.hybridDerivative_rankLevel_energy_le_strong_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.hybridDerivative_rankLevel_energy_le_strong_oai.{u_1, u_2}
