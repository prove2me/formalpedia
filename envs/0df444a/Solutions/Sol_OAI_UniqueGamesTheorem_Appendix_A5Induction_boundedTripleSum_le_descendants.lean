-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:49.27261+00:00
-- url     : https://prove2.me/submissions/4242aaca-3f03-4cc4-9d58-f4af40960aad

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
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5Induction_postA5Sum_hybrid_average
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_a5_energySquare_le

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

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

end OAI
end

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

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

theorem factorViaRange_apply {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) (u : U) :
    factorViaRange X P hker (X.rangeRestrict u) = P u := by
  have hq : X.quotKerEquivRange.symm (X.rangeRestrict u) = X.ker.mkQ u :=
    X.quotKerEquivRange.symm_apply_apply (X.ker.mkQ u)
  dsimp only [factorViaRange, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hq]
  rfl

theorem factorViaRange_range {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    (factorViaRange X P hker).range = P.range := by
  have hc : (factorViaRange X P hker).comp X.rangeRestrict = P := by
    apply LinearMap.ext
    intro u
    exact factorViaRange_apply X P hker u
  calc
    _ = ((factorViaRange X P hker).comp X.rangeRestrict).range :=
      (LinearMap.range_comp_of_range_eq_top _ X.range_rangeRestrict).symm
    _ = _ := congrArg LinearMap.range hc

end Generic

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

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
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
/-- Every member of a compression fiber has rank `rank X + rank Z`. -/
theorem fiber_rank (X : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range)) (Y : Fiber X Z) :
    finrank F2 Y.val.range = finrank F2 X.range + finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  have h := CompressionCount.fiber_rank
    ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z)
    ((fiberEquiv X Z P hP C hC) Y)
  change finrank F2 (toBlocks X P hP C hC Y.val).range =
    finrank F2 X.range +
      finrank F2 ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z).range at h
  rw [finrank_toBlocks, finrank_comp_equiv] at h
  exact h

end

end UniqueGamesTheorem.Appendix.FullCompression

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
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

variable [Finite E] [Finite F]

theorem linearCoeff_mapDerivative (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (Z : X.ker →ₗ[F2] (E ⧸ X.range)) :
    linearCoeff (mapDerivative X f) Z =
      ∑ Y : F →ₗ[F2] E,
        if RankAdditivity.RankBelow X Y ∧
            Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0 := by
  classical
  unfold mapDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [rankProjector, linearCoeff_spectralProjector]
  have hp : (linearTraceCharacter Y (0 : E →ₗ[F2] F)).re = 1 := by simp
  rw [hp]
  by_cases hR : RankAdditivity.RankBelow X Y <;>
    by_cases hC : Restriction.compressFrequency X.range X.ker Y = Z <;> simp [hR, hC]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

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

variable [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.compressedDualFintype
theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem degree_mapDerivative (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - frequencyRank X) (mapDerivative X f) := by
  intro Z hZ
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem degree_map_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - (order A B + frequencyRank X))
      (mapDerivative X (hybridDerivative A B T f)) := by
  simpa only [Nat.sub_sub] using
    degree_mapDerivative X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)

end UniqueGamesTheorem.Appendix.DerivativeDegree

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A5IndexCount
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A5IndexCount

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

theorem projectionA0_injective (A I A0 A0' : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A)
    (hd' : Disjoint A0' I) (hj' : A0' ⊔ I = A)
    (h : projectionA0 A I A0 hIA hd hj = projectionA0 A I A0' hIA hd' hj') :
    A0 = A0' := by
  let P := I.comap A.subtype
  let Q : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩
  let Q' : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0'.comap A.subtype, internal_isCompl A I A0' hIA hd' hj'⟩
  have hp : (P.isComplEquivProj Q).val = (P.isComplEquivProj Q').val := by
    apply LinearMap.ext
    intro a
    apply (insideEquiv A I hIA).injective
    exact LinearMap.congr_fun h a
  have hQ := P.isComplEquivProj.injective (Subtype.ext hp)
  have hq : A0.comap A.subtype = A0'.comap A.subtype := congrArg Subtype.val hQ
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  have hA0' : A0' ≤ A := le_sup_left.trans hj'.le
  ext x
  constructor
  · intro hx
    have hm : (⟨x, hA0 hx⟩ : A) ∈ A0.comap A.subtype := hx
    rw [hq] at hm
    exact hm
  · intro hx
    have hm : (⟨x, hA0' hx⟩ : A) ∈ A0'.comap A.subtype := hx
    rw [← hq] at hm
    exact hm

theorem fullRange_surjective {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    Function.Surjective (fullRange S hS) := fun c => ⟨c.val, Subtype.ext rfl⟩

theorem range_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range = (A4IndexCount.quotientRestriction B B0).range := by
  rw [sectionB0, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (fullRange_surjective _ _))]
  exact A4IndexCount.factorViaRange_range _ _ _

theorem recover_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range.comap B.mkQ = B0 := by
  rw [range_sectionB0]
  have hB : B ≤ B0 := hm.symm.le.trans inf_le_left
  ext w
  change B.mkQ w ∈ (A4IndexCount.quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hz : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hz) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem sectionB0_injective (B J B0 B0' : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B)
    (hc' : B0' ⊔ J = ⊤) (hm' : B0' ⊓ J = B)
    (h : sectionB0 B J B0 hc hm = sectionB0 B J B0' hc' hm') : B0 = B0' := by
  calc
    B0 = (sectionB0 B J B0 hc hm).range.comap B.mkQ :=
      (recover_sectionB0 B J B0 hc hm).symm
    _ = (sectionB0 B J B0' hc' hm').range.comap B.mkQ :=
      congrArg (fun T : (W ⧸ J) →ₗ[F2] (W ⧸ B) => T.range.comap B.mkQ) h
    _ = B0' := recover_sectionB0 B J B0' hc' hm'

theorem encode_injective (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) : Function.Injective (encode X A B hIA) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact projectionA0_injective A X.range p.val.1 q.val.1 hIA
      p.property.1 p.property.2.1 q.property.1 q.property.2.1 (congrArg Prod.fst h)
  · exact sectionB0_injective B X.ker p.val.2 q.val.2
      p.property.2.2.1 p.property.2.2.2 q.property.2.2.1 q.property.2.2.2
      (congrArg Prod.snd h)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_geometricIndex_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B))) := by
  have hfirst := CompressionCount.natCard_linearMap (U := A) (C := X.range)
  have hsecond := CompressionCount.natCard_linearMap (U := W ⧸ X.ker) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] X.range) := Nat.finite_of_card_ne_zero
    (by rw [hfirst]; exact pow_ne_zero _ (by decide))
  let : Finite ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero
    (by rw [hsecond]; exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode X A B hIA) (encode_injective X A B hIA)
  rw [Nat.card_prod, hfirst, hsecond, X.quotKerEquivRange.finrank_eq, ← pow_add] at h
  have he : Module.finrank F2 A * Module.finrank F2 X.range +
      Module.finrank F2 X.range * Module.finrank F2 (W ⧸ B) =
      Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) := by ring
  rwa [he] at h

theorem card_geometricIndex_degree_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (2 * d * Module.finrank F2 X.range) := by
  have hs : Module.finrank F2 A + Module.finrank F2 (W ⧸ B) ≤ 2 * d := by omega
  have he : Module.finrank F2 X.range *
      (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) ≤
      2 * d * Module.finrank F2 X.range := by
    calc
      _ ≤ Module.finrank F2 X.range * (2 * d) := Nat.mul_le_mul_left _ hs
      _ = _ := by ac_rfl
  exact (card_geometricIndex_le X A B hIA).trans
    (Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) he)

theorem card_geometricIndex_cube_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ^ 3 ≤
      2 ^ (6 * d * Module.finrank F2 X.range) := by
  have h := Nat.pow_le_pow_left (card_geometricIndex_degree_le X A B hIA d hA hB) 3
  rw [← pow_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end UniqueGamesTheorem.Appendix.A5IndexCount

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
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

local instance quotientFinite_r3e0ee5_1 (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
local instance compressedDualFintype_r3e0ee5_1 (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective
omit [Finite E] in
theorem finrank_comap_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) :
    Module.finrank F2 (C.comap A.mkQ) = Module.finrank F2 A + Module.finrank F2 C := by
  let P := C.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  let q : P →ₗ[F2] (E ⧸ A) := A.mkQ.comp P.subtype
  have hR : q.range = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y, hy⟩ := A.mkQ_surjective x
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change A.mkQ y ∈ C
        rw [hy]
        exact hx
      · exact hy
  have hK : q.ker.map P.subtype = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hz : (y : E) ∈ LinearMap.ker A.mkQ := hy
      change (y : E) ∈ A
      simpa only [Submodule.ker_mkQ] using hz
    · intro hx
      refine Submodule.mem_map.mpr ⟨⟨x, hAP hx⟩, ?_, rfl⟩
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
  have hKdim := Submodule.finrank_map_subtype_eq P q.ker
  rw [hK] at hKdim
  have hdim := q.finrank_range_add_finrank_ker
  rw [hR, ← hKdim] at hdim
  change Module.finrank F2 P = Module.finrank F2 A + Module.finrank F2 C
  omega

end UniqueGamesTheorem.Appendix.HybridComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A5FrequencyTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Dimension bounds for the outer subspaces used by the actual A.5 operator
identity, obtained from the order of an actual derivative-space index. -/
theorem lifted_outer_dimensions (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d) :
    Module.finrank F2 (C.comap X.range.mkQ) ≤ d ∧
      Module.finrank F2 (F ⧸ D.map X.ker.subtype) ≤ d := by
  have hC := HybridComposition.finrank_comap_mkQ X.range C
  have hD := Submodule.finrank_map_subtype_eq X.ker D
  have hKD := D.finrank_quotient_add_finrank
  have hFD := (D.map X.ker.subtype).finrank_quotient_add_finrank
  have hX := X.finrank_range_add_finrank_ker
  change Module.finrank F2 X.range +
    (Module.finrank F2 C + Module.finrank F2 (X.ker ⧸ D)) ≤ d at hcut
  constructor <;> omega

/-- The native A.5 energy inequality with its actually proved numerical
complement factor. The only cutoff is the rank plus the outer derivative order. -/
theorem a5_energySquare_le_power (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    [Fintype (OperatorPartitions.A5GeometricIndex X
      (C.comap X.range.mkQ) (D.map X.ker.subtype))]
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (S : Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) ^ 2 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
        ∑ p : OperatorPartitions.A5GeometricIndex X
          (C.comap X.range.mkQ) (D.map X.ker.subtype),
          (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
            (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
  have hI : X.range ≤ C.comap X.range.mkQ := by
    intro x hx
    change X.range.mkQ x ∈ C
    have hz : X.range.mkQ x = 0 := by
      change x ∈ LinearMap.ker X.range.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map X.ker.subtype ≤ X.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hCmap : (C.comap X.range.mkQ).map X.range.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := X.range.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hDcomap : (D.map X.ker.subtype).comap X.ker.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hdims := lifted_outer_dimensions X C D d hcut
  have hcount := A5IndexCount.card_geometricIndex_cube_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI d hdims.1 hdims.2
  rw [Nat.card_eq_fintype_card] at hcount
  have hcountR :
      (Fintype.card (OperatorPartitions.A5GeometricIndex X
        (C.comap X.range.mkQ) (D.map X.ker.subtype)) : ℝ)^3 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) := by exact_mod_cast hcount
  have hn := OperatorNorm.a5_energySquare_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI hB f S
  have hfinal := hn.trans
    (mul_le_mul_of_nonneg_right hcountR
      (Finset.sum_nonneg (fun p _ => sq_nonneg _)))
  let energy (C' : Submodule F2 (E ⧸ X.range)) (D' : Submodule F2 X.ker) : ℝ :=
    (𝔼 N, hybridDerivative C' D' S (mapDerivative X f) N ^ 2)^2
  have he : energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) = energy C D :=
    congrArg₂ energy hCmap hDcomap
  change energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) ≤ _ at hfinal
  rw [he] at hfinal
  exact hfinal

theorem mapDerivative_hybridMomentSum_le (d e : ℕ) (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (hcut : Module.finrank F2 X.range + e ≤ d) :
    hybridMomentSum e (mapDerivative X f) ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) * postA5Sum X e f := by
  unfold hybridMomentSum postA5Sum
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  let : Fintype (OperatorPartitions.A5GeometricIndex X
      (s.val.1.comap X.range.mkQ) (s.val.2.map X.ker.subtype)) :=
    A5Passage.pairFintype X s
  have hs : Module.finrank F2 X.range + order s.val.1 s.val.2 ≤ d := by
    have ho := s.property
    omega
  calc
    (𝔼 S, (𝔼 N, hybridDerivative s.val.1 s.val.2 S (mapDerivative X f) N ^ 2)^2) ≤
        𝔼 S, (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
          ∑ p : A5Passage.Pair X s,
            (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
              (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
      apply Finset.expect_le_expect
      intro S _
      exact a5_energySquare_le_power X s.val.1 s.val.2 d hs f S
    _ = _ := by rw [← Finset.mul_expect, Finset.expect_sum_comm]

/-- The actual A.15 induction step for one positive-order derivative triple.
The induction hypothesis is used only at the strictly smaller degree `d-t`,
on its genuine quotient-domain and kernel-codomain spaces. -/
theorem a15_of_strong_induction (d t : ℕ) (A : Submodule F2 E)
    (B : Submodule F2 F) (X : B →ₗ[F2] (E ⧸ A))
    (ht : t = order A B + Module.finrank F2 X.range)
    (htpos : 0 < t) (htd : t ≤ d)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
      (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
        A5Passage.descendantSum A B X (d - t) f := by
  have hlt : d - t < d := by omega
  have hcut : Module.finrank F2 X.range + (d - t) ≤ d := by omega
  have hpoint (T : E →ₗ[F2] F) :
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) := by
    have hdeg : DegreeAtMost (d - t) (mapDerivative X (hybridDerivative A B T f)) := by
      simpa only [ht, frequencyRank] using degree_map_hybridDerivative A B X T f hf
    have hIH := ih (d - t) hlt (mapDerivative X (hybridDerivative A B T f)) hdeg
    have hnorm := mapDerivative_hybridMomentSum_le d (d - t) X
      (hybridDerivative A B T f) hcut
    calc
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
          (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
            hybridMomentSum (d - t) (mapDerivative X (hybridDerivative A B T f)) := hIH
      _ ≤ (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
          ((2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
            postA5Sum X (d - t) (hybridDerivative A B T f)) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = _ := by rw [pow_add]; ring
  calc
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        𝔼 T, (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) :=
      Finset.expect_le_expect (fun T _ => hpoint T)
    _ = _ := by rw [← Finset.mul_expect, postA5Sum_hybrid_average]

/-- Apply the genuine lower-degree induction step to every term of the
checked A.13 sum, preserving its original positive-order cutoff. -/
theorem boundedTripleSum_le_descendants_oai (d : ℕ)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    A13Reduction.boundedPositiveTripleSum d f ≤
      ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
        (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
          24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
          A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
            (d - A13Index.size p.val) f := by
  unfold A13Reduction.boundedPositiveTripleSum
  apply Finset.sum_le_sum
  intro p _
  have h15 := a15_of_strong_induction d (A13Index.size p.val)
    p.val.1 p.val.2.1 p.val.2.2 rfl p.property.1 p.property.2 ih f hf
  have hw := mul_le_mul_of_nonneg_left h15
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (24 * d * A13Index.size p.val))
  have he : 24 * d * A13Index.size p.val +
      (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
        6 * d * Module.finrank F2 p.val.2.2.range) =
      100 * (d - A13Index.size p.val)^2 + 24 * d * A13Index.size p.val +
        6 * d * Module.finrank F2 p.val.2.2.range := by ring
  calc
    A13Reduction.tripleTerm d p.val f ≤
        (2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          ((2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f) := hw
    _ = ((2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          (2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range)) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f := by ring
    _ = _ := by rw [← pow_add, he]

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants_oai.{u, v} := @OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants_oai.{u, v}
