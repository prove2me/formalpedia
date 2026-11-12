-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:54.04778+00:00
-- url     : https://prove2.me/submissions/c247a956-4d70-48a1-b343-8500884330a6

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
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A13Reduction_degree_reduction_truncated
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5ForwardIndex_card_fiber_le
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5Induction_boundedTripleSum_le_descendants
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5Induction_recurrence_closure

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.Induction

theorem square_remainder_budget (d t : Nat) (ht : t ≤ d) :
    (d - t) * (d - t) + d * t ≤ d * d := by
  have hm := Nat.mul_le_mul_left (d - t) (Nat.sub_le d t)
  have hs : d - t + t = d := by omega
  have he : (d - t) * d + t * d = d * d := by
    rw [← Nat.add_mul, hs]
  rw [Nat.mul_comm d t]
  omega

/-- The exponent inequality preceding (A.16), with negative exponents moved
to the left side so natural subtraction cannot hide an invalid inequality. -/
theorem induction_exponent_budget (d t k : Nat) (ht : t ≤ d) (hk : k ≤ t) :
    100 * ((d - t) * (d - t)) + 27 * (d * t) + 6 * (d * k) +
      63 * (d * t) + 4 * (d * k) ≤ 100 * (d * d) := by
  have hs := Nat.mul_le_mul_left 100 (square_remainder_budget d t ht)
  have hm := Nat.mul_le_mul_left d hk
  omega

/-- For positive k the geometric-series exponent has at least d of slack. -/
theorem positive_rank_geometric_slack (d k : Nat) (hk : 1 ≤ k) :
    31 * (d * (k + 1)) + d ≤ 63 * (d * k) := by
  have hm := Nat.mul_le_mul_left d hk
  have he : d * (k + 1) = d * k + d := by simp [Nat.mul_add]
  omega

end UniqueGamesTheorem.Appendix.Induction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

variable [FiniteDimensional K W]

/-- Compression preserves the full rank when its quotient is disjoint
from the image and its restricted domain spans the domain modulo the kernel. -/
theorem compress_rank_preserved (X : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hdis : Disjoint A (LinearMap.range X))
    (hcover : B ⊔ LinearMap.ker X = ⊤) :
    Module.finrank K (LinearMap.range (compress X A B)) =
      Module.finrank K (LinearMap.range X) := by
  have hrestrict : LinearMap.range (X.domRestrict B) = LinearMap.range X := by
    apply le_antisymm (LinearMap.range_domRestrict_le_range X B)
    intro v hv
    rcases hv with ⟨w, hw⟩
    have hwtop : w ∈ B ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    change X b = v
    rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]
  have h := (A.mkQ.comp (LinearMap.range X).subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (A.mkQ.comp (LinearMap.range X).subtype) =
      LinearMap.range (compress X A B) := by
    simp only [compress, LinearMap.range_comp, Submodule.range_subtype, hrestrict]
  rw [hr, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.disjoint_iff_comap_eq_bot.mp hdis.symm] at h
  simpa using h

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

section

/-! The degree-zero base case in the actual finite binary Fourier model. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.DegreeZero
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem rank_pos_of_ne_zero (Y : F →ₗ[F2] E) (hY : Y ≠ 0) :
    0 < Module.finrank F2 Y.range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hb : Y.range = ⊥ := Submodule.finrank_eq_zero.mp hr
  apply hY
  ext x
  have hx : Y x ∈ Y.range := ⟨x, rfl⟩
  rw [hb] at hx
  exact hx

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_constant_of_degree_zero (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0)
    (M : E →ₗ[F2] F) : f M = linearCoeff f 0 := by
  classical
  rw [← linear_fourier_inversion f M, Finset.sum_eq_single (0 : F →ₗ[F2] E)]
  · simp
  · intro Y _ hY
    rw [hdegree Y (rank_pos_of_ne_zero Y hY), zero_mul]
  · simp

theorem fourth_moment_eq_energy_sq (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) = (𝔼 M, f M^2)^2 := by
  simp only [eq_constant_of_degree_zero f hdegree, Fintype.expect_const]
  rw [← pow_mul]

end UniqueGamesTheorem.Appendix.DegreeZero

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5Scalar

theorem geometric_sum_le (q : ℝ) (n : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    (∑ i ∈ Finset.range n, q ^ i) ≤ 4 / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ, pow_zero, ← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right ih hq₀]

theorem pair_sum_factor (q : ℝ) (n m k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), q ^ (i + j + k)) =
      ((∑ i ∈ Finset.range (n + 1), q ^ i) *
        (∑ j ∈ Finset.range (m + 1), q ^ j)) * q ^ k := by
  simp only [pow_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The exact decomposition with the origin deleted. -/
theorem positiveSum_zero_eq (q : ℝ) (n m : ℕ) :
    positiveSum q n m 0 =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) +
        q * (∑ j ∈ Finset.range m, q ^ j) := by
  have htail : (∑ j ∈ Finset.range (m + 1), if 1 ≤ j then q ^ j else 0) =
      q * (∑ j ∈ Finset.range m, q ^ j) := by
    rw [Finset.sum_range_succ']
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have hshift : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (m + 1), q ^ (i + 1 + j)) =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) := by
    simp only [pow_add, pow_one, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos : ∀ i j : ℕ, 1 ≤ i + 1 + j := by
    intro i j
    omega
  unfold positiveSum
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.zero_add, hpos, ↓reduceIte]
  rw [htail, hshift]

theorem positiveSum_zero_le (q : ℝ) (n m : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    positiveSum q n m 0 ≤ 4 * q := by
  have hn := geometric_sum_le q n hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm' := geometric_sum_le q m hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  rw [positiveSum_zero_eq]
  have h₁ := mul_le_mul_of_nonneg_left hp hq₀
  have h₂ := mul_le_mul_of_nonneg_left hm' hq₀
  nlinarith

theorem positiveSum_pos_le (q : ℝ) (n m k : ℕ) (hq₀ : 0 ≤ q)
    (hq : q ≤ 1 / 4) (hk : 1 ≤ k) : positiveSum q n m k ≤ 2 * q ^ k := by
  have hpos : ∀ i j : ℕ, 1 ≤ i + j + k := by
    intro i j
    omega
  simp only [positiveSum, hpos, ↓reduceIte]
  rw [pair_sum_factor]
  have hn := geometric_sum_le q (n + 1) hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  calc
    _ ≤ ((4 / 3 : ℝ) * (4 / 3)) * q ^ k :=
      mul_le_mul_of_nonneg_right hp (pow_nonneg hq₀ k)
    _ ≤ 2 * q ^ k := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hq₀ k)

/-- The original positive-order geometric bound in (A.16), with independent
finite truncations. No upper bound on `k` is required. -/
theorem a16_finite_geometric (d n m k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (63 * d)
  have hq₀ : 0 ≤ q := pow_nonneg (by norm_num) _
  have hq : q ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ ((2 : ℝ)⁻¹) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have heq : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) =
        positiveSum q n m k := by
    simp only [positiveSum, q, pow_mul]
  rw [heq]
  by_cases hk : k = 0
  · subst k
    calc
      _ ≤ 4 * q := positiveSum_zero_le q n m hq₀ hq
      _ ≤ 4 * ((2 : ℝ)⁻¹) ^ (31 * d + 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (0 + 1)) := by
          norm_num [pow_add]
          ring
  · have hkpos : 1 ≤ k := by omega
    have hs := Induction.positive_rank_geometric_slack d k hkpos
    have hex : 31 * d * (k + 1) + 1 ≤ 63 * d * k := by nlinarith
    calc
      _ ≤ 2 * q ^ k := positiveSum_pos_le q n m k hq₀ hq hkpos
      _ = 2 * ((2 : ℝ)⁻¹) ^ (63 * d * k) := by
        dsimp only [q]
        rw [← pow_mul]
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1) + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hex) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
          norm_num [pow_add]
          ring

theorem a16_original_range (d k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) :=
  a16_finite_geometric d d d k hd

end UniqueGamesTheorem.Appendix.A5Scalar

end

end

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

theorem exponent_weight_le (d t k : ℕ) (ht : t ≤ d) (hk : k ≤ t) :
    (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have he : (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) +
      (63 * d * t + 4 * d * k) ≤ 100 * d * d := by
    simpa only [pow_two, Nat.mul_assoc, Nat.add_assoc] using
      Induction.induction_exponent_budget d t k ht hk
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  rw [pow_add] at hp
  have hn : (2 : ℝ) ^ (63 * d * t + 4 * d * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (63 * d * t + 4 * d * k)))
  rw [mul_assoc, mul_inv_cancel₀ hn, mul_one] at hm
  simpa only [inv_pow] using hm

theorem counted_weight_le (d t k c : ℕ) (ht : t ≤ d) (hk : k ≤ t)
    (hc : c ≤ 2 ^ (3 * d * t)) :
    (c : ℝ) * (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have hc' : (c : ℝ) ≤ (2 : ℝ) ^ (3 * d * t) := by exact_mod_cast hc
  calc
    _ ≤ (2 : ℝ) ^ (3 * d * t) *
        (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) :=
      mul_le_mul_of_nonneg_right hc' (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) := by
      rw [← pow_add]
      congr 1
      ring
    _ ≤ _ := exponent_weight_le d t k ht hk

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Exact finite grouping by the actual result and both dimension indices. -/
theorem sum_grouped (d : ℕ) (result : α → β) (i j : α → ℕ)
    (hbound : ∀ a, i a ≤ d ∧ j a ≤ d) (C : β → ℕ → ℕ → ℝ) :
    (∑ a, C (result a) (i a) (j a)) =
      ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        ((fiber result i j b r s).card : ℝ) * C b r s := by
  classical
  let key : α → β × ℕ × ℕ := fun a => (result a, i a, j a)
  let target : Finset (β × ℕ × ℕ) :=
    Finset.univ ×ˢ (Finset.range (d + 1) ×ˢ Finset.range (d + 1))
  let G : β × ℕ × ℕ → ℝ := fun p => C p.1 p.2.1 p.2.2
  have hmap : ∀ a ∈ (Finset.univ : Finset α), key a ∈ target := by
    intro a _
    simp only [target, key, Finset.mem_product, Finset.mem_univ,
      Finset.mem_range, true_and]
    exact ⟨Nat.lt_succ_iff.mpr (hbound a).1, Nat.lt_succ_iff.mpr (hbound a).2⟩
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := target)
    (g := key) hmap G
  simpa only [target, Finset.sum_product, G, key, Prod.mk.injEq,
    Finset.sum_const, nsmul_eq_mul, fiber] using h.symm

theorem weighted_reindex (d : ℕ) (hd : 1 ≤ d)
    (result : α → β) (i j : α → ℕ) (k : β → ℕ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (horder : ∀ a, 1 ≤ i a + j a + k (result a) ∧ i a + j a + k (result a) ≤ d)
    (hcard : ∀ b r s,
      Nat.card {a : α // result a = b ∧ i a = r ∧ j a = s} ≤
        2 ^ (3 * d * (r + s + k b))) :
    (∑ a, (2 : ℝ) ^ (100 * (d - (i a + j a + k (result a))) ^ 2 +
        24 * d * (i a + j a + k (result a)) + 6 * d * k (result a)) * w (result a)) ≤
      (2 : ℝ) ^ (100 * d * d) *
        ∑ b, ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1) + 4 * d * k b) * w b := by
  classical
  let C : β → ℕ → ℕ → ℝ := fun b r s =>
    (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
      24 * d * (r + s + k b) + 6 * d * k b) * w b
  let envelope : β → ℝ := fun b =>
    (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (4 * d * k b) * w b
  have henvelope : ∀ b, 0 ≤ envelope b := by
    intro b
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (by norm_num) _)) (hw b)
  have hbound : ∀ a, i a ≤ d ∧ j a ≤ d := by
    intro a
    have h := (horder a).2
    omega
  have hfiber : ∀ b r s,
      ((fiber result i j b r s).card : ℝ) * C b r s ≤
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
    intro b r s
    by_cases hne : (fiber result i j b r s).Nonempty
    · obtain ⟨a, ha⟩ := hne
      rcases Finset.mem_filter.mp ha with ⟨_, hr, hi, hj⟩
      have ht := horder a
      rw [hr, hi, hj] at ht
      have hc : (fiber result i j b r s).card ≤ 2 ^ (3 * d * (r + s + k b)) := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, fiber] using hcard b r s
      have hweight := counted_weight_le d (r + s + k b) (k b)
        (fiber result i j b r s).card ht.2 (by omega) hc
      rw [ite_eq_left ht.1]
      calc
        _ = (((fiber result i j b r s).card : ℝ) *
            (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
              24 * d * (r + s + k b) + 6 * d * k b)) * w b := by
          dsimp only [C]
          ring
        _ ≤ ((2 : ℝ) ^ (100 * d * d) *
            ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b) + 4 * d * k b)) * w b :=
          mul_le_mul_of_nonneg_right hweight (hw b)
        _ = envelope b * ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) := by
          dsimp only [envelope]
          rw [pow_add]
          ring
    · have hz : (fiber result i j b r s).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      rw [hz, Nat.cast_zero, zero_mul]
      apply mul_nonneg (henvelope b)
      split_ifs <;> positivity
  change (∑ a, C (result a) (i a) (j a)) ≤ _
  rw [sum_grouped d result i j hbound C]
  calc
    _ ≤ ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun s _ => hfiber b r s)
    _ = ∑ b, envelope b *
        (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
          if 1 ≤ r + s + k b then ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ b, envelope b * ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (A5Scalar.a16_original_range d (k b) hd) (henvelope b)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [envelope]
      rw [pow_add]
      ring

end UniqueGamesTheorem.Appendix.A5WeightedReindex

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

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
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

local instance quotientFinite_rb76f31_1 (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
local instance compressedDualFintype_rb76f31_1 (A : Submodule F2 E) (B : Submodule F2 F) :
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

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem order_effective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    order (C.comap A.mkQ) (D.map B.subtype) = order A B + order C D := by
  have hA := finrank_comap_mkQ A C
  have hD := Submodule.finrank_map_subtype_eq B D
  have hFB := B.finrank_quotient_add_finrank
  have hBD := D.finrank_quotient_add_finrank
  have hFbar := (D.map B.subtype).finrank_quotient_add_finrank
  change Module.finrank F2 (C.comap A.mkQ) +
      Module.finrank F2 (F ⧸ D.map B.subtype) =
    (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      (Module.finrank F2 C + Module.finrank F2 (B ⧸ D))
  omega

end UniqueGamesTheorem.Appendix.HybridComposition

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
theorem dualFactor_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    Module.finrank F2 (dualFactor A B C D Z).range = Module.finrank F2 Z.range :=
  rank_arrowCongr (outputFactor B D) (quotientFactor A C).symm Z

end Nested
end UniqueGamesTheorem.Appendix.NaturalTransport

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

namespace Appendix.A5Passage

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

variable [Finite E] [Finite F]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dim_pairA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 q.2.val.1 = Module.finrank F2 q.1.val.1 := by
  have hsup := q.2.val.1.finrank_sup_add_finrank_inf_eq X.range
  rw [q.2.property.2.1, q.2.property.1.eq_bot, finrank_bot, add_zero] at hsup
  have hcomap := HybridComposition.finrank_comap_mkQ X.range q.1.val.1
  change Module.finrank F2 (LiftedA X q.1) =
    Module.finrank F2 X.range + Module.finrank F2 q.1.val.1 at hcomap
  omega

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem codim_pairB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (F ⧸ q.2.val.2) =
      Module.finrank F2 (X.ker ⧸ q.1.val.2) := by
  have hsup := q.2.val.2.finrank_sup_add_finrank_inf_eq X.ker
  rw [q.2.property.2.2.1, q.2.property.2.2.2, finrank_top] at hsup
  have hmap := Submodule.finrank_map_subtype_eq X.ker q.1.val.2
  change Module.finrank F2 (LiftedB X q.1) = Module.finrank F2 q.1.val.2 at hmap
  have hF := q.2.val.2.finrank_quotient_add_finrank
  have hK := q.1.val.2.finrank_quotient_add_finrank
  change Module.finrank F2 (X.ker ⧸ q.1.val.2) + Module.finrank F2 q.1.val.2 =
    Module.finrank F2 X.ker at hK
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 := by
  unfold UniqueGamesTheorem.Fourier.MatrixRestrictions.order
  rw [dim_pairA X q, codim_pairB X q]

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_rank (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (LinearIdentities.compress X q.2.val.1 q.2.val.2).range =
      Module.finrank F2 X.range :=
  LinearIdentities.compress_rank_preserved X q.2.val.1 q.2.val.2
    q.2.property.1 q.2.property.2.2.1

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
      (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      Module.finrank F2 X.range := by
  rw [NaturalTransport.dualFactor_rank]
  exact pair_rank X q

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 +
        Module.finrank F2 X.range := by
  rw [HybridComposition.order_effective, NaturalTransport.dualFactor_rank,
    pair_order, pair_rank]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_le (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (d : Nat)
    (h : UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range ≤ d)
    (q : Passage X (d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
      Module.finrank F2 X.range))) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range ≤ d := by
  rw [effective_order_rank]
  have hq := q.1.property
  change UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 ≤
    d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range) at hq
  omega

end Appendix.A5Passage

namespace Appendix.A5ForwardIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank {d : ℕ} (a : Index (E := E) (F := F) d) :
    targetRank (descendant a) = Module.finrank F2 a.1.val.2.2.range :=
  A5Passage.descendant_rank a.1.val.1 a.1.val.2.1 a.1.val.2.2 a.2

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_size {d : ℕ} (a : Index (E := E) (F := F) d) :
    sourceI a + sourceJ a + targetRank (descendant a) = A13Index.size a.1.val := by
  rw [descendant_rank]
  rfl

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_order_bounds {d : ℕ} (a : Index (E := E) (F := F) d) :
    1 ≤ sourceI a + sourceJ a + targetRank (descendant a) ∧
      sourceI a + sourceJ a + targetRank (descendant a) ≤ d := by
  rw [original_size]
  exact a.1.property

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_size_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.size (descendant a) ≤ d :=
  A5Passage.effective_order_rank_le a.1.val.1 a.1.val.2.1 a.1.val.2.2 d
    a.1.property.2 a.2

end Appendix.A5ForwardIndex

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

namespace Appendix.A5ReverseSum

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem targetWeight_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : 0 ≤ targetWeight d f r := by
  unfold targetWeight
  split_ifs
  · exact Finset.expect_nonneg fun _ _ => sq_nonneg _
  · exact le_refl _

theorem targetWeight_descendant (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    targetWeight d f (descendant a) = actualMoment f (descendant a) := by
  have h := descendant_size_le a
  have ho : order (descendant a).1 (descendant a).2.1 ≤ d := by
    unfold A13Index.size at h
    omega
  exact ite_eq_left ho

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- The target cutoff is exactly the actual finite hybrid index. -/
theorem sum_triples_cutoff (d : ℕ)
    (H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y := by
  classical
  let G : Submodule F2 E × Submodule F2 F → ℝ :=
    fun p => ∑ Y : p.2 →ₗ[F2] (E ⧸ p.1), H p.1 p.2 Y
  have hh : (∑ s : HybridIndex (E := E) (F := F) d, G s.val) =
      ∑ p : Submodule F2 E × Submodule F2 F,
        if order p.1 p.2 ≤ d then G p else 0 := by
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Submodule F2 E × Submodule F2 F =>
            order p.1 p.2 ≤ d), G p := by
        exact (Finset.sum_subtype _ (by simp) G).symm
      _ = _ := Finset.sum_filter _ _
  change _ = ∑ s : HybridIndex (E := E) (F := F) d, G s.val
  rw [hh, Fintype.sum_prod_type]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro A _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : order A B ≤ d
  · simp only [h, ite_true, if_true, G]
  · simp only [h, ite_false, if_false, Finset.sum_const_zero]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem target_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      ((2 : ℝ)⁻¹) ^ (31 * d * (targetRank r + 1) + 4 * d * targetRank r) *
        targetWeight d f r) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
        ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
          4 * d * Module.finrank F2 Y.range) *
          (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  let H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ := fun A B Y =>
    ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
      4 * d * Module.finrank F2 Y.range) * actualMoment f ⟨A, B, Y⟩
  calc
    _ = ∑ r : A13Index.Triple (E := E) (F := F),
        if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0 := by
      apply Finset.sum_congr rfl
      rintro ⟨A, B, Y⟩ _
      simp only [targetWeight, targetRank, H, mul_ite, mul_zero]
    _ = ∑ s : HybridIndex (E := E) (F := F) d,
        ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y :=
      sum_triples_cutoff d H
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  rw [← Finset.mul_expect]
  rfl

theorem source_summand_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
      24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
      6 * d * targetRank (descendant a)) * targetWeight d f (descendant a) =
    (2 : ℝ) ^ (100 * (d - A13Index.size a.1.val) ^ 2 +
      24 * d * A13Index.size a.1.val + 6 * d * Module.finrank F2 a.1.val.2.2.range) *
        actualMoment f (descendant a) := by
  rw [original_size, descendant_rank, targetWeight_descendant]

theorem source_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ a : Index (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
        24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
        6 * d * targetRank (descendant a)) * targetWeight d f (descendant a)) =
    ∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f := by
  simp_rw [source_summand_eq]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [A5Passage.descendantSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- The weighted sum of actual A.5 descendants is bounded by damped actual
map-derivative moments over all hybrid restrictions of order at most `d`. -/
theorem weighted_descendantSum_le (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f) ≤
    (2 : ℝ) ^ (100 * d * d) *
      ∑ s : HybridIndex (E := E) (F := F) d,
        𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
          ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
            4 * d * Module.finrank F2 Y.range) *
            (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  have h := A5WeightedReindex.weighted_reindex d hd
    (descendant (E := E) (F := F) (d := d)) sourceI sourceJ targetRank
    (targetWeight d f) (targetWeight_nonneg d f) original_order_bounds
    (fun r i j => by simpa only [Nat.mul_assoc] using card_fiber_le d r i j)
  rwa [source_sum_eq, target_sum_eq] at h

end Appendix.A5ReverseSum

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

omit [Finite E] [Finite F] in
theorem hybridProjector_zero_pair (f : (E →ₗ[F2] F) → ℝ) :
    hybridProjector (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f = f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp [hybridProjector, linearCoeff_spectralProjector, LinearIdentities.Hybrid]

theorem energy_sq_le_hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, f M ^ 2) ^ 2 ≤ hybridMomentSum d f := by
  have hzero : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    have he : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) + Module.finrank F2 F =
        Module.finrank F2 F := by simpa using hq
    omega
  let s0 : HybridIndex (E := E) (F := F) d := ⟨(⊥, ⊤), by
    change Module.finrank F2 (⊥ : Submodule F2 E) +
      Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) ≤ d
    rw [hzero]
    simp⟩
  have havg := hybridDerivative_energy_average
    (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f
  rw [hybridProjector_zero_pair] at havg
  have hcs : (𝔼 T, 𝔼 N,
      hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 ≤
      𝔼 T, (𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 := by
    simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun T => 𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2)
      (fun _ => (1 : ℝ))
  rw [havg] at hcs
  apply hcs.trans
  change (𝔼 T, (𝔼 N, hybridDerivative s0.val.1 s0.val.2 T f N ^ 2) ^ 2) ≤ _
  unfold hybridMomentSum
  let H : HybridIndex (E := E) (F := F) d → ℝ :=
    fun s => 𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)^2
  change H s0 ≤ ∑ s, H s
  exact Finset.single_le_sum (f := H) (s := Finset.univ)
    (fun s _ => Finset.expect_nonneg (fun T _ =>
      sq_nonneg (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)))
    (Finset.mem_univ s0)

theorem degree_zero_bound (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost 0 f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * 0 * 0) * hybridMomentSum 0 f := by
  rw [DegreeZero.fourth_moment_eq_energy_sq f (fun Y hY => hf Y hY)]
  simpa using energy_sq_le_hybridMomentSum 0 f

/-- Proposition A.5 on every finite-dimensional binary linear-map space,
proved by strong induction with all changing domains in the motive. -/
theorem boundAtDegree (d : ℕ) : BoundAtDegree.{u, v} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E F instE instME instF instMF instDE instDF instFiniteE instFiniteF
      instHom instDual f hf
    by_cases hz : d = 0
    · subst d
      exact degree_zero_bound f hf
    · have hd : 1 ≤ d := by omega
      have hreverse :
          (∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
            (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
              24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
              A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
                (d - A13Index.size p.val) f) ≤
            (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f := by
        simpa only [dampedHybridMoment, dampedMapMoment, frequencyRank, one_div] using
          A5ReverseSum.weighted_descendantSum_le d hd f
      have hbounded := (boundedTripleSum_le_descendants d ih f hf).trans hreverse
      have hA13 := A13Reduction.degree_reduction_truncated f d hf
      apply recurrence_closure d hd f hf
      simpa only [pow_two, Nat.mul_assoc] using
        hA13.trans (add_le_add le_rfl hbounded)

theorem derivative_inequality_oai (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d f := by
  simpa only [pow_two, Nat.mul_assoc] using boundAtDegree.{u, v} d f hf

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality_oai.{u, v} := @OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality_oai.{u, v}
