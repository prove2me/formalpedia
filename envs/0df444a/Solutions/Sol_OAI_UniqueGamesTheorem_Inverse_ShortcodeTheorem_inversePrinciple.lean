-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:46:54.472513+00:00
-- url     : https://prove2.me/submissions/3bdf2ac0-e4b1-45dd-9350-aa92d67e9772

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U009
import Theorems.Thm_OAI_UniqueGamesTheorem_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
import Theorems.Thm_OAI_UniqueGamesTheorem_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

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
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_SubspaceCountingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem span_generators (S : Submodule K V) (k : ℕ) (h : finrank K S = k) :
    Submodule.span K (Set.range (generators S k h)) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  change Submodule.span K (Set.range (S.subtype ∘ b)) = S
  rw [Set.range_comp, Submodule.span_image, b.span_eq]
  simp

/-- A k-subspace is determined by a chosen ordered k-tuple of spanning vectors. -/
theorem card_subspaces_rank_le [Finite V] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤ Nat.card V ^ k := by
  classical
  let code : {S : Submodule K V // finrank K S = k} → (Fin k → V) :=
    fun S => generators S.1 k S.2
  have hinj : Function.Injective code := by
    intro S T h
    apply Subtype.ext
    calc
      S.1 = Submodule.span K (Set.range (code S)) := (span_generators S.1 k S.2).symm
      _ = Submodule.span K (Set.range (code T)) :=
        congrArg (fun f : Fin k → V => Submodule.span K (Set.range f)) h
      _ = T.1 := span_generators T.1 k T.2
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hinj

/-- General finite-field form of the image-choice estimate in A.4. -/
theorem card_subspaces_rank_le_field_power [Finite K] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤
      Nat.card K ^ (finrank K V * k) := by
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  have h := card_subspaces_rank_le (K := K) (V := V) k
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_mul] at h

/-- Binary specialization: the ambient dimension is the dimension of Y's image,
not the potentially much larger original vector space. -/
theorem card_binary_subspaces_rank_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (d k : ℕ) (hd : finrank (ZMod 2) V ≤ d) :
    Nat.card {S : Submodule (ZMod 2) V // finrank (ZMod 2) S = k} ≤
      2 ^ (d * k) := by
  calc
    _ ≤ Nat.card (ZMod 2) ^ (finrank (ZMod 2) V * k) :=
      card_subspaces_rank_le_field_power (K := ZMod 2) (V := V) k
    _ = 2 ^ (finrank (ZMod 2) V * k) := by simp
    _ ≤ 2 ^ (d * k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k hd)

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixRestrictions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixRestrictions

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

theorem embed_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) : Function.Injective (embed W C') := by
  intro A B h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : (E →ₗ[F2] C) => f y) h

theorem embed_vanishes (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    W ≤ LinearMap.ker (embed W C' A) := by
  intro x hx
  change (A (W.mkQ x) : C) = 0
  have hzero : W.mkQ x = 0 := by simpa using hx
  simp [hzero]

theorem embed_range (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    LinearMap.range (embed W C' A) ≤ C' := by
  rintro x ⟨y, rfl⟩
  exact (A (W.mkQ y)).property

/-- These are exactly the maps vanishing on `W` with image in `C'`. -/
theorem exists_embed_iff (W : Submodule F2 E)
    (C' : Submodule F2 C) (B : (E →ₗ[F2] C)) :
    (∃ A : Parameter W C', embed W C' A = B) ↔
      W ≤ LinearMap.ker B ∧ LinearMap.range B ≤ C' := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨embed_vanishes W C' A, embed_range W C' A⟩
  · rintro ⟨hW, hC⟩
    let B' : E →ₗ[F2] C' :=
      B.codRestrict C' (fun x => hC ⟨x, rfl⟩)
    have hker : W ≤ LinearMap.ker B' := by
      intro x hx
      apply Subtype.ext
      exact hW hx
    refine ⟨W.liftQ B' hker, ?_⟩
    apply LinearMap.ext
    intro x
    rfl

end UniqueGamesTheorem.Fourier.MatrixRestrictions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_RestrictionTransport
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end General

end UniqueGamesTheorem.Appendix.NaturalTransport

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_AdaptivePathsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceFibersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace UniqueGamesTheorem.Decoder.PositiveMultiplier

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

omit [FiniteDimensional F2 K] in
theorem subspaceLaw_sum (ι : K →ₗ[F2] V) (f : V → ℝ) :
    (∑ v, subspaceLaw ι v * f v) = (Fintype.card K : ℝ)⁻¹ * ∑ k, f (ι k) := by
  classical
  unfold subspaceLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact (Finset.mul_sum _ _ _).symm

theorem subspaceLaw_eigenvalue (ι : K →ₗ[F2] V) (S : V →ₗ[F2] E) :
    linearNoiseEigenvalue (subspaceLaw ι) S =
      ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ := by
  classical
  let k := (Finset.univ.filter fun x : K => S (ι x) = 0).card
  have hs : (∑ x : K, if S (ι x) = 0 then (1 : ℝ) else 0) = (k : ℝ) := by
    rw [← Finset.sum_filter]
    simp [k]
  have hc : (k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
      (Fintype.card K : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (UniqueGamesTheorem.Gadget.LinearKernelCount.zero_event_finset_count_mul_pow_rank (S.comp ι))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, LinearMap.comp_apply] using h
  have hn : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold linearNoiseEigenvalue
  rw [subspaceLaw_sum, hs]
  apply mul_right_cancel₀ hp
  calc
    ((Fintype.card K : ℝ)⁻¹ * (k : ℝ)) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range =
        (Fintype.card K : ℝ)⁻¹ * ((k : ℝ) * (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range) :=
      mul_assoc _ _ _
    _ = (Fintype.card K : ℝ)⁻¹ * (Fintype.card K : ℝ) := by rw [hc]
    _ = 1 := inv_mul_cancel₀ hn
    _ = ((2 : ℝ) ^ Module.finrank F2 (S.comp ι).range)⁻¹ *
        (2 : ℝ) ^ Module.finrank F2 (S.comp ι).range := (inv_mul_cancel₀ hp).symm

end UniformSubspace

end UniqueGamesTheorem.Decoder.PositiveMultiplier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_EqualityFiber
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace UniqueGamesTheorem.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem sum_fiberMass (p : X → ℝ) (f : X → Y) :
    ∑ y, fiberMass p f y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
theorem fiberMass_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → Y) (y : Y) : 0 ≤ fiberMass p f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiberFlow_nonneg (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x x', 0 ≤ k x x')
    (f : X → Y) (y : Y) : 0 ≤ fiberFlow p k f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hp x)
  apply Finset.sum_nonneg
  intro x' _
  apply mul_nonneg (hk x x')
  split <;> norm_num

omit [Fintype Y] in
theorem fiberFlow_le_mass (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) (y : Y) : fiberFlow p k f y ≤ fiberMass p f y := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases h : f x = y
  · simp only [h, true_and, ite_true, if_true]
    have hinner : (∑ x', k x x' * if f x' = y then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ x', k x x' := by
          apply Finset.sum_le_sum
          intro x' _
          split <;> simp [(hk x).1 x']
        _ = 1 := (hk x).2
    simpa using mul_le_mul_of_nonneg_left hinner (hp x)
  · simp [h]

private theorem sum_sameFiber_indicator (a b : Y) :
    (∑ y, if a = y ∧ b = y then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    have h' : ¬ (a = y ∧ b = y) := fun hy => h (hy.1.trans hy.2.symm)
    simp [h']

theorem sum_fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) :
    ∑ y, fiberFlow p k f y = equalityAcceptance p k f := by
  classical
  unfold fiberFlow equalityAcceptance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x' _
  rw [← Finset.mul_sum, sum_sameFiber_indicator]

/-- A probability-weighted average at least `η` contains a positive-weight
fiber whose unnormalized flow is at least `η` times its mass. -/
theorem exists_positive_mass_le_flow (mass flow : Y → ℝ)
    (hmass : IsProbability mass) (_hflow : ∀ y, 0 ≤ flow y)
    (hzero : ∀ y, mass y = 0 → flow y = 0)
    {η : ℝ} (haccept : η ≤ ∑ y, flow y) :
    ∃ y, 0 < mass y ∧ η * mass y ≤ flow y := by
  classical
  by_contra hnone
  have hless (y : Y) (hy : 0 < mass y) : flow y < η * mass y := by
    apply lt_of_not_ge
    intro h
    exact hnone ⟨y, hy, h⟩
  have hle (y : Y) : flow y ≤ η * mass y := by
    rcases eq_or_lt_of_le (hmass.1 y) with hz | hz
    · simp [← hz, hzero y hz.symm]
    · exact (hless y hz).le
  have hex : ∃ y, 0 < mass y := by
    by_contra hn
    have hall (y : Y) : mass y = 0 := le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
      (hmass.1 y)
    have := hmass.2
    simp [hall] at this
  obtain ⟨y, hy⟩ := hex
  have hstrict : (∑ y, flow y) < ∑ y, η * mass y := by
    exact Finset.sum_lt_sum (fun y _ => hle y) ⟨y, Finset.mem_univ y, hless y hy⟩
  rw [← Finset.mul_sum, hmass.2, mul_one] at hstrict
  exact (not_lt_of_ge haccept) hstrict

/-- Equality acceptance supplies a nonempty output fiber with the claimed
retention.  The kernel is the actual sampling kernel; no conditioned sampling
law is silently substituted. -/
theorem exists_fiber_retention (p : X → ℝ) (k : X → X → ℝ)
    (hp : IsProbability p) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) {η : ℝ} (haccept : η ≤ equalityAcceptance p k f) :
    ∃ y, 0 < fiberMass p f y ∧ η ≤ fiberFlow p k f y / fiberMass p f y := by
  have hmass : IsProbability (fiberMass p f) :=
    ⟨fiberMass_nonneg p hp.1 f, (sum_fiberMass p f).trans hp.2⟩
  have hflow := fiberFlow_nonneg p k hp.1 (fun x => (hk x).1) f
  have hzero (y : Y) (hy : fiberMass p f y = 0) : fiberFlow p k f y = 0 := by
    apply le_antisymm _ (hflow y)
    simpa [hy] using fiberFlow_le_mass p k hp.1 hk f y
  obtain ⟨y, hy, hret⟩ := exists_positive_mass_le_flow (fiberMass p f)
    (fiberFlow p k f) hmass hflow hzero (by simpa [sum_fiberFlow] using haccept)
  exact ⟨y, hy, (le_div_iff₀ hy).2 hret⟩

/-- Removing a self-loop mass `p₀ ≤ η/2` leaves retention at least `η/2`.
This is the precise algebra needed when one or both rank-one factors may be
zero in the unconditioned test. -/
theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

end
end UniqueGamesTheorem.Inverse.EqualityFiber

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionComplementLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Complements adapted to an affine restriction. The prescribed directions are
contained in a small summand, and the complementary directions are mapped into
the prescribed target subspace. This is ordinary finite-dimensional geometry;
no Fourier inequality or pseudorandomness hypothesis is used.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionComplement

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F]

/-- Enlarge prescribed directions by at most the rank of `L`, leaving a
complement on which `L` vanishes. -/
theorem exists_bounded_complement_of_linearMap
    (V1 : Submodule K E) (L : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker L ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (LinearMap.range L) := by
  obtain ⟨D, hD⟩ := (LinearMap.ker L).exists_isCompl
  let U : Submodule K E := V1 ⊔ D
  have hcover : Codisjoint (LinearMap.ker L) U :=
    hD.codisjoint.mono_right le_sup_right
  obtain ⟨E0, hE0, hcompl⟩ := hcover.exists_isCompl
  refine ⟨U, E0, le_sup_left, hE0, hcompl.symm, ?_⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl hD
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hDdim : Module.finrank K D = Module.finrank K (LinearMap.range L) := by
    omega
  exact (Submodule.finrank_add_le_finrank_add_finrank V1 D).trans
    (by rw [hDdim])

/-- Split the domain while preserving `V1` and mapping all complementary
directions into `W`. The extra dimension is at most the codimension of `W`. -/
theorem exists_bounded_complement [FiniteDimensional K F]
    (V1 : Submodule K E) (W : Submodule K F) (T : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker (W.mkQ.comp T) ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (F ⧸ W) := by
  obtain ⟨U, E0, hV1, hE0, hcompl, hdim⟩ :=
    exists_bounded_complement_of_linearMap V1 (W.mkQ.comp T)
  refine ⟨U, E0, hV1, hE0, hcompl, hdim.trans ?_⟩
  exact Nat.add_le_add_left (Submodule.finrank_le (LinearMap.range (W.mkQ.comp T))) _

end UniqueGamesTheorem.Inverse.KMSAffineRestrictionComplement

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridCoordinatesConditions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open UniqueGamesTheorem.Appendix

private theorem psi_split {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (b : B) (c : C) :
    p.psi (b, c) = z b + p.psi (0, c) := by
  have hleft : p.psi (b, 0) = z b :=
    congrArg (fun L : B →ₗ[R] W => L b) p.psi_left
  calc
    p.psi (b, c) = p.psi ((b, 0) + (0, c)) := by simp
    _ = p.psi (b, 0) + p.psi (0, c) := p.psi.map_add _ _
    _ = z b + p.psi (0, c) := by rw [hleft]

/-- The genuine hybrid selector is exactly the two independent coordinate
conditions. In particular the full-rank coordinate condition does not
depend on the chosen injective map into the complementary target. -/
theorem hybrid_assemble_iff {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hz : Function.Surjective z) :
    LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl R A (W × D)))
        (LinearMap.range (LinearMap.inl R B C)) ↔
      Function.Injective p.v ∧
        Function.Surjective (p.alpha.prod (p.psi.prod (LinearMap.snd R B C))) := by
  constructor
  · intro h
    have hzero : ∀ c : C, p.v c = 0 → c = 0 := by
      intro c hc
      obtain ⟨b, hb⟩ := hz (-p.psi (0, c))
      have hpsi : p.psi (b, c) = 0 := by
        rw [psi_split, hb, neg_add_cancel]
      have hmem : (b, c) ∈ LinearMap.range (LinearMap.inl R B C) := by
        apply h.2
        change assemble p (b, c) ∈ LinearMap.range (LinearMap.inl R A (W × D))
        refine ⟨p.alpha (b, c), ?_⟩
        change (p.alpha (b, c), (0, 0)) = (p.alpha (b, c), p.psi (b, c), p.v c)
        rw [hpsi, hc]
      obtain ⟨b', hb'⟩ := hmem
      exact (congrArg (fun x : B × C => x.2) hb').symm
    refine ⟨?_, ?_⟩
    · intro c d hcd
      apply sub_eq_zero.mp
      apply hzero
      rw [map_sub, hcd, sub_self]
    · rintro ⟨a, w, c⟩
      obtain ⟨b, hb⟩ := hz (w - p.psi (0, c))
      have hpsi : p.psi (b, c) = w := by
        rw [psi_split, hb, sub_add_cancel]
      have hmem : (a - p.alpha (b, c), (0, 0)) ∈ LinearMap.range (assemble p) := by
        apply h.1
        exact ⟨a - p.alpha (b, c), rfl⟩
      obtain ⟨x, hx⟩ := hmem
      have hxa : p.alpha x = a - p.alpha (b, c) :=
        congrArg (fun y : A × (W × D) => y.1) hx
      have hxw : p.psi x = 0 :=
        congrArg (fun y : A × (W × D) => y.2.1) hx
      have hxd : p.v x.2 = 0 :=
        congrArg (fun y : A × (W × D) => y.2.2) hx
      have hxc : x.2 = 0 := hzero _ hxd
      refine ⟨x + (b, c), ?_⟩
      change (p.alpha (x + (b, c)), p.psi (x + (b, c)), (x + (b, c)).2) =
        (a, w, c)
      apply Prod.ext
      · rw [map_add, hxa, sub_add_cancel]
      · apply Prod.ext
        · change p.psi (x + (b, c)) = w
          rw [map_add, hxw, zero_add, hpsi]
        · change x.2 + c = c
          rw [hxc, zero_add]
  · rintro ⟨hv, htheta⟩
    constructor
    · rintro y ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := htheta (a, 0, 0)
      change (p.alpha x, p.psi x, x.2) = (a, 0, 0) at hx
      have hxa : p.alpha x = a := congrArg (fun y : A × (W × C) => y.1) hx
      have hxw : p.psi x = 0 := congrArg (fun y : A × (W × C) => y.2.1) hx
      have hxc : x.2 = 0 := congrArg (fun y : A × (W × C) => y.2.2) hx
      refine ⟨x, ?_⟩
      change (p.alpha x, p.psi x, p.v x.2) = (a, 0, 0)
      rw [hxa, hxw, hxc, map_zero]
    · intro x hx
      change assemble p x ∈ LinearMap.range (LinearMap.inl R A (W × D)) at hx
      obtain ⟨a, ha⟩ := hx
      have hxd : p.v x.2 = 0 :=
        (congrArg (fun y : A × (W × D) => y.2.2) ha).symm
      have hxc : x.2 = 0 := hv (by simpa only [map_zero] using hxd)
      exact ⟨x.1, Prod.ext rfl hxc.symm⟩

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridCoordinatesRankLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

theorem embedLast_injective (v : C →ₗ[R] D) (hv : Function.Injective v) :
    Function.Injective (embedLast (A := A) (W := W) v) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun u : A × (W × D) => u.1) h
  · apply Prod.ext
    · exact congrArg (fun u : A × (W × D) => u.2.1) h
    · apply hv
      exact congrArg (fun u : A × (W × D) => u.2.2) h

theorem assemble_eq_embedLast_comp {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    assemble p = (embedLast p.v).comp (fullCoordinates p) := by
  apply LinearMap.ext
  intro x
  rfl

theorem range_assemble_of_fullCoordinates_surjective {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hp : Function.Surjective (fullCoordinates p)) :
    (assemble p).range = (embedLast (A := A) (W := W) p.v).range := by
  rw [assemble_eq_embedLast_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hp, Submodule.map_top]

theorem finrank_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) (hp : Function.Surjective (fullCoordinates p)) :
    Module.finrank R (assemble p).range = Module.finrank R (A × (W × C)) := by
  rw [range_assemble_of_fullCoordinates_surjective p hp]
  exact LinearMap.finrank_range_of_inj (embedLast_injective p.v hv)

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

section

/-!
# Cauchy--Schwarz for the hybrid coefficient fibers

The complementary-vector phase sum contributes the square of its number
of terms. Merging extensions with the same restriction contributes their
largest fiber size. Both factors come from finite Cauchy--Schwarz; summing
the disjoint fibers preserves the unnormalized coefficient energy.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical

/-- Unit-bounded squared phases cost at most the number of summands in the
finite Cauchy--Schwarz inequality. -/
theorem phase_weighted_sum_sq_le {Ψ : Type*} (s : Finset Ψ)
    (b H : Ψ → ℝ) (hb : ∀ ψ ∈ s, b ψ ^ 2 ≤ 1) :
    (∑ ψ ∈ s, b ψ * H ψ) ^ 2 ≤ (s.card : ℝ) * ∑ ψ ∈ s, H ψ ^ 2 := by
  have hphase : (∑ ψ ∈ s, b ψ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _ψ ∈ s, (1 : ℝ) := Finset.sum_le_sum hb
      _ = _ := by simp
  exact (Finset.sum_mul_sq_le_sq_mul_sq s b H).trans
    (mul_le_mul_of_nonneg_right hphase (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))

/-- A finite sum of phases has square at most the squared cardinality.
The statement also covers an empty indexing type. -/
theorem phase_sum_sq_le_card_sq {V : Type*} [Fintype V]
    (a : V → ℝ) (ha : ∀ v, a v ^ 2 ≤ 1) :
    (∑ v, a v) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := phase_weighted_sum_sq_le Finset.univ a (fun _ => (1 : ℝ))
    (fun v _ => ha v)
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, pow_two] using h

/-- Summing the Cauchy--Schwarz bounds over the disjoint restriction fibers
loses only the largest fiber cardinality. -/
theorem sum_fiber_phase_sq_le {Ψ Z : Type*} [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2) ≤
      (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have hlocal (z : Z) :
      (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 ≤
        (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 := by
    have hc : ((Finset.univ.filter (fun ψ => r ψ = z)).card : ℝ) ≤
        (maxFiber : ℝ) := Nat.cast_le.mpr (hcard z)
    exact (phase_weighted_sum_sq_le (Finset.univ.filter (fun ψ => r ψ = z))
      b H (fun ψ _ => hb ψ)).trans
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))
  calc
    _ ≤ ∑ z, (maxFiber : ℝ) * ∑ ψ with r ψ = z, H ψ ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
      rw [← Finset.mul_sum]
      exact congrArg (fun t : ℝ => (maxFiber : ℝ) * t)
        (Finset.sum_fiberwise Finset.univ r (fun ψ => H ψ ^ 2))

/-- The hybrid coefficient factorization has energy bounded by the squared
number of complementary choices times the extension-fiber size and the
original mixed coefficient energy. No phase cancellation is assumed. -/
theorem sum_fiber_product_sq_le {V Ψ Z : Type*}
    [Fintype V] [Fintype Ψ] [Fintype Z]
    (r : Ψ → Z) (a : V → ℝ) (b H : Ψ → ℝ) (maxFiber : ℕ)
    (ha : ∀ v, a v ^ 2 ≤ 1) (hb : ∀ ψ, b ψ ^ 2 ≤ 1)
    (hcard : ∀ z, (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ maxFiber) :
    (∑ z, ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2) ≤
      (Fintype.card V : ℝ) ^ 2 * (maxFiber : ℝ) * ∑ ψ, H ψ ^ 2 := by
  have haSum := phase_sum_sq_le_card_sq a ha
  have hmerged := sum_fiber_phase_sq_le r b H maxFiber hb hcard
  calc
    _ = (∑ v, a v) ^ 2 * ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ (Fintype.card V : ℝ) ^ 2 *
        ∑ z, (∑ ψ with r ψ = z, b ψ * H ψ) ^ 2 :=
      mul_le_mul_of_nonneg_right haSum (Finset.sum_nonneg (fun z _ => sq_nonneg _))
    _ ≤ (Fintype.card V : ℝ) ^ 2 * ((maxFiber : ℝ) * ∑ ψ, H ψ ^ 2) :=
      mul_le_mul_of_nonneg_left hmerged (sq_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

section ImageCoordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Each fixed-image frequency has exactly the block form used by the
compressed Hybrid-coordinate parametrization. -/
theorem imageCoordinates_frequency {X : Type*} [AddCommGroup X] [Module K X]
    (W D : Submodule K V) (h : IsCompl W D) (z : X →ₗ[K] W) :
    (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) =
      z.prod (0 : X →ₗ[K] D) := by
  apply LinearMap.ext
  intro x
  exact imageCoordinates_subtype W D h (z x)

/-- A complement contributes exactly the remaining ambient dimension. -/
theorem imageCoordinates_finrank [FiniteDimensional K V]
    (W D : Submodule K V) (h : IsCompl W D) :
    Module.finrank K W + Module.finrank K D = Module.finrank K V := by
  simpa only [Module.finrank_prod] using (Submodule.prodEquivOfIsCompl W D h).finrank_eq

end ImageCoordinates
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
/-- Finset conditioning and uniform sampling from its membership subtype are
the same normalized finite sum, including the empty event. -/
theorem expect_coe_eq (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x : s, f x.val) = s.expect f := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, Finset.sum_coe_sort]

omit [Fintype Ω] in
theorem expect_unit_interval (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ s.expect f ∧ s.expect f ≤ 1 := by
  refine ⟨Finset.expect_nonneg (fun x _ => hf0 x), ?_⟩
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · exact Finset.expect_le hs (fun x _ => hf1 x)

/-- The weighted conditional expectation is the unnormalized sum divided by
the ambient cardinality, also for an empty conditioning event. -/
theorem mass_mul_expect (s : Finset Ω) (f : Ω → ℝ) :
    (s.card : ℝ) / Fintype.card Ω * s.expect f =
      (∑ x ∈ s, f x) / Fintype.card Ω := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [Finset.expect_eq_sum_div_card]
    have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
    by_cases hN : (Fintype.card Ω : ℝ) = 0
    · simp [hN]
    · field_simp

/-- Exact two-event total expectation, with the same zero convention on both
conditional expectations as mathlib's finite expectation. -/
theorem expect_partition (s : Finset Ω) (f : Ω → ℝ) :
    (𝔼 x, f x) =
      (s.card : ℝ) / Fintype.card Ω * s.expect f +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω *
        (Finset.univ \ s).expect f := by
  rw [mass_mul_expect, mass_mul_expect, ← add_div, Fintype.expect_eq_sum_div_card]
  congr 1
  exact (Finset.sum_sdiff (Finset.subset_univ s)).symm.trans (add_comm _ _)

/-- Conditioning a bounded function changes its expectation by at most the
discarded probability mass. No independence assumption is used here. -/
theorem abs_expect_sub_restrict_le [Nonempty Ω] (s : Finset Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(𝔼 x, f x) - s.expect f| ≤
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by
  have hB := expect_unit_interval s f hf0 hf1
  have hC := expect_unit_interval (Finset.univ \ s) f hf0 hf1
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (s.card : ℝ) / Fintype.card Ω +
      ((Finset.univ \ s).card : ℝ) / Fintype.card Ω = 1 := by
    rw [← add_div]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcast : ((Finset.univ \ s).card : ℝ) + (s.card : ℝ) =
        Fintype.card Ω := by exact_mod_cast hc.trans (Finset.card_univ)
    rw [add_comm, hcast, div_self hN]
  have hq : 0 ≤ ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by positivity
  have hp : (s.card : ℝ) / Fintype.card Ω =
      1 - ((Finset.univ \ s).card : ℝ) / Fintype.card Ω := by linarith
  rw [expect_partition]
  rw [hp]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hB.2)]
  · nlinarith [mul_nonneg hq hB.1, mul_nonneg hq hC.1,
      mul_nonneg hq (sub_nonneg.mpr hC.2)]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- Equal fiber cardinality follows from the explicit completion equivalence. -/
theorem restrictedCompletionCard_eq
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    Nat.card (RestrictedCompletion (t := t) Q W L) =
      Nat.card (RestrictedCompletion (t := t) Q W M) :=
  Nat.card_congr (restrictedCompletionEquiv x y)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

/-- Exact uniform expectation in any presentation of the actual restriction. -/
theorem expect_presentation [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L))) =
      𝔼 A : Parameter L.ker J.range, restrict f L.ker J.range T A := by
  apply Fintype.expect_equiv (parameterEquiv L hL J hJ).toEquiv
  intro X
  exact congrArg f (translate_parameterEquiv L hL J hJ T X).symm

/-- In particular, the normalized squared restriction norms coincide. -/
theorem expect_presentation_sq [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) =
      𝔼 A : Parameter L.ker J.range, (restrict f L.ker J.range T A) ^ 2 :=
  expect_presentation L hL J hJ T (fun X => f X ^ 2)

/-- The intrinsic restriction order is exactly the dimensions lost by the
surjective input and injective output presentations. -/
theorem order_add_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    order L.ker J.range + Module.finrank F2 D + Module.finrank F2 C =
      Module.finrank F2 E + Module.finrank F2 F := by
  have hD := L.ker.finrank_quotient_add_finrank
  have hD' := (L.quotKerEquivOfSurjective hL).finrank_eq
  have hF := J.range.finrank_quotient_add_finrank
  have hC := (LinearEquiv.ofInjective J hJ).finrank_eq
  unfold order
  omega

/-- The sum-of-dimensions budget used in the fourth-moment statement implies
the actual quotient/subspace restriction budget, without truncated subtraction. -/
theorem order_le_of_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) (r : ℕ)
    (h : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r) :
    order L.ker J.range ≤ r := by
  have hdim := order_add_dimensions L hL J hJ
  omega

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

end

section

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Exact product uniform sampling on the original quotient-map parameters. -/
theorem expect_join [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (f : Parameter D W → ℝ) :
    (𝔼 A : Parameter D W, f A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (join D U E₀ W hDU hc B C) := by
  calc
    _ = 𝔼 P : Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W),
        f (join D U E₀ W hDU hc P.1 P.2) :=
      Fintype.expect_equiv (splitEquiv D U E₀ W hDU hc).toEquiv _ _
        (fun A => congrArg f (join_split D U E₀ W hDU hc A).symm)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]

/-- The same exact split for the observable on the actual affine restriction. -/
theorem expect_restrict [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (T : E →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter D W, restrict f D W T A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (translate D W T (join D U E₀ W hDU hc B C)) :=
  expect_join D U E₀ W hDU hc (restrict f D W T)

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

end

section

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier infrastructure, not the legacy rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem synthesis_coeff (f : (E →ₗ[F2] F) → ℝ) : synthesis (linearCoeff f) = f := by
  funext X
  simpa only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    linear_fourier_inversion f X

theorem eq_of_coeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ T, linearCoeff f T = linearCoeff g T) : f = g := by
  rw [← synthesis_coeff f, ← synthesis_coeff g]
  exact congrArg synthesis (funext h)

/-- Exact squared norm, used for every restricted KMS component. -/
theorem synthesis_energy (a : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X ^ 2) = ∑ T, a T ^ 2 := by
  rw [← linear_parseval]
  simp

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

theorem component_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) = ∑ T with P T, linearCoeff f T ^ 2 := by
  rw [component, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem component_inner_self (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * f X) = 𝔼 X, component P f X ^ 2 := by
  rw [← linear_parseval_inner, component_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_component]
  split_ifs <;> simp [pow_two]

theorem rankComponent_energy (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankComponent i f X ^ 2) =
      ∑ T with Module.finrank F2 T.range = i, linearCoeff f T ^ 2 := by
  unfold rankComponent
  rw [component_energy]
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro T _
    rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

noncomputable section
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

section Product

variable {H U V : Type*}
  [AddCommGroup H] [Module F2 H]
  [AddCommGroup U] [Module F2 U]
  [AddCommGroup V] [Module F2 V]

/-- Each frequency block pairs with the corresponding restriction of the
primal map. The trace is taken on the common codomain `H`. -/
theorem tracePair_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTracePair X (S.prod T) =
      linearTracePair (X.comp (LinearMap.inl F2 U V)) S +
      linearTracePair (X.comp (LinearMap.inr F2 U V)) T := by
  have hc : X.comp (S.prod T) =
      (X.comp (LinearMap.inl F2 U V)).comp S +
        (X.comp (LinearMap.inr F2 U V)).comp T := by
    apply LinearMap.ext
    intro h
    change X (S h, T h) = X (S h, 0) + X (0, T h)
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      X.map_add (S h, 0) (0, T h)
  simp only [linearTracePair, hc, map_add]

/-- Exact complex-valued phase splitting into two frequency blocks. -/
theorem character_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTraceCharacter (S.prod T) X =
      linearTraceCharacter S (X.comp (LinearMap.inl F2 U V)) *
      linearTraceCharacter T (X.comp (LinearMap.inr F2 U V)) := by
  simp only [linearTraceCharacter_apply, tracePair_prod, binarySign_add]

/-- The real phases multiply because every binary trace character is real. -/
theorem character_prod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) X).re =
      (linearTraceCharacter S (X.comp (LinearMap.inl F2 U V))).re *
      (linearTraceCharacter T (X.comp (LinearMap.inr F2 U V))).re := by
  rw [character_prod, Complex.mul_re]
  simp [linearTraceCharacter_apply]

/-- Splitting a primal map and its dual frequency introduces no cardinal
factor: both traces remain on the common space `H`. -/
theorem character_prod_coprod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (a : U →ₗ[F2] H) (X : V →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) (a.coprod X)).re =
      (linearTraceCharacter S a).re * (linearTraceCharacter T X).re := by
  simpa only [LinearMap.coprod_inl, LinearMap.coprod_inr] using
    character_prod_re S T (a.coprod X)

end Product

section AdaptedCoordinates

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

/-- The real phase factorization used in the coefficient fiber sum. -/
theorem character_assemble_re {z : B →ₗ[F2] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) :
    (linearTraceCharacter (assemble p) X).re =
      (linearTraceCharacter p.alpha (X.comp (LinearMap.inl F2 A (W × D)))).re *
        ((linearTraceCharacter p.psi
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D))).re *
        (linearTraceCharacter (p.v.comp (LinearMap.snd F2 B C))
          ((X.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D))).re) := by
  simp only [assemble, character_prod_re]

end AdaptedCoordinates
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

end

section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives

section General

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The coefficient of an actual Hybrid derivative is the translated sum over
the actual Hybrid selector and quotient-compression fiber. -/
theorem linearCoeff_hybridDerivative
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ)
    (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (hybridDerivative A B T f) Z =
      ∑ S : F →ₗ[F2] E,
        if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
        then linearCoeff f S * (linearTraceCharacter S T).re else 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro S _
  simp only [hybridProjector, linearCoeff_spectralProjector]
  by_cases hH : LinearIdentities.Hybrid S A B <;>
    by_cases hC : Restriction.compressFrequency A B S = Z <;> simp [hH, hC]

end General

section ProductEnergy

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- Equality of actual compressed frequencies is exactly equality of blocks. -/
theorem compressFrequency_eq_iff_product
    (S : (B × C) →ₗ[F2] (A × U))
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Restriction.compressFrequency (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S = Z ↔
    (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) =
      productFrequencyEquiv Z := by
  constructor
  · intro h
    rw [← productFrequencyEquiv_compressFrequency S, h]
  · intro h
    apply productFrequencyEquiv.injective
    rw [productFrequencyEquiv_compressFrequency, h]

end ProductEnergy
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyTransport
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']

private theorem mem_map_equiv_iff (a : E ≃ₗ[F2] E')
    (A : Submodule F2 E) (x : E) :
    a x ∈ A.map a.toLinearMap ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp h
    exact (a.injective heq) ▸ hy
  · intro h
    exact Submodule.mem_map.mpr ⟨x, h, rfl⟩

/-- The two clauses of the actual Hybrid selector are coordinate invariant. -/
theorem hybrid_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (S : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F) :
    LinearIdentities.Hybrid (LinearEquiv.arrowCongr b a S)
      (A.map a.toLinearMap) (B.map b.toLinearMap) ↔
      LinearIdentities.Hybrid S A B := by
  constructor
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := hr ((mem_map_equiv_iff a A x).mpr hx)
      refine ⟨b.symm y, a.injective hy⟩
    · intro y hy
      apply (mem_map_equiv_iff b B y).mp
      apply hk
      change (LinearEquiv.arrowCongr b a S) (b y) ∈ A.map a.toLinearMap
      simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
        using (mem_map_equiv_iff a A (S y)).mpr hy
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨z, hz⟩ := hr hy
      refine ⟨b z, ?_⟩
      change a (S (b.symm (b z))) = a y
      rw [b.symm_apply_apply]
      exact congrArg a hz
    · intro y hy
      have hy' : S (b.symm y) ∈ A := (mem_map_equiv_iff a A _).mp hy
      have hm := (mem_map_equiv_iff b B _).mpr (hk hy')
      simpa only [LinearEquiv.apply_symm_apply] using hm

/-- The actual vanishing and range constraints of an affine perturbation
transport to the mapped subspaces. -/
theorem restriction_admissible_arrowCongr
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (A : Submodule F2 E) (B : Submodule F2 F) :
    (A.map a.toLinearMap ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ B.map b.toLinearMap) ↔
      (A ≤ M.ker ∧ M.range ≤ B) := by
  constructor
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      have heq := hk ((mem_map_equiv_iff a A x).mpr hx)
      have heq' : b (M x) = b 0 := by
        simpa only [LinearMap.mem_ker, LinearEquiv.arrowCongr_apply,
          LinearEquiv.symm_apply_apply, map_zero] using heq
      exact b.injective heq'
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff b B _).mp
      apply hr
      exact ⟨a x, by simp only [LinearEquiv.arrowCongr_apply,
        LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      change b (M (a.symm (a y))) = 0
      rw [a.symm_apply_apply, hk hy, map_zero]
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff b B _).mpr
      exact hr ⟨a.symm x, rfl⟩

/-- Transported quotient parameters give exactly the directly transported
affine perturbations; no multiplicity or normalization factor occurs. -/
theorem hybrid_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (A : Submodule F2 E) (B : Submodule F2 F) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B)).range =
      (embedding (A.map a.toLinearMap) (B.map b.toLinearMap)).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  ext M'
  change (∃ N, e (embed A B N) = M') ↔
    (∃ N, embed (A.map a.toLinearMap) (B.map b.toLinearMap) N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff _ _ _).mpr
    apply (restriction_admissible_arrowCongr a b (embed A B N) A B).mpr
    exact (exists_embed_iff A B _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff _ _ _).mp hM'
    have hm : A ≤ M.ker ∧ M.range ≤ B := by
      apply (restriction_admissible_arrowCongr a b M A B).mp
      change A.map a.toLinearMap ≤ (e M).ker ∧
        (e M).range ≤ B.map b.toLinearMap
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr hm
    exact ⟨N, by rw [hN]; exact he⟩

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

/-- The actual Fourier Hybrid projector commutes with coordinate pullback. -/
theorem hybridProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F) :
    hybridProjector A B (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [hybridProjector, linearCoeff_spectralProjector,
    NaturalTransport.linearCoeff_pullback, hybrid_arrowCongr]

/-- The actual pure-rank Fourier component commutes with coordinate pullback. -/
theorem rankComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ) :
    rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankComponent i f (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankComponent, coeff_component,
    NaturalTransport.linearCoeff_pullback, NaturalTransport.rank_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

/-- Exact normalized energy transport, with the actual Hybrid selector,
quotient restriction, and affine translate transported together. -/
theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, Fourier.MatrixRestrictions.translate,
    hybridProjector_pullback, map_add]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B))
    (embedding (A.map a.toLinearMap) (B.map b.toLinearMap))
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective A B))
    (embed_injective _ _) (hybrid_embedding_range a b A B)
    (fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
      (LinearEquiv.arrowCongr a b T + M) ^ 2)

/-- Pure-rank derivative energy is invariant under both coordinate changes. -/
theorem hybridDerivative_rankComponent_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M))) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) (rankComponent i f) N ^ 2 := by
  rw [rankComponent_pullback]
  exact hybridDerivative_energy_pullback a b (rankComponent i f) A B T

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentMixedScalarLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- This identification respects every original vector, including vectors in
the kernel and maps of rank zero. -/
theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

/-- Finite-dimensional image suffices: the ambient codomain and domain may
otherwise be infinite-dimensional. -/
theorem exists_postcomp_equiv_of_ker_eq (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] (hker : S.ker = T.ker) :
    ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (rangeEquivOfKerEq S T hker)
  refine ⟨g, ?_⟩
  ext x
  change g (S x) = T x
  exact (hg ⟨S x, ⟨x, rfl⟩⟩).symm.trans (rangeEquivOfKerEq_apply S T hker x)

end
end UniqueGamesTheorem.Inverse.KMSKernelOrbits

end

section

namespace UniqueGamesTheorem.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem boolean_nonneg {f : X → ℝ} (hf : IsBoolean f) (x : X) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype X] in
theorem boolean_sq {f : X → ℝ} (hf : IsBoolean f) (x : X) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_average_nonneg {f : X → ℝ} (hf : IsBoolean f) : 0 ≤ 𝔼 x, f x :=
  Finset.expect_nonneg fun x _ => boolean_nonneg hf x

theorem boolean_squared_average {f : X → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  exact boolean_sq hf x

/-- Two finite Cauchy–Schwarz steps, with the Boolean support kept explicitly. -/
theorem boolean_fourth_holder {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ) :
    (𝔼 x, g x * f x) ^ 4 ≤ (𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have h₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => g x * f x) f
  have hleft : (𝔼 x, (g x * f x) * f x) = 𝔼 x, g x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = g x * f x ^ 2 := by ring
      _ = _ := by rw [boolean_sq hf]
  have hright : (𝔼 x, (g x * f x) ^ 2) = 𝔼 x, g x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [hleft, hright, boolean_squared_average hf] at h₁
  have h₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => g x ^ 2) f
  have hpow : (𝔼 x, (g x ^ 2) ^ 2) = 𝔼 x, g x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hpow, boolean_squared_average hf] at h₂
  have hδ := boolean_average_nonneg hf
  have hweighted : 0 ≤ 𝔼 x, g x ^ 2 * f x :=
    Finset.expect_nonneg fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x)
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, g x * f x)) h₁
  have hscaled := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The squared norm of an orthogonal component is bounded by the Boolean
function's density. The projection identity is the only needed property. -/
theorem projection_energy_le_density {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ≤ 𝔼 x, f x := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ g f
  rw [← hprojection, boolean_squared_average hf] at h
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ := boolean_average_nonneg hf
  nlinarith

/-- A stronger lower fourth-moment estimate than KMS Lemma 2.14, avoiding
division by the density and remaining valid at density zero. -/
theorem projection_fifth_le_density_fourth_moment {f : X → ℝ} (hf : IsBoolean f)
    (g : X → ℝ) (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x) :
    (𝔼 x, g x ^ 2) ^ 5 ≤ (𝔼 x, f x) ^ 4 * (𝔼 x, g x ^ 4) := by
  have hholder := boolean_fourth_holder hf g
  rw [← hprojection] at hholder
  have hηδ := projection_energy_le_density hf g hprojection
  have hδ := boolean_average_nonneg hf
  have hη : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hηδ (pow_nonneg hη 4)
  have hscale := mul_le_mul_of_nonneg_right hholder hδ
  calc
    _ ≤ (𝔼 x, g x ^ 2) ^ 4 * (𝔼 x, f x) := by nlinarith only [hmul]
    _ ≤ ((𝔼 x, g x ^ 4) * (𝔼 x, f x) ^ 3) * (𝔼 x, f x) := hscale
    _ = _ := by ring

theorem fourth_root_power {ε : ℝ} (hε : 0 ≤ ε) :
    (ε ^ ((1 : ℝ) / 4)) ^ 4 = ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε]
  norm_num

theorem le_of_fourth_power_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  have := pow_lt_pow_left₀ hlt hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) this

end
end UniqueGamesTheorem.Inverse.KMSMomentScalar

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportCoreLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]

theorem imageAmbientEquiv_leftRange (W D : Submodule F2 U) (h : IsCompl W D) :
    (LinearMap.range (LinearMap.inl F2 A (W × D))).map
      (imageAmbientEquiv (A := A) W D h).toLinearMap =
      LinearMap.range (LinearMap.inl F2 A U) := by
  rw [← LinearMap.range_comp]
  congr 1
  apply LinearMap.ext
  intro a
  change (a, (imageCoordinates W D h).symm 0) = (a, 0)
  rw [map_zero]

theorem image_hybrid_iff (W D : Submodule F2 U) (h : IsCompl W D)
    (S : (B × C) →ₗ[F2] (A × (W × D))) :
    LinearIdentities.Hybrid ((imageAmbientEquiv W D h).toLinearMap.comp S)
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) ↔
    LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) := by
  have hh := hybrid_arrowCongr (imageAmbientEquiv (A := A) W D h)
    (LinearEquiv.refl F2 (B × C)) S
    (LinearMap.range (LinearMap.inl F2 A (W × D)))
    (LinearMap.range (LinearMap.inl F2 B C))
  have he : LinearEquiv.arrowCongr (LinearEquiv.refl F2 (B × C))
      (imageAmbientEquiv (A := A) W D h) S =
      (imageAmbientEquiv W D h).toLinearMap.comp S := by
    apply LinearMap.ext
    intro x
    rfl
  rw [imageAmbientEquiv_leftRange, he] at hh
  simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id] using hh

theorem image_compression_eq_iff (W D : Submodule F2 U) (h : IsCompl W D)
    (z : B →ₗ[F2] W) (S : (B × C) →ₗ[F2] (A × (W × D))) :
    (LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C)) =
      W.subtype.comp z ↔ compressBlock S = z.prod (0 : B →ₗ[F2] D) := by
  have hc : (imageCoordinates W D h).toLinearMap.comp
      ((LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C))) =
      compressBlock S := by
    apply LinearMap.ext
    intro b
    change imageCoordinates W D h ((imageCoordinates W D h).symm (S (b, 0)).2) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · intro he
    rw [← hc, he, imageCoordinates_frequency]
  · intro he
    apply LinearMap.ext
    intro b
    apply (imageCoordinates W D h).injective
    have he' : (imageCoordinates W D h).toLinearMap.comp
        ((LinearMap.snd F2 A U).comp
          (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C))) =
        (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) := by
      rw [hc, imageCoordinates_frequency, he]
    exact congrArg (fun L : B →ₗ[F2] (W × D) => L b) he'

theorem image_character (W D : Submodule F2 U) (h : IsCompl W D)
    (S : (B × C) →ₗ[F2] (A × (W × D))) (T : (A × U) →ₗ[F2] (B × C)) :
    linearTraceCharacter ((imageAmbientEquiv W D h).toLinearMap.comp S) T =
      linearTraceCharacter S (imageTranslate W D h T) := by
  simp only [imageTranslate, linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

theorem image_rank_coefficient (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ)
    (S : (B × C) →ₗ[F2] (A × (W × D))) :
    linearCoeff (rankComponent i (imagePullback W D h f)) S =
      linearCoeff (rankComponent i f) ((imageAmbientEquiv W D h).toLinearMap.comp S) := by
  change linearCoeff (rankComponent i (fun X => f
      (LinearEquiv.arrowCongr (imageAmbientEquiv W D h) (LinearEquiv.refl F2 (B × C)) X))) S = _
  rw [rankComponent_pullback, NaturalTransport.linearCoeff_pullback]
  rfl

/-- Exact reindexing of a selected coefficient at a prescribed compressed
image. No rank, surjectivity, or basis-invariance assumption is needed. -/
theorem image_coefficient_sum_transport (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (z : B →ₗ[F2] W) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ) :
    (∑ S : (B × C) →ₗ[F2] (A × U),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = W.subtype.comp z
      then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0) =
    ∑ S : (B × C) →ₗ[F2] (A × (W × D)),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          compressBlock S = z.prod (0 : B →ₗ[F2] D)
      then linearCoeff (rankComponent i (imagePullback W D h f)) S *
        (linearTraceCharacter S (imageTranslate W D h T)).re else 0 := by
  symm
  apply Fintype.sum_equiv
    (LinearEquiv.arrowCongr (LinearEquiv.refl F2 (B × C))
      (imageAmbientEquiv (A := A) W D h)).toEquiv
  intro S
  change _ = if LinearIdentities.Hybrid ((imageAmbientEquiv W D h).toLinearMap.comp S)
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) ∧
      (LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C)) =
          W.subtype.comp z
    then linearCoeff (rankComponent i f) ((imageAmbientEquiv W D h).toLinearMap.comp S) *
      (linearTraceCharacter ((imageAmbientEquiv W D h).toLinearMap.comp S) T).re else 0
  rw [image_hybrid_iff, image_compression_eq_iff, ← image_rank_coefficient,
    image_character]

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- Composition with an injection preserves the actual kernel. -/
theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- The small Fourier array is independent of the chosen injection once the
large function's actual coefficients are proved constant on kernel classes. -/
theorem smallCoeff_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallCoeff ι f = smallCoeff κ f := by
  funext T
  unfold smallCoeff
  by_cases hT : Function.Surjective T
  · simp only [ite_eq_left hT]
    exact hcoeff _ _ ((ker_comp_of_injective ι hι T).trans
      (ker_comp_of_injective κ hκ T).symm)
  · simp only [ite_eq_right hT]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

/-- Invariance of the function transfers to its actual normalized coefficients. -/
theorem coefficient_change (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    linearCoeff f (g.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (primalChange g)
  intro X
  change f X * (linearTraceCharacter (g.toLinearMap.comp S) X).re =
    f (X.comp g.toLinearMap) * (linearTraceCharacter S (X.comp g.toLinearMap)).re
  rw [character_change, hf g X]

end
end UniqueGamesTheorem.Inverse.KMSBasisInvariant

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergySupport
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The actual selector implies the exact rank loss for the actual
compressed Fourier frequency. -/
theorem hybrid_frequency_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (S : F →ₗ[F2] E) (hS : LinearIdentities.Hybrid S A B) :
    Module.finrank F2 (Restriction.compressFrequency A B S).range + order A B =
      Module.finrank F2 S.range := by
  have hr := Level.LinearRank.hybrid_rank_loss A B S hS.1 hS.2
  have hc : Level.LinearRank.compress A B S = Restriction.compressFrequency A B S := rfl
  rw [hc] at hr
  change Module.finrank F2 (Restriction.compressFrequency A B S).range +
    (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) = Module.finrank F2 S.range
  omega

variable [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- A rank-`i` component has no derivative coefficient away from the
exact compressed rank plus the order. -/
theorem linearCoeff_hybridDerivative_rankComponent_eq_zero
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : Module.finrank F2 Z.range + order A B ≠ i) :
    linearCoeff (hybridDerivative A B T (rankComponent i f)) Z = 0 := by
  rw [linearCoeff_hybridDerivative]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : LinearIdentities.Hybrid S A B ∧
      Restriction.compressFrequency A B S = Z
  · rw [ite_eq_left hS]
    have hr := hybrid_frequency_rank A B S hS.1
    rw [hS.2] at hr
    have hne : Module.finrank F2 S.range ≠ i := fun hs => hZ (hr.trans hs)
    simp only [rankComponent, coeff_component, ite_eq_right hne, zero_mul]
  · rw [ite_eq_right hS]

/-- If the order is larger than the selected rank, the actual derivative
vanishes, including all affine translates. -/
theorem hybridDerivative_rankComponent_eq_zero_of_lt_order
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (hi : i < order A B) :
    hybridDerivative A B T (rankComponent i f) = 0 := by
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_hybridDerivative_rankComponent_eq_zero A B T f i Z (by omega)]
  simp [linearCoeff]

/-- Exact normalized energy is supported on compressed frequencies of rank
`i - order A B`. This also holds above the order cutoff since every
coefficient then vanishes. -/
theorem hybridDerivative_rankComponent_energy_eq_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A) with Module.finrank F2 Z.range = i - order A B,
        linearCoeff (hybridDerivative A B T (rankComponent i f)) Z ^ 2 := by
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z _
  by_cases hZ : Module.finrank F2 Z.range = i - order A B
  · rw [ite_eq_left hZ]
  · rw [ite_eq_right hZ,
      linearCoeff_hybridDerivative_rankComponent_eq_zero A B T f i Z (by omega)]
    norm_num

/-- The rank-restricted exact energy written in the actual compressed
Fourier fibers used by the analytic estimate. -/
theorem hybridDerivative_rankComponent_energy_eq_rank_fibers
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A) with Module.finrank F2 Z.range = i - order A B,
        (∑ S : F →ₗ[F2] E,
          if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
          then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re
          else 0) ^ 2 := by
  rw [hybridDerivative_rankComponent_energy_eq_rank]
  simp_rw [linearCoeff_hybridDerivative]

section Product

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- The explicit change from quotient frequencies to blocks preserves rank. -/
theorem productFrequencyEquiv_finrank
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Module.finrank F2 (productFrequencyEquiv Z).range = Module.finrank F2 Z.range := by
  change Module.finrank F2
    (((quotientRightEquiv (R := F2) (A := A) (U := U)).toLinearMap.comp Z).comp
      (leftRangeEquiv (R := F2) (B := B) (C := C)).toLinearMap).range = _
  rw [LinearEquiv.range_comp, LinearMap.range_comp]
  exact (quotientRightEquiv (R := F2) (A := A) (U := U)).finrank_map_eq Z.range

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- The intrinsic restriction order agrees with the two fixed block dimensions. -/
theorem product_restriction_order :
    order (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) =
      Module.finrank F2 A + Module.finrank F2 C := by
  unfold order
  rw [← (leftRangeEquiv (R := F2) (B := A) (C := U)).finrank_eq,
    (quotientRightEquiv (R := F2) (A := B) (U := C)).finrank_eq]

variable [Finite A] [Finite U] [Finite B] [Finite C]
  [Fintype ((A × U) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × U))] [Fintype (B →ₗ[F2] U)]

/-- The actual derivative energy, restricted to the exact ordinary block rank. -/
theorem hybridDerivative_rankComponent_product_energy_eq_rank_fibers
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] U with
          Module.finrank F2 Z.range = i - (Module.finrank F2 A + Module.finrank F2 C),
        (∑ S : (B × C) →ₗ[F2] (A × U),
          if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
              (LinearMap.range (LinearMap.inl F2 B C)) ∧
              (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
          then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re
          else 0) ^ 2 := by
  let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
    Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
  rw [hybridDerivative_rankComponent_energy_eq_rank_fibers,
    product_restriction_order, Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv productFrequencyEquiv
  intro Z
  rw [productFrequencyEquiv_finrank]
  simp_rw [compressFrequency_eq_iff_product]

end Product

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyTransportSmall
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Small-component pullback under ambient coordinate equivalences

The small domain stays fixed while the ambient embedding and primal codomain
are transported together. These are exact identities for the actual Fourier
coefficients and synthesized functions; they require no analytic estimate.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F E' F' I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]

/-- Ambient coordinate pullback preserves invariance under every domain
basis change, by transporting that change through the domain equivalence. -/
theorem basisInvariant_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant
      (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro g X
  change f (LinearEquiv.arrowCongr a b (X.comp g.toLinearMap)) =
    f (LinearEquiv.arrowCongr a b X)
  have h : LinearEquiv.arrowCongr a b (X.comp g.toLinearMap) =
      (LinearEquiv.arrowCongr a b X).comp ((a.symm.trans g).trans a).toLinearMap := by
    ext x
    change b (X (g (a.symm x))) = b (X (a.symm (a (g (a.symm x)))))
    rw [a.symm_apply_apply]
  rw [h]
  exact hf ((a.symm.trans g).trans a) (LinearEquiv.arrowCongr a b X)

private theorem surjective_comp_symm_iff (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    Function.Surjective (T.comp b.symm.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨b.symm x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨b x, ?_⟩
    change T (b.symm (b x)) = y
    rw [b.symm_apply_apply, hx]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (E' →ₗ[F2] F')]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Exact small Fourier coefficient transport. The embedding need not be
injective, and the observable need not be basis invariant. -/
theorem smallCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff ι (fun M => f (LinearEquiv.arrowCongr a b M)) T =
      smallCoeff (a.toLinearMap.comp ι) f (T.comp b.symm.toLinearMap) := by
  have hc : LinearEquiv.arrowCongr b a (ι.comp T) =
      (a.toLinearMap.comp ι).comp (T.comp b.symm.toLinearMap) := by
    ext y
    rfl
  unfold smallCoeff
  rw [surjective_comp_symm_iff, NaturalTransport.linearCoeff_pullback, hc]

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

/-- The actual synthesized small component commutes with ambient pullback,
with the small domain fixed and the primal codomain transported by `b`. -/
theorem smallComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) :
    smallComponent ι (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun X => smallComponent (a.toLinearMap.comp ι) f (b.toLinearMap.comp X) := by
  apply eq_of_coeff_eq
  intro T
  rw [coeff_smallComponent, smallCoeff_pullback]
  have hp (X : I →ₗ[F2] F) :
      LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
    ext x
    rfl
  have hd : LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
    ext x
    rfl
  simpa only [coeff_smallComponent, hp, hd] using
    (NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b
      (smallComponent (a.toLinearMap.comp ι) f) T).symm

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFoundationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

/-- Restricting the denominator to a chart containing the set preserves the
numerator. This is the exact finite-set step used after Grassmann expansion. -/
theorem inter_chart_eq (S I C : Finset Ω) (hSC : S ⊆ C) :
    S ∩ (I ∩ C) = S ∩ I := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hS, hI, _⟩
    exact ⟨hS, hI⟩
  · rintro ⟨hS, hI⟩
    exact ⟨hS, hI, hSC hS⟩

/-- A nonempty part of the set in an interval witnesses that the chart and
interval meet. No positive denominator is silently assumed. -/
theorem chart_inter_nonempty (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) : (I ∩ C).Nonempty := by
  obtain ⟨x, hx⟩ := hSI
  exact ⟨x, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).2, hSC (Finset.mem_inter.mp hx).1⟩⟩

/-- Intersecting a nonempty conditioning interval with a chart containing the
set can only increase its relative density. -/
theorem relativeDensity_le_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hIC : (I ∩ C).Nonempty) :
    relativeDensity S I ≤ relativeDensity S (I ∩ C) := by
  unfold relativeDensity
  rw [inter_chart_eq S I C hSC]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hIC)
  · exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

/-- The quantitative density conclusion passes to the matrix chart without
losing any factor. -/
theorem density_bound_passes_to_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) {α : ℝ} (hα : α ≤ relativeDensity S I) :
    (I ∩ C).Nonempty ∧ α ≤ relativeDensity S (I ∩ C) := by
  have hIC := chart_inter_nonempty S I C hSC hSI
  exact ⟨hIC, hα.trans (relativeDensity_le_chart S I C hSC hIC)⟩

end FiniteDensity

end
end UniqueGamesTheorem.Inverse.KMS

end

section

/-!
An independent frame inside `L` can be completed using vectors from `W` whenever
`L` lies in the sum of the frame's span and `W`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Inverse.KMS

/-- Restricted completion of an independent frame. The original vectors need
not belong to `W`; only the newly chosen vectors are required to do so. -/
theorem exists_restricted_completion {n q t : ℕ}
    (Q : Fin q → Ambient n) (W L : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (hQL : Submodule.span F2 (Set.range Q) ≤ L)
    (hLW : L ≤ Submodule.span F2 (Set.range Q) ⊔ W)
    (hL : Module.finrank F2 L = q + t) :
    ∃ z : Fin t → W,
      LinearIndependent F2 (Sum.elim Q (fun i => (z i : Ambient n))) ∧
        Submodule.span F2
          (Set.range (Sum.elim Q (fun i => (z i : Ambient n)))) = L := by
  classical
  let T : Set (Ambient n) := Set.range Q ∪ (W ⊓ L : Submodule F2 (Ambient n))
  have hQT : Set.range Q ⊆ T := Set.subset_union_left
  have hTspan : Submodule.span F2 T = L := by
    change Submodule.span F2
      (Set.range Q ∪ ((W ⊓ L : Submodule F2 (Ambient n)) : Set (Ambient n))) = L
    rw [Submodule.span_union, Submodule.span_eq,
      ← sup_inf_assoc_of_le W hQL, inf_eq_right.mpr hLW]
  obtain ⟨B, hBT, hQB, hTB, hB⟩ :=
    exists_linearIndepOn_id_extension hQ.linearIndepOn_id hQT
  have hBspan : Submodule.span F2 B = L := by
    rw [← hTspan]
    exact le_antisymm (Submodule.span_mono hBT) (Submodule.span_le.mpr hTB)
  let D : Set (Ambient n) := B \ Set.range Q
  let f : Fin q ⊕ D → Ambient n := Sum.elim Q Subtype.val
  have hf_inj : Function.Injective f := by
    apply Sum.elim_injective.mpr
    refine ⟨hQ.injective, Subtype.val_injective, ?_⟩
    intro i d hid
    exact d.property.2 ⟨i, hid⟩
  have hf_range : Set.range f = B := by
    ext x
    constructor
    · rintro ⟨i | d, rfl⟩
      · exact hQB (Set.mem_range_self i)
      · exact d.property.1
    · intro hx
      by_cases hxQ : x ∈ Set.range Q
      · obtain ⟨i, rfl⟩ := hxQ
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx, hxQ⟩, rfl⟩
  have hf : LinearIndependent F2 f := by
    apply (linearIndepOn_id_range_iff hf_inj).mp
    rw [hf_range]
    exact hB
  have hcard := finrank_span_eq_card hf
  rw [hf_range, hBspan, hL] at hcard
  have hDcard : Fintype.card D = t := by
    apply Nat.add_left_cancel (n := q)
    simpa using hcard.symm
  let e : Fin t ≃ D := (Fintype.equivFinOfCardEq hDcard).symm
  let z : Fin t → W := fun i =>
    ⟨(e i).val, ((hBT (e i).property.1).resolve_left (e i).property.2).1⟩
  let g : (Fin q ⊕ Fin t) ≃ (Fin q ⊕ D) := Equiv.sumCongr (Equiv.refl _) e
  have hz : Sum.elim Q (fun i => (z i : Ambient n)) = f ∘ g := by
    funext i
    cases i <;> rfl
  refine ⟨z, ?_, ?_⟩
  · rw [hz]
    exact hf.comp g g.injective
  · rw [hz, g.surjective.range_comp, hf_range, hBspan]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Decompose a finite domain by its exact fibers. -/
theorem nat_card_eq_sum_fibers (f : X → Y) :
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]

/-- The event count is the sum of the same fibers over the event. -/
theorem nat_card_event_eq_sum_fibers (f : X → Y) (p : Y → Prop) :
    Nat.card {x : X // p (f x)} =
      ∑ y : {y : Y // p y}, Nat.card {x : X // f x = y.val} := by
  let e : (Σ y : {y : Y // p y}, {x : X // f x = y.val}) ≃
      {x : X // p (f x)} :=
    { toFun := fun a => ⟨a.2.val, a.2.property.symm ▸ a.1.property⟩
      invFun := fun a => ⟨⟨f a.val, a.property⟩, ⟨a.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro a; rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]

/-- Constant fibers give an exact density identity, including an empty target.
The nonzero fiber size is established geometrically for restricted bases. -/
theorem uniformFiber_card_ratio (f : X → Y) (p : Y → Prop)
    (c : ℕ) (hc : 0 < c)
    (hf : ∀ y, Nat.card {x : X // f x = y} = c) :
    (Nat.card {x : X // p (f x)} : ℝ) / Nat.card X =
      (Nat.card {y : Y // p y} : ℝ) / Nat.card Y := by
  have hX : Nat.card X = Nat.card Y * c := by
    rw [nat_card_eq_sum_fibers f]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  have hE : Nat.card {x : X // p (f x)} = Nat.card {y : Y // p y} * c := by
    rw [nat_card_event_eq_sum_fibers f p]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  rw [hE, hX, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Nat.cast_pos.mpr hc))

/-- Sampling from a larger finite space and accepting only a subset never
increases the density of an event within that subset. Empty subsets are handled
explicitly, so this statement makes no hidden nonemptiness assumption. -/
theorem subtype_event_ratio_le {Z : Type*} [Fintype Z] (D : Z → Prop)
    (p : {z : Z // D z} → Prop) :
    (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card Z ≤
      (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card {z : Z // D z} := by
  by_cases hD : Nat.card {z : Z // D z} = 0
  · have hE : Nat.card {z : {z : Z // D z} // p z} = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hD]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hE]
    simp
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
    · exact Nat.cast_le.mpr
        (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

theorem prefix_independent (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : LinearIndependent F2 Q :=
  z.property.comp Sum.inl Sum.inl_injective

/-- The restriction's Grassmann interval satisfies the same total complexity
budget. This uses only `W ≤ span Q ⊔ W`, never the false assumption `Q ⊆ W`. -/
theorem interval_complexity_le (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    Module.finrank F2 (prefixSpan Q) +
      (n - Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n))) ≤
        q + (n - Module.finrank F2 W) := by
  have hA : Module.finrank F2 (prefixSpan Q) = q := by
    change Module.finrank F2 ↥(Submodule.span F2 (Set.range Q)) = q
    exact (finrank_span_eq_card hQ).trans (Fintype.card_fin q)
  have hW : Module.finrank F2 W ≤
      Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n)) :=
    Submodule.finrank_mono le_sup_right
  rw [hA]
  omega

theorem restrictedLiftDensity_eq_zero_of_dependent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : ¬ LinearIndependent F2 Q) : restrictedLiftDensity S Q W = 0 := by
  have hE : IsEmpty {z : Fin t → W // completionEvent S Q W z} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨h, _⟩ := z.property
    exact hQ (prefix_independent Q W ⟨z.val, h⟩)
  let := hE
  simp [restrictedLiftDensity]

theorem interval_completion_nonempty (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (hQ : LinearIndependent F2 Q)
    (L : IntervalVertex (t := t) Q W) :
    Nonempty (RestrictedCompletion (t := t) Q W L.val.val) := by
  have hL := (Finset.mem_filter.mp L.property).2
  obtain ⟨z, hz, hspan⟩ := exists_restricted_completion Q W L.val.val hQ
    hL.1 hL.2 L.val.property
  exact ⟨⟨z, hz, hspan⟩⟩

/-- The uniform law on successful completions is exactly the uniform
Grassmann interval law, even when the fixed prefix is not contained in W. -/
theorem independent_density_eq_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (z₀ : IndependentCompletion (t := t) Q W) :
    (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
        relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  let f := completionIntervalVertex (t := t) Q W
  let c := Nat.card {z : IndependentCompletion (t := t) Q W // f z = f z₀}
  have hc : 0 < c := by
    let : Nonempty {z : IndependentCompletion (t := t) Q W // f z = f z₀} :=
      ⟨⟨z₀, rfl⟩⟩
    exact Nat.card_pos
  have hf (L : IntervalVertex (t := t) Q W) :
      Nat.card {z : IndependentCompletion (t := t) Q W // f z = L} = c := by
    obtain ⟨a⟩ := interval_completion_nonempty Q W hQ L
    obtain ⟨b⟩ := interval_completion_nonempty Q W hQ (f z₀)
    exact (Nat.card_congr (completionFiberEquiv Q W L)).trans
      ((restrictedCompletionCard_eq a b).trans
        (Nat.card_congr (completionFiberEquiv Q W (f z₀))).symm)
  have he := uniformFiber_card_ratio f (fun L => L.val ∈ S) c hc hf
  change (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
    (Nat.card {L : IntervalVertex (t := t) Q W // L.val ∈ S} : ℝ) /
      Nat.card (IntervalVertex (t := t) Q W) at he
  rw [he, Nat.card_congr (intervalEventEquiv S Q W)]
  simp only [IntervalVertex, Nat.card_eq_finsetCard, relativeDensity]

/-- The unconditioned restricted lift has density at most that of its exact
Grassmann interval. Unlike a union-bound argument, no independence-error term
is needed because dependent tuples are rejected by the lift. -/
theorem restrictedLiftDensity_le_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    restrictedLiftDensity S Q W ≤
      relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  unfold restrictedLiftDensity
  rw [Nat.card_congr (completionEventEquiv S Q W)]
  by_cases h : Nonempty (IndependentCompletion (t := t) Q W)
  · obtain ⟨z₀⟩ := h
    exact (subtype_event_ratio_le
      (fun z : Fin t → W => LinearIndependent F2 (joinedTuple Q W z))
      (fun z => completionVertex Q W z ∈ S)).trans
        (le_of_eq (independent_density_eq_interval S Q W hQ z₀))
  · let : IsEmpty (IndependentCompletion (t := t) Q W) := not_nonempty_iff.mp h
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The full KMS restriction transfer, with the stronger exact ε bound. -/
theorem grassmann_pseudorandom_restricted {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n (q + t))) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    restrictedLiftDensity S Q W ≤ ε := by
  by_cases hQ : LinearIndependent F2 Q
  · exact (restrictedLiftDensity_le_interval S Q W hQ).trans
      (hS (prefixSpan Q) (prefixSpan Q ⊔ W) le_sup_left
        ((interval_complexity_le Q W hQ).trans hbudget))
  · rw [restrictedLiftDensity_eq_zero_of_dependent S Q W hQ]
    exact hε

theorem grassmann_pseudorandom_lift {ell r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) : TuplePseudorandom S r ε := by
  intro q t h Q W hb
  subst ell
  exact grassmann_pseudorandom_restricted S hS hε Q W hb

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem lowerRows_le_graph_iff {ι : Type*} (d : ι → X) (s : ι → Y)
    (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ↔ ∀ i, T (d i) = s i := by
  rw [lowerRows, Submodule.span_le]
  constructor
  · intro h i
    exact (h ⟨i, rfl⟩).symm
  · rintro h _ ⟨i, rfl⟩
    exact (h i).symm

theorem graph_le_upperColumns_iff {ι : Type*}
    (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    T.graph ≤ upperColumns t q ↔ ∀ i, (q i).comp T = t i := by
  constructor
  · intro h i
    apply LinearMap.ext
    intro x
    have hx := h (show (x, T x) ∈ T.graph from rfl)
    have hi := ((Submodule.mem_iInf _).mp hx) i
    exact sub_eq_zero.mp hi
  · intro h x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    change q i x.2 - t i x.1 = 0
    rw [hx]
    exact sub_eq_zero.mpr (congrArg (fun f : X →ₗ[K] K => f x.1) (h i))

/-- Exact translation of a Grassmann interval into simultaneous row and
column constraints, retaining their inhomogeneous right-hand sides. -/
theorem interval_iff_slice {ι κ : Type*} (d : ι → X) (s : ι → Y)
    (t : κ → X →ₗ[K] K) (q : κ → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ∧ T.graph ≤ upperColumns t q ↔
      (∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j) := by
  rw [lowerRows_le_graph_iff, graph_le_upperColumns_iff]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- Transposing the chart map sends a column specification to its dot functional. -/
theorem dotFunctional_comp_vecMulLinear (M : Matrix ι κ K) (q : κ → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional (M *ᵥ q) := by
  apply LinearMap.ext
  intro x
  change q ⬝ᵥ (x ᵥ* M) = (M *ᵥ q) ⬝ᵥ x
  rw [← Matrix.mulVec_transpose, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem column_equation_iff (M : Matrix ι κ K) (q : κ → K) (t : ι → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional t ↔ M *ᵥ q = t := by
  rw [dotFunctional_comp_vecMulLinear]
  exact dotFunctional_injective.eq_iff

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_lines_binary [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] :
    Nat.card (Lines (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  classical
  let spanMap : {v : E // v ≠ 0} → Lines (ZMod 2) E := fun v =>
    ⟨Submodule.span (ZMod 2) {v.val}, finrank_span_singleton v.property⟩
  have hinj : Function.Injective spanMap := by
    intro v w h
    have hv : v.val ∈ Submodule.span (ZMod 2) {w.val} := by
      have hs : Submodule.span (ZMod 2) {v.val} =
          Submodule.span (ZMod 2) {w.val} := congrArg Subtype.val h
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · exact False.elim (v.property (by simpa [hc0] using hc.symm))
    · exact Subtype.ext (by simpa [hc1] using hc.symm)
  have hsurj : Function.Surjective spanMap := by
    intro L
    obtain ⟨v, hv0, _⟩ := (finrank_eq_one_iff').mp L.property
    have hv : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one L.property v.property hv).symm
  let e : {v : E // v ≠ 0} ≃ Lines (ZMod 2) E := Equiv.ofBijective spanMap ⟨hinj, hsurj⟩
  let coords : E ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) E) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let : Finite E := Finite.of_equiv _ coords.symm.toEquiv
  let : Fintype E := Fintype.ofFinite E
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem card_hyperplanes_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] :
    Nat.card (Hyperplanes (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  rw [Nat.card_congr (hyperplanesEquivDualLines (K := ZMod 2) (E := E)),
    card_lines_binary, Subspace.dual_finrank_eq]

theorem card_extensions_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (H : Submodule (ZMod 2) E) :
    Nat.card (Extensions H) = 2 ^ finrank (ZMod 2) (E ⧸ H) - 1 := by
  rw [Nat.card_congr (extensionsEquivLines H), card_lines_binary]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_other_extensions_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E)
    (H : HyperplanesBelow L) :
    Nat.card {W : Extensions H.val // W.val ≠ L} =
      2 ^ finrank (ZMod 2) (E ⧸ H.val) - 2 := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let base : Extensions H.val := ⟨L, H.property.1, H.property.2.symm⟩
  let : Fintype (Extensions H.val) := Fintype.ofFinite _
  have heq : (fun W : Extensions H.val => W.val ≠ L) = (fun W => W ≠ base) := by
    funext W
    apply propext
    apply not_congr
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [heq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
    card_extensions_binary]
  omega

theorem card_grassmann_neighbors_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E) (m : ℕ)
    (hE : finrank (ZMod 2) E = finrank (ZMod 2) L + m) :
    Nat.card (GrassmannNeighbors L) =
      (2 ^ finrank (ZMod 2) L - 1) * (2 ^ (m + 1) - 2) := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let : Fintype (HyperplanesBelow L) := Fintype.ofFinite _
  rw [Nat.card_congr (neighborsEquivExtensionData L), Nat.card_sigma]
  have hterm (H : HyperplanesBelow L) :
      Nat.card {W : Extensions H.val // W.val ≠ L} = 2 ^ (m + 1) - 2 := by
    rw [card_other_extensions_binary]
    have h := H.val.finrank_quotient_add_finrank
    have hH := H.property.2
    congr 2
    omega
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (hyperplanesBelowEquiv L), card_hyperplanes_binary]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Every full Grassmann neighbor is reached by an outside rank-one update.
The proof works over every field and never selects a graph chart. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]

/-- A codimension-one subspace is the kernel of a nonzero functional. -/
theorem exists_functional_ker_eq (H : Submodule K E)
    (hH : finrank K H + 1 = finrank K E) :
    ∃ a : E →ₗ[K] K, a ≠ 0 ∧ LinearMap.ker a = H := by
  have hproper : H < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    rw [h, finrank_top] at hH
    omega)
  obtain ⟨a, ha, hle⟩ := H.exists_le_ker_of_lt_top hproper
  refine ⟨a, ha, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

/-- An arbitrary Grassmann neighbor is the range of one of the actual
rank-one updates used by the ordered-basis test. -/
theorem exists_rankOneUpdate_range_eq (X : E →ₗ[K] F)
    (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors (LinearMap.range X)) :
    ∃ (a : E →ₗ[K] K) (y : F), a ≠ 0 ∧ y ∉ LinearMap.range X ∧
      LinearMap.range (rankOneUpdate X a y) = W.val := by
  let H : Submodule K E := W.val.comap X
  have hmap : H.map X = LinearMap.range X ⊓ W.val := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨LinearMap.mem_range_self X x, hx⟩
    · rintro ⟨⟨x, hx⟩, hz⟩
      exact ⟨x, by change X x ∈ W.val; rw [hx]; exact hz, hx⟩
  have hH : finrank K H + 1 = finrank K E := by
    rw [(Submodule.equivMapOfInjective X hX H).finrank_eq, hmap]
    exact W.property.2.trans (LinearMap.finrank_range_of_inj hX)
  obtain ⟨a, ha, hker⟩ := exists_functional_ker_eq H hH
  obtain ⟨x₀, hx₀⟩ := LinearMap.surjective ha (1 : K)
  have hnotle : ¬ W.val ≤ LinearMap.range X := by
    intro hle
    have heq := Submodule.eq_of_le_of_finrank_eq hle W.property.1
    have hd := W.property.2
    rw [heq, inf_idem] at hd
    omega
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp hnotle
  let y := w - X x₀
  have hy : y ∉ LinearMap.range X := by
    intro hy
    apply hwX
    have h := (LinearMap.range X).add_mem hy (LinearMap.mem_range_self X x₀)
    simpa only [y, sub_add_cancel] using h
  refine ⟨a, y, ha, hy, ?_⟩
  have hle : LinearMap.range (rankOneUpdate X a y) ≤ W.val := by
    rintro z ⟨x, rfl⟩
    have hxker : x - a x • x₀ ∈ LinearMap.ker a := by
      change a (x - a x • x₀) = 0
      simp only [map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
    have hxW : X (x - a x • x₀) ∈ W.val := by
      have hxH : x - a x • x₀ ∈ H := by rwa [← hker]
      exact hxH
    have heq : rankOneUpdate X a y x = X (x - a x • x₀) + a x • w := by
      simp only [rankOneUpdate_apply, y, map_sub, map_smul, smul_sub]
      abel
    rw [heq]
    exact W.val.add_mem hxW (W.val.smul_mem _ hwW)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
    W.property.1, LinearMap.finrank_range_of_inj hX]

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartIntervalsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

/-- Checking an annihilator basis suffices to test membership in a subspace. -/
theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

/-- Split a product functional into its two coordinate functionals. -/
theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

/-- Coordinates for an arbitrary interval. There are exactly `dim A` rows and
`codim B` columns, so an interval order bound gives the required slice bound. -/
theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
For a fixed nonzero binary functional, all updates with a prescribed image
form one affine coset of the image of its kernel. This is an exact fiber
equivalence, so it retains the multiplicities needed for uniform sampling.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem card_fixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) = Nat.card a.ker :=
  (Nat.card_congr (fixedFunctionalNeighborFiberEquiv X hX a ha hy₀)).symm

theorem card_fixedFunctionalNeighborFiber_pow [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (FixedFunctionalNeighborFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  classical
  rw [card_fixedFunctionalNeighborFiber X hX a ha hy₀, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := a.ker), ZMod.card]
  congr 1
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  omega

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

theorem card_outsideNeighborPairFiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Nat.card (OutsideNeighborPairFiber X a y₀) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  rw [← Nat.card_congr (fixedFunctionalEquivPairFiber X hX a ha hy₀)]
  exact card_fixedFunctionalNeighborFiber_pow X hX a ha hy₀

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

theorem card_grassmann_neighbors_graph (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  have h := card_grassmann_neighbors_binary T.graph m (by
    rw [finrank_graph, Module.finrank_prod]
    simp)
  simpa only [finrank_graph, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

theorem card_full_neighbors {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  classical
  have h : Nat.card {W : KMS.Vertex (ell + m) ell //
      KMS.Adjacent (matrixVertex M) W} =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
    rw [← Nat.card_congr (kmsNeighborsEquiv (matrixVertex M))]
    change Nat.card (GrassmannNeighbors
      ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap)) = _
    rw [← Nat.card_congr (grassmannNeighborsMapEquiv
      (coordinateJoin (ZMod 2) ell m) (matrixGraph M))]
    exact card_grassmann_neighbors_graph M.vecMulLinear
  simpa only [Nat.card_eq_fintype_card, KMS.neighbors, Fintype.card_subtype] using h

/-- Exactly two full Grassmann neighbors for every nonzero factor pair. -/
theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

theorem liftedIndicator_nonneg {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : 0 ≤ liftedIndicator S X := by
  unfold liftedIndicator
  split <;> norm_num

theorem liftedIndicator_le_one {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : liftedIndicator S X ≤ 1 := by
  unfold liftedIndicator
  split <;> norm_num

/-- A change of the ordered domain basis leaves the range unchanged. -/
theorem inLift_comp_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (g : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) (X : BasisMap n ell) :
    InLift S (X.comp g.toLinearMap) ↔ InLift S X := by
  unfold InLift
  rw [LinearMap.range_comp_of_range_eq_top X g.range]

/-- The lift is basis-invariant in precisely the Fourier theorem's sense. -/
theorem liftedIndicator_basisInvariant {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    KMSBasisInvariant.IsBasisInvariant (liftedIndicator S) := by
  intro g X
  simp only [liftedIndicator, inLift_comp_iff]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

/-- Uniform sampling pushes forward to uniform sampling whenever every fiber
is equivalent to the same nonempty finite type. This applies to real and
rational expectations alike. -/
theorem expect_eq_of_uniform_fibers [Fintype X] [Fintype Y] [Fintype G]
    [Nonempty G] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) (g : Y → M) :
    (𝔼 x, g (f x)) = 𝔼 y, g y := by
  calc
    _ = 𝔼 z : Y × G, g z.1 :=
      Fintype.expect_equiv (fiberProductEquiv f e) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset Y) (Finset.univ : Finset G)
          (fun z : Y × G => g z.1))

end UniformFibers

theorem lift_nonempty_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (lift S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨L, hL, _⟩ := (mem_lift S X).mp hX
    exact ⟨L, hL⟩
  · rintro ⟨L, hL⟩
    let X := (rangeFiberEquiv L.val).symm (vertexBasis L)
    refine ⟨X.val, (mem_lift S X.val).mpr ?_⟩
    exact ⟨L, hL, X.property.2⟩

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

theorem card_functional (ell : ℕ) : Fintype.card (Functional ell) = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2)]
  change Fintype.card (ZMod 2) ^ Module.finrank KMS.F2 (Module.Dual KMS.F2
    (KMS.Ambient ell)) = _
  rw [Subspace.dual_finrank_eq]
  simp [KMS.Ambient, KMS.F2]

theorem card_ambient (n : ℕ) : Fintype.card (KMS.Ambient n) = 2 ^ n := by
  simp [KMS.Ambient, KMS.F2]

theorem card_range {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    Fintype.card X.range = 2 ^ ell := by
  rw [Module.card_eq_pow_finrank (K := KMS.F2), LinearMap.finrank_range_of_inj hX]
  simp [KMS.Ambient, KMS.F2]

/-- The exact good-event count, including the zero-dimensional boundary. -/
theorem card_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (goodParameters X).card = (2 ^ ell - 1) * (2 ^ n - 2 ^ ell) := by
  rw [goodParameters, Finset.card_product]
  have ha : (Finset.univ.filter (fun a : Functional ell => a ≠ 0)).card =
      2 ^ ell - 1 := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_functional]
    simp
  have hy : (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range)).card =
      2 ^ n - 2 ^ ell := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_ambient]
    rw [card_range X hX]
  rw [ha, hy]

/-- Exceptional mass is bounded by the sum of the two factor exceptions. -/
theorem badParameters_mass_le {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    1 - ((goodParameters X).card : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hcard : 2 ^ ell ≤ 2 ^ n := by
    rw [← card_ambient ell, ← card_ambient n]
    exact Fintype.card_le_of_injective X hX
  have hone : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by decide)
  rw [card_goodParameters X hX, Fintype.card_prod, card_functional, card_ambient]
  push_cast [Nat.cast_sub hone, Nat.cast_sub hcard]
  have he : (0 : ℝ) < 2 ^ ell := pow_pos (by norm_num) _
  have hn : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  field_simp
  nlinarith

/-- The same estimate in the complement-cardinality form used for deleting
the bad event from a finite expectation. -/
theorem badParameters_mass_le_compl {n ell : ℕ} (X : BasisMap n ell)
    (hX : Function.Injective X) :
    (((Finset.univ \ goodParameters X).card : ℕ) : ℝ) /
        Fintype.card (Functional ell × KMS.Ambient n) ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have ht : (0 : ℝ) < Fintype.card (Functional ell × KMS.Ambient n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsub := Finset.card_le_card (Finset.subset_univ (goodParameters X))
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub hsub,
    Finset.card_univ, sub_div, div_self (ne_of_gt ht)]
  exact badParameters_mass_le X hX

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

/-- Every full Grassmann neighbor has exactly the same number of original
factor pairs. The number is the size of one codimension-one kernel. -/
theorem card_outsideNeighborSample_fiber [Fintype E]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (W : MatrixChart.GrassmannNeighbors X.range) :
    Nat.card {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
  obtain ⟨a, y, ha, hy, hW⟩ := exists_rankOneUpdate_range_eq X hX W
  let e : {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃
      OutsideNeighborPairFiber X a y := Equiv.subtypeEquivRight (fun p => by
    constructor
    · intro h
      exact (congrArg Subtype.val h).trans hW.symm
    · intro h
      exact Subtype.ext (h.trans hW))
  rw [Nat.card_congr e]
  exact card_outsideNeighborPairFiber X hX a ha hy

/-- Uniform neighbor law for any real observable. There is no chart
restriction, hidden conditioning, or additional loss in this identity. -/
theorem expect_outsideNeighborSample [Fintype E] [Fintype F]
    [Fintype (E →ₗ[ZMod 2] ZMod 2)]
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    [Fintype (MatrixChart.GrassmannNeighbors X.range)]
    (g : MatrixChart.GrassmannNeighbors X.range → ℝ) :
    (𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p)) =
      𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W := by
  let G := Fin (2 ^ (Module.finrank (ZMod 2) E - 1))
  let : Nonempty G := ⟨⟨0, by positivity⟩⟩
  let e : ∀ W : MatrixChart.GrassmannNeighbors X.range,
      {p : OutsideNeighborFactors X // outsideNeighborSample X hX p = W} ≃ G :=
    fun W => Finite.equivFinOfCardEq (card_outsideNeighborSample_fiber X hX W)
  exact expect_eq_of_uniform_fibers (outsideNeighborSample X hX) e g

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonNeighborsRetention
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

private theorem relativeDensity_eq_expect_subtype {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- The ordered-basis test conditioned on its good event samples every full
Grassmann neighbor uniformly. The target observable is the original lifted
indicator, so this identity directly feeds the matrix-test retention bound. -/
theorem outsideNeighbor_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (𝔼 p : OutsideNeighborFactors X,
      liftedIndicator S (rankOneUpdate X p.1.val p.2.val)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  let e : MatrixChart.GrassmannNeighbors X.range ≃
      {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} :=
    MatrixChart.kmsNeighborsEquiv (rangeVertex X hX)
  let : Fintype (MatrixChart.GrassmannNeighbors X.range) :=
    Fintype.ofEquiv {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} e.symm
  let g : MatrixChart.GrassmannNeighbors X.range → ℝ :=
    fun W => if (e W).val ∈ S then 1 else 0
  calc
    _ = 𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p) := by
      apply Finset.expect_congr rfl
      intro p _
      unfold liftedIndicator
      rw [inLift_iff_rangeVertex_mem S _
        (injective_rankOneUpdate X hX p.1.val p.2.property)]
      have hv : rangeVertex (rankOneUpdate X p.1.val p.2.val)
          (injective_rankOneUpdate X hX p.1.val p.2.property) =
            (e (outsideNeighborSample X hX p)).val := by
        apply Subtype.ext
        rfl
      rw [hv]
      by_cases hp : (e (outsideNeighborSample X hX p)).val ∈ S <;> simp [g, hp]
    _ = 𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W :=
      expect_outsideNeighborSample X hX g
    _ = 𝔼 W : {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W},
        if W.val ∈ S then (1 : ℝ) else 0 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := (relativeDensity_eq_expect_subtype S
      (KMS.Adjacent (rangeVertex X hX))).symm

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonPseudorandomTupleMapLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

theorem tupleMap_range (x : (Fin q ⊕ Fin t) → Ambient n) :
    LinearMap.range (tupleMap x) = Submodule.span F2 (Set.range x) :=
  (tupleBasis q t).constr_range F2

theorem tupleMap_injective_iff (x : (Fin q ⊕ Fin t) → Ambient n) :
    Function.Injective (tupleMap x) ↔ LinearIndependent F2 x := by
  constructor
  · intro h
    have hi := (tupleBasis q t).linearIndependent.map' (tupleMap x)
      (LinearMap.ker_eq_bot.mpr h)
    simpa only [Function.comp_def, tupleMap_basis] using hi
  · intro h
    exact (tupleBasis q t).injective_constr_of_linearIndependent h

theorem inLift_tupleMap_iff (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) :
    InLift S (tupleMap (joinedTuple Q W z)) ↔ completionEvent S Q W z := by
  constructor
  · intro h
    have hi := (tupleMap_injective_iff _).mp (injective_of_inLift h)
    obtain ⟨L, hLS, hr⟩ := h
    refine ⟨hi, ?_⟩
    have he : completionVertex Q W ⟨z, hi⟩ = L := by
      apply Subtype.ext
      exact (tupleMap_range _).symm.trans hr
    simpa only [he] using hLS
  · rintro ⟨hi, hmem⟩
    exact ⟨completionVertex Q W ⟨z, hi⟩, hmem, tupleMap_range _⟩

/-- The tuple density equals the normalized expectation of the actual lift's
indicator on the prescribed basis-coordinate restriction. -/
theorem restrictedLiftDensity_eq_expect (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    restrictedLiftDensity S Q W =
      𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z)) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [liftedIndicator, inLift_tupleMap_iff]
  rw [Finset.sum_boole]
  simp only [restrictedLiftDensity, Nat.card_eq_fintype_card, Fintype.card_subtype]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open KMSAffineRestrictionSplit

variable {n ell q t : ℕ}

/-- Exact pointwise identity for the actual affine slice after splitting its
parameters. The fixed prefix includes the affine intercept. -/
theorem translate_join_eq_constr
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0)
    (B : Parameter (localVanishing D U) W) (C : E0 →ₗ[F2] W) :
    translate D W T (join D U E0 W hDU hc B C) =
      (complementBasis U E0 hc bU b0).constr F2
        (joinedTuple
          (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
          (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i))) := by
  apply (complementBasis U E0 hc bU b0).ext
  intro i
  rw [Module.Basis.constr_basis]
  cases i with
  | inl i =>
      simp only [complementBasis_inl, joinedTuple, Sum.elim_inl,
        Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_left]
  | inr i =>
      simp only [complementBasis_inr, joinedTuple, Sum.elim_inr,
        Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_right]
      rfl

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- Good-event conditioning is the exact full-neighbor Grassmann retention. -/
theorem goodParameters_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (goodParameters X).expect
      (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  rw [← expect_coe_eq]
  calc
    _ = 𝔼 p : OutsideNeighborFactors X,
        liftedIndicator S (rankOneUpdate X p.1.val p.2.val) :=
      Fintype.expect_equiv (goodParametersEquiv X) _ _ (fun _ => rfl)
    _ = _ := outsideNeighbor_retention S X hX

/-- Quantitative local comparison, with a slightly smaller exceptional-mass
bound than the stated KMS Lemma 2.7. -/
theorem fullStepRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    |fullStepRetention S X -
      KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX))| ≤
        ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  rw [← goodParameters_expect S X hX]
  apply (abs_expect_sub_restrict_le (goodParameters X)
    (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2))
    (fun p => liftedIndicator_nonneg S _) (fun p => liftedIndicator_le_one S _)).trans
  simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] using
    (badParameters_mass_le_compl X hX)

/-- Choosing a uniform accepted ordered basis chooses a uniform element of
the original Grassmann set. -/
theorem liftRange_retention_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (𝔼 X : lift S,
      KMS.relativeDensity S (KMS.neighbors (liftRange S X).val)) = KMS.retention S := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  rw [expect_eq_of_uniform_fibers (liftRange S) (liftRangeFiberAut S)
    (fun L : S => KMS.relativeDensity S (KMS.neighbors L.val))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, KMS.retention]
  congr 1
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun L => KMS.relativeDensity S (KMS.neighbors L))).symm

/-- The actual full sampling-law comparison for the lifted Grassmann set. -/
theorem liftRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hLift := (lift_nonempty_iff S).mpr hS
  let : Nonempty (lift S) := ⟨⟨hLift.choose, hLift.choose_spec⟩⟩
  rw [liftRetention, ← liftRange_retention_expect S,
    ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  exact fullStepRetention_compare S X.val
    (injective_of_inLift ((mem_lift S X.val).mp X.property))

theorem liftDensity_eq_card {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S = ((lift S).card : ℝ) / Fintype.card (BasisMap n ell) := by
  simp only [liftDensity, liftedIndicator, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, lift]

theorem liftDensity_pos {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) : 0 < liftDensity S := by
  rw [liftDensity_eq_card]
  apply div_pos
  · exact Nat.cast_pos.mpr ((lift_nonempty_iff S).mpr hS).card_pos
  · exact Nat.cast_pos.mpr Fintype.card_pos

/-- Fourier correlation uses the full ambient space. This identity is the
exact conversion to the conditional-start retention and preserves density. -/
theorem liftDensity_mul_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S * liftRetention S =
      𝔼 X : BasisMap n ell, liftedIndicator S X * fullStepRetention S X := by
  rw [liftDensity_eq_card, liftRetention, expect_coe_eq, mass_mul_expect,
    Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [liftedIndicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rfl

/-- Swapping the independent factors matches the Fourier noise convention
of first choosing a direction, then a functional, including both zero cases. -/
theorem fullStepRetention_eq_noise {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) :
    fullStepRetention S X =
      𝔼 y : KMS.Ambient n, 𝔼 a : Functional ell,
        liftedIndicator S (X + a.smulRight y) := by
  unfold fullStepRetention
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Finset.expect_comm _ _ _

/-- A proved ambient correlation bound converts directly to the conditional
retention bound; positive density follows from the actual nonempty lift. -/
theorem liftRetention_le_of_correlation_le {n ell : ℕ}
    (S : Finset (KMS.Vertex n ell)) (hS : S.Nonempty) (ζ : ℝ)
    (hc : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) ≤ ζ * liftDensity S) :
    liftRetention S ≤ ζ := by
  rw [← liftDensity_mul_retention S, mul_comm ζ (liftDensity S)] at hc
  exact le_of_mul_le_mul_left hc (liftDensity_pos S hS)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

/-- Elementary eventual decay, using Archimedean unboundedness of powers.
No dimensional rate is hidden in a limit or a filter assumption. -/
theorem exists_binary_ratio_threshold (c ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → c / (2 : ℝ) ^ n ≤ ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (c / ε) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, fun n hn => ?_⟩
  have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hcp : c / ε ≤ (2 : ℝ) ^ n := hk.le.trans hp
  have hc : c ≤ (2 : ℝ) ^ n * ε := (div_le_iff₀ hε).mp hcp
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  simpa only [mul_comm] using hc

/-- Positive relative density implies a nonempty intersection, even though
relative density itself is defined to be zero on empty intervals. -/
theorem nonempty_of_relativeDensity_pos {Ω : Type*} [DecidableEq Ω]
    (S I : Finset Ω) (h : 0 < KMS.relativeDensity S I) : (S ∩ I).Nonempty := by
  by_contra hn
  have he : S ∩ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [KMS.relativeDensity, he] at h

/-- The complete inverse implication from the explicit analytic lift theorem
to the dimension-uniform Grassmann theorem required by the inverse. -/
theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
    KMS.ExpansionPrinciple := by
  intro ζ hζ hζ1
  obtain ⟨ε, hε, hε1, r, ellA, hA⟩ :=
    h (ζ / 2) (by positivity) (by linarith)
  obtain ⟨ellE, hEllE⟩ := exists_binary_ratio_threshold 1 (ζ / 8) (by positivity)
  refine ⟨ε, hε, hε1, max r 1, le_max_right _ _, max ellA ellE, ?_⟩
  intro ell hEll
  obtain ⟨nA, hnA⟩ := hA ell ((le_max_left _ _).trans hEll)
  obtain ⟨nE, hnE⟩ := exists_binary_ratio_threshold ((2 : ℝ) ^ ell)
    (ζ / 8) (by positivity)
  refine ⟨max nA nE, ?_⟩
  intro n hn S hS hret
  have hError : ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n ≤ ζ / 4 := by
    have he := hEllE ell ((le_max_right _ _).trans hEll)
    have hn' := hnE n ((le_max_right _ _).trans hn)
    rw [one_div] at he
    linarith
  by_contra hNo
  have hPseudo : GrassmannPseudorandom S r ε := by
    intro A B hAB hbudget
    by_contra hd
    have hd' : ε < KMS.relativeDensity S (KMS.interval A B) := lt_of_not_ge hd
    apply hNo
    exact ⟨A, B, hAB, hbudget.trans (le_max_left _ _),
      nonempty_of_relativeDensity_pos S _ (hε.trans hd'), hd'.le⟩
  have hLift : liftRetention S ≤ ζ / 2 :=
    hnA n ((le_max_left _ _).trans hn) S hS
      (grassmann_pseudorandom_lift S hPseudo hε.le)
  have hCmp := (abs_le.mp ((liftRetention_compare S hS).trans hError)).1
  linarith

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentZoomInAlgebraLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- A stronger restriction budget supplies every smaller budget. -/
theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
# Tuple pseudorandomness controls the actual affine squared density

This is the input conversion needed by the ordered-basis expansion theorem.
It starts directly from its tuple pseudorandomness assumption. All affine
intercepts and the full uniform parameter law are preserved by the checked
adapted-complement, split, and presentation equivalences.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonAffineDensity

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAffineRestriction KMSAffineRestrictionSplit
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {n ell q t r : ℕ} {ε : ℝ}

/-- The tuple hypothesis bounds the lift in every domain basis: the lift
depends only on the range, which is the span of the same prescribed tuple. -/
theorem lifted_expect_in_basis_of_tuple (S : Finset (Vertex n ell))
    (hS : TuplePseudorandom S r ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z))) ≤ ε := by
  have hdim : ell = q + t := by
    simpa [KMS.Ambient] using Module.finrank_eq_card_basis b
  subst ell
  have hc : restrictedLiftDensity S Q W ≤ ε := hS q t rfl Q W hbudget
  rw [restrictedLiftDensity_eq_expect] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.expect_congr rfl
  intro z _
  unfold liftedIndicator InLift
  rw [b.constr_range F2, tupleMap_range]

/-- Translation of the free coordinates retains the full uniform tuple law. -/
theorem lifted_expect_shifted_basis_of_tuple {E0 : Type*}
    [AddCommGroup E0] [Module F2 E0]
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S r ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    [Fintype (E0 →ₗ[F2] W)]
    (b0 : Module.Basis (Fin t) F2 E0) (T0 : E0 →ₗ[F2] W)
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) ≤ ε := by
  have heq : (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) =
      𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z)) := by
    apply Fintype.expect_equiv (affineCoordinates b0 T0)
    intro H
    rfl
  rw [heq]
  exact lifted_expect_in_basis_of_tuple S hS b Q W hbudget

/-- The adapted prefix contains all directions whose affine center lies
outside W. After splitting, each fixed constrained parameter gives an allowed
arbitrary prefix, and all free coordinates remain uniform in W. -/
theorem affine_expect_of_complement_of_tuple
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S r ε)
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (hbudget : Module.finrank F2 U + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  rw [expect_restrict D U E0 W hDU hc T]
  apply Finset.expect_le Finset.univ_nonempty
  intro B _
  let bU := Module.finBasis F2 U
  let b0 := Module.finBasis F2 E0
  have heq :
      (𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S (translate D W T (join D U E0 W hDU hc B C))) =
      𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S ((complementBasis U E0 hc bU b0).constr F2
          (joinedTuple
            (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
            (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i)))) := by
    apply Finset.expect_congr rfl
    intro C _
    rw [translate_join_eq_constr D U E0 W hDU hc T hE0 bU b0 B C]
  rw [heq]
  exact lifted_expect_shifted_basis_of_tuple S hS (complementBasis U E0 hc bU b0)
    _ W b0 (freeCenter E0 W T hE0) hbudget

/-- Order d affine restrictions require at most 2d tuple restriction budget. -/
theorem affine_expect_bound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε)
    (D : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  obtain ⟨U, E0, hDU, hE0, hc, hdim⟩ :=
    KMSAffineRestrictionComplement.exists_bounded_complement D W T
  have hcodim : n - Module.finrank F2 W = Module.finrank F2 (KMS.Ambient n ⧸ W) := by
    have hd := W.finrank_quotient_add_finrank
    have hn : Module.finrank F2 (KMS.Ambient n) = n := by simp [KMS.Ambient]
    rw [hn] at hd
    omega
  apply affine_expect_of_complement_of_tuple S hS D U E0 W hDU hc T hE0
  rw [hcodim]
  change Module.finrank F2 D + Module.finrank F2 (KMS.Ambient n ⧸ W) ≤ d at horder
  omega

/-- Booleanity turns the exact restriction probability into its squared norm. -/
theorem affine_squared_expect_bound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε)
    (D : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) ≤ ε := by
  have heq : (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) =
      𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A := by
    apply Finset.expect_congr rfl
    intro A _
    unfold restrict liftedIndicator
    split <;> norm_num
  rw [heq]
  exact affine_expect_bound_of_tuple S hS D W T horder

/-- Directly discharge the fourth-moment affine density input from the
literal tuple pseudorandomness input of the ordered-basis expansion theorem. -/
theorem lifted_affineDensityBound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε) :
    KMSFourthMoment.AffineDensityBound d ε (liftedIndicator S) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  calc
    (𝔼 X : D →ₗ[F2] C, liftedIndicator S (T + J.comp (X.comp L)) ^ 2) =
        𝔼 A : Parameter L.ker J.range,
          (restrict (liftedIndicator S) L.ker J.range T A) ^ 2 :=
      KMSAffineRestrictionPresentation.expect_presentation_sq L hL J hJ T _
    _ ≤ ε := affine_squared_expect_bound_of_tuple S hS L.ker J.range T
      (KMSAffineRestrictionPresentation.order_le_of_dimensions L hL J hJ d hdim)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonAffineDensity

end

section

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

/-- The actual invariance property is independent of the ambient coordinates. -/
theorem ambient_basisInvariant_transport (h : E ≃ₗ[F2] E')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (fun X : E' →ₗ[F2] F =>
      f (X.comp h.toLinearMap)) := by
  intro g X
  let k : E ≃ₗ[F2] E := (h.trans g).trans h.symm
  have hc : (X.comp g.toLinearMap).comp h.toLinearMap =
      (X.comp h.toLinearMap).comp k.toLinearMap := by
    ext x
    simp [k]
  change f ((X.comp g.toLinearMap).comp h.toLinearMap) = f (X.comp h.toLinearMap)
  rw [hc]
  exact hf k (X.comp h.toLinearMap)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Basis-invariant matrix functions have constant actual Fourier coefficients
on kernel fibers. This uses ambient automorphism transitivity proved from the
first isomorphism theorem, followed by the exact change-of-basis identity for
the normalized trace-character transform. -/

namespace UniqueGamesTheorem.Inverse.KMSKernelOrbitsFourier

open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant
open UniqueGamesTheorem.Inverse.KMSKernelOrbits

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]

/-- Actual coefficients depend on the kernel, not on the chosen embedding of
the quotient into the basis-index space. No coefficient-invariance premise is
assumed beyond the original function's basis invariance. -/
theorem coefficient_eq_of_ker_eq (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (S T : F →ₗ[F2] E) (hker : S.ker = T.ker) :
    linearCoeff f S = linearCoeff f T := by
  obtain ⟨g, hg⟩ := exists_postcomp_equiv_of_ker_eq S T hker
  have h := coefficient_change f hf g S
  rw [hg] at h
  exact h.symm

end
end UniqueGamesTheorem.Inverse.KMSKernelOrbitsFourier

end

section

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallCoeff ι f = smallCoeff κ f :=
  smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalyticHybridCoordinates KMSAnalytic

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

section Binary
variable [Module F2 A] [Module F2 W] [Module F2 D] [Module F2 B] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]

omit [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))] in
/-- The actual hybrid and rank selectors reduce to the small component's
ordinary surjectivity selector. The only remaining geometric selector is
injectivity of the complementary block. -/
theorem hybrid_rank_coeff_assemble
    {z : B →ₗ[F2] W} (hz : Function.Surjective z)
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D)))
    (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) :
    (if LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) (assemble p)
     else 0) =
      if Function.Injective p.v then smallCoeff κ f (fullCoordinates p) else 0 := by
  have hh := hybrid_assemble_iff p hz
  change LinearIdentities.Hybrid (assemble p) _ _ ↔
    Function.Injective p.v ∧ Function.Surjective (fullCoordinates p) at hh
  rw [hh]
  by_cases hv : Function.Injective p.v
  · simp only [hv, true_and, ite_true, if_true]
    by_cases hp : Function.Surjective (fullCoordinates p)
    · rw [ite_eq_left hp]
      have hr := finrank_assemble p hv hp
      simp only [rankComponent, coeff_component, hr, ite_true, if_true]
      have he := congrFun (smallCoeff_eq_of_basisInvariant (embedLast p.v) κ
        (embedLast_injective p.v hv) hκ f hf) (fullCoordinates p)
      rw [smallCoeff, ite_eq_left hp, ← assemble_eq_embedLast_comp] at he
      exact he
    · simp [hp, smallCoeff]
  · simp [hv]

end Binary
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Cardinality budgets for hybrid coefficient fibers

Extensions are counted by an exact equivalence with linear maps on the
complement. Injective complementary maps are bounded by all linear maps.
Images of fixed dimension are counted using the proved basis encoding of
subspaces. Their combined exponent fits the mixed Fourier denominator.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix

/-- The restriction fiber has exactly as many elements as the maps on its
complement, before any finite-field cardinality formula is applied. -/
theorem card_restriction_fiber_eq {R B C W : Type*} [Ring R]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup W] [Module R W]
    [Fintype ((B × C) →ₗ[R] W)] [Fintype (C →ₗ[R] W)]
    (z : B →ₗ[R] W) :
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)).card = Fintype.card (C →ₗ[R] W) := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (extensionEquiv (C := C) z)

section Injections

variable {C D : Type*}
  [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
  [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]

/-- Exact binary cardinality of the unrestricted complementary map space. -/
theorem card_linearMap_eq [Fintype (C →ₗ[F2] D)] :
    Fintype.card (C →ₗ[F2] D) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using
    (CompressionCount.natCard_linearMap (U := C) (C := D))

end Injections

section Images

variable {U : Type*} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]

/-- Choose one ordered basis for each image. The resulting encoding gives
the dimension-sensitive image count, rather than the count of all subspaces. -/
theorem natCard_rank_subspaces_le (q : ℕ) :
    Nat.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.mul_comm] using
    (SubspaceCounting.card_binary_subspaces_rank_le (V := U)
      (Module.finrank F2 U) q le_rfl)

theorem card_rank_subspaces_le [Fintype (Submodule F2 U)] (q : ℕ) :
    Fintype.card {W : Submodule F2 U // Module.finrank F2 W = q} ≤
      2 ^ (q * Module.finrank F2 U) := by
  simpa only [Nat.card_eq_fintype_card] using natCard_rank_subspaces_le (U := U) q

end Images

/-- The three counting costs leave nonnegative slack in the ambient
dimension exponent. The complementary image space has dimension `q + d`. -/
theorem count_exponent_le (a b q d : ℕ) :
    q * (q + d) + (b * d) * 2 + b * q ≤ (2 * b + q) * (a + q + d) := by
  calc
    _ ≤ q * (q + d) + (b * d) * 2 + b * q + ((2 * b + q) * a + b * q) :=
      Nat.le_add_right _ _
    _ = _ := by ring

/-- The actual nonnegative counts fit the mixed Fourier denominator.
The bound also permits real-valued upper estimates for those counts. -/
theorem count_budget_le (a b q d : ℕ) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (q + d)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤
      (2 : ℝ) ^ ((2 * b + q) * (a + q + d)) := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hvSq : countV ^ 2 ≤ ((2 : ℝ) ^ (b * d)) ^ 2 :=
    (sq_le_sq₀ hv0 (pow_nonneg htwo _)).mpr hv
  have hfirst : countW * countV ^ 2 ≤
      (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 :=
    mul_le_mul hw hvSq (sq_nonneg countV) (pow_nonneg htwo _)
  calc
    _ ≤ (2 : ℝ) ^ (q * (q + d)) * ((2 : ℝ) ^ (b * d)) ^ 2 *
        (2 : ℝ) ^ (b * q) :=
      mul_le_mul hfirst he he0 (mul_nonneg (pow_nonneg htwo _) (sq_nonneg _))
    _ = (2 : ℝ) ^ (q * (q + d) + (b * d) * 2 + b * q) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (count_exponent_le a b q d)

/-- Ambient-dimension form of the same budget, with the split dimension
identity supplied by the adapted coordinates. -/
theorem count_budget_le_of_dimension (a b q d ell : ℕ)
    (hell : ell = a + q + d) (countW countV extensionFactor : ℝ)
    (hv0 : 0 ≤ countV) (he0 : 0 ≤ extensionFactor)
    (hw : countW ≤ (2 : ℝ) ^ (q * (ell - a)))
    (hv : countV ≤ (2 : ℝ) ^ (b * d))
    (he : extensionFactor ≤ (2 : ℝ) ^ (b * q)) :
    countW * countV ^ 2 * extensionFactor ≤ (2 : ℝ) ^ ((2 * b + q) * ell) := by
  have hsub : ell - a = q + d := by omega
  rw [hsub] at hw
  rw [hell]
  exact count_budget_le a b q d countW countV extensionFactor hv0 he0 hw hv he

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentMixedEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact Fourier merging after fixing a primal product block. The coefficient
uses normalized expectation, while the merged frequency sum is unnormalized.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment
open UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergyPhase

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- The free frequency can be summed first, with no multiplicity factor. -/
theorem sum_frequency_blocks {M : Type*} [AddCommMonoid M]
    [Fintype (F →ₗ[F2] A)] [Fintype (F →ₗ[F2] I)]
    [Fintype (F →ₗ[F2] (A × I))]
    (g : (F →ₗ[F2] (A × I)) → M) :
    ∑ S, g S = ∑ T : F →ₗ[F2] I, ∑ alpha : F →ₗ[F2] A, g (alpha.prod T) := by
  rw [← frequencyBlockEquiv.sum_comp g, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable [FiniteDimensional F2 A] [FiniteDimensional F2 I]
  [FiniteDimensional F2 F]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (F →ₗ[F2] A)]

omit [Fintype (I →ₗ[F2] F)] in
/-- Fixing a primal block merges exactly its dual frequency block. -/
theorem partialRestrict_eq_synthesis
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict h a = synthesis (fun T : F →ₗ[F2] I =>
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re) := by
  funext X
  change h (a.coprod X) = _
  rw [← linear_fourier_inversion h (a.coprod X), sum_frequency_blocks]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro alpha _
  rw [character_prod_coprod_re]
  ring

/-- The actual partial-restriction coefficient is an unnormalized frequency
merge; normalized Fourier expectation introduces no additional factor. -/
theorem coeff_partialRestrict
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (T : F →ₗ[F2] I) :
    linearCoeff (partialRestrict h a) T =
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re := by
  rw [partialRestrict_eq_synthesis, coeff_synthesis]

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! The actual Fourier coefficient of an adapted hybrid fiber factors into
the complementary-block phase and a mixed partial-restriction coefficient. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSAnalyticHybridEnergyPhase
open KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

variable [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype (C →ₗ[F2] D)] [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]

theorem sum_compressedFiber (z : B →ₗ[F2] W)
    (g : ((B × C) →ₗ[F2] (A × (W × D))) → ℝ) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)}, g S.val) =
      ∑ α : (B × C) →ₗ[F2] A, ∑ ψ : Extension (C := C) z,
        ∑ v : C →ₗ[F2] D, g (assemble (coordinateOfData z α ψ v)) := by
  calc
    _ = ∑ p : ((B × C) →ₗ[F2] A) × Extension (C := C) z × (C →ₗ[F2] D),
        g (assemble (coordinateOfData z p.1 p.2.1 p.2.2)) := by
      apply Fintype.sum_equiv (compressedFiberDataEquiv (A := A) (D := D) z)
      intro S
      exact congrArg g (assemble_extract z S).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]

variable [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

omit [Fintype ((B × C) →ₗ[F2] W)] [Fintype (C →ₗ[F2] D)] in
/-- One sum over the fixed frequency block is precisely the Fourier
coefficient of the actual partially restricted small component. -/
theorem sum_alpha_hybrid_term (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C))
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    (∑ α : (B × C) →ₗ[F2] A,
      (if LinearIdentities.Hybrid (assemble (coordinateOfData z α ψ v))
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f)
          (assemble (coordinateOfData z α ψ v)) else 0) *
        (linearTraceCharacter (assemble (coordinateOfData z α ψ v)) T).re) =
      if Function.Injective v then
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re *
        ((linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) else 0 := by
  simp_rw [hybrid_rank_coeff_assemble hz _ κ hκ f hf, character_assemble_re]
  by_cases hv : Function.Injective v
  · simp only [coordinateOfData, hv, ite_true, if_true]
    rw [coeff_partialRestrict]
    simp only [coeff_smallComponent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    change smallCoeff κ f (α.prod (ψ.val.prod (LinearMap.snd F2 B C))) *
        ((linearTraceCharacter α (primalA T)).re *
          ((linearTraceCharacter ψ.val (primalW T)).re *
            (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re)) = _
    ring
  · simp [coordinateOfData, hv]

/-- Exact phase/frequency factorization in the adapted fiber. Every
coefficient on the right belongs to the actual mixed partial restriction. -/
theorem hybrid_fiber_coefficient_factorization
    (z : B →ₗ[F2] W) (hz : Function.Surjective z)
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
        compressBlock S = z.prod (0 : B →ₗ[F2] D)},
      (if LinearIdentities.Hybrid S.val
          (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
        (linearTraceCharacter S.val T).re) =
      (∑ v ∈ Finset.univ.filter (fun v : C →ₗ[F2] D => Function.Injective v),
        (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re) *
      (∑ ψ : Extension (C := C) z,
        (linearTraceCharacter ψ.val (primalW T)).re *
          linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
            (ψ.val.prod (LinearMap.snd F2 B C))) := by
  rw [sum_compressedFiber z (fun S =>
    (if LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S else 0) *
      (linearTraceCharacter S T).re), Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ((B × C) →ₗ[F2] A)))
    (t := (Finset.univ : Finset (C →ₗ[F2] D))),
    sum_alpha_hybrid_term z hz κ hκ f hf T]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
Exact sums on fixed Fourier slices and compressed-frequency extension fibers.
Fixing the last frequency block leaves each first block exactly once, and
passing between an extension subtype and a filtered sum changes no weights.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSFourthMoment

section Slice

variable {F W C : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (W × C))]
  [Fintype (F →ₗ[F2] W)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in
/-- An actual slice fixing the last frequency block is parametrized by all
first blocks, with no multiplicity or normalization factor. -/
theorem sliceEnergy_fixed_snd (ν : F →ₗ[F2] C)
    (g : ((W × C) →ₗ[F2] F) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = ν) g =
      ∑ ψ : F →ₗ[F2] W, linearCoeff g (ψ.prod ν) ^ 2 := by
  let : Finite (F →ₗ[F2] C) := Finite.of_injective
    (fun ν : F →ₗ[F2] C => (0 : F →ₗ[F2] W).prod ν) (by
      intro ν μ h
      simpa using congrArg
        (fun T : F →ₗ[F2] (W × C) => (LinearMap.snd F2 W C).comp T) h)
  let := Fintype.ofFinite (F →ₗ[F2] C)
  unfold sliceEnergy
  rw [Finset.sum_filter, sum_frequency_blocks, Finset.sum_comm]
  simp only [LinearMap.snd_prod]
  apply Finset.sum_congr rfl
  intro ψ _
  exact Fintype.sum_ite_eq' ν (fun x => linearCoeff g (ψ.prod x) ^ 2)

end Slice

section HybridSlice

variable {B W C : Type*}
  [AddCommGroup B] [Module F2 B]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]
  [Fintype ((B × C) →ₗ[F2] W)]

omit [FiniteDimensional F2 B] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in
theorem sliceEnergy_snd_eq_sum (g : ((W × C) →ₗ[F2] (B × C)) → ℝ) :
    sliceEnergy (fun T => (LinearMap.snd F2 W C).comp T = LinearMap.snd F2 B C) g =
      ∑ ψ : (B × C) →ₗ[F2] W,
        linearCoeff g (ψ.prod (LinearMap.snd F2 B C)) ^ 2 :=
  sliceEnergy_fixed_snd (LinearMap.snd F2 B C) g

end HybridSlice

section Extensions

variable {R B W C M : Type*} [Ring R]
  [AddCommGroup B] [Module R B]
  [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]
  [AddCommMonoid M] [Fintype ((B × C) →ₗ[R] W)]

/-- Summing over actual extensions is exactly the corresponding filtered
frequency sum. This identity applies to phases and squared coefficients. -/
theorem sum_extensions_eq_filter (z : B →ₗ[R] W)
    [Fintype (Extension (C := C) z)] (H : ((B × C) →ₗ[R] W) → M) :
    (∑ ψ : Extension (C := C) z, H ψ.val) =
      ∑ ψ with ψ.comp (LinearMap.inl R B C) = z, H ψ := by
  exact (Finset.sum_subtype
    (p := fun ψ : (B × C) →ₗ[R] W => ψ.comp (LinearMap.inl R B C) = z)
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)) (by simp) H).symm

end Extensions
end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! A single compressed-image contribution is controlled by an actual mixed
slice energy. The only losses are the explicit finite coordinate counts. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] D)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

omit [FiniteDimensional F2 W] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] W)] [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((W × C) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (W × C))] in
theorem traceCharacter_re_sq (S : (B × C) →ₗ[F2] W) (X : W →ₗ[F2] (B × C)) :
    (linearTraceCharacter S X).re ^ 2 = 1 := by
  by_cases h : linearTracePair X S = 0 <;>
    simp [linearTraceCharacter_apply, binarySign, h]

omit [Fintype ((B × C) →ₗ[F2] C)] in
/-- The contribution of all surjective compressed maps onto one fixed image
is bounded by the actual mixed-slice energy, with its exact extension count. -/
theorem adapted_image_energy_le_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) *
        sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
          (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
          (partialRestrict (smallComponent κ f) (primalA T)) := by
  let r : ((B × C) →ₗ[F2] W) → (B →ₗ[F2] W) :=
    fun ψ => ψ.comp (LinearMap.inl F2 B C)
  let a : (C →ₗ[F2] D) → ℝ := fun v => if Function.Injective v then
    (linearTraceCharacter (v.comp (LinearMap.snd F2 B C)) (primalD T)).re else 0
  let b : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    (linearTraceCharacter ψ (primalW T)).re
  let H : ((B × C) →ₗ[F2] W) → ℝ := fun ψ =>
    linearCoeff (partialRestrict (smallComponent κ f) (primalA T))
      (ψ.prod (LinearMap.snd F2 B C))
  have ha (v : C →ₗ[F2] D) : a v ^ 2 ≤ 1 := by
    dsimp [a]
    split_ifs
    · by_cases h : linearTracePair (primalD T) (v.comp (LinearMap.snd F2 B C)) = 0 <;>
        simp [binarySign, h]
    · norm_num
  have hb (ψ : (B × C) →ₗ[F2] W) : b ψ ^ 2 ≤ 1 := by
    exact le_of_eq (traceCharacter_re_sq ψ (primalW T))
  have hr (z : B →ₗ[F2] W) :
      (Finset.univ.filter (fun ψ => r ψ = z)).card ≤ Fintype.card (C →ₗ[F2] W) := by
    exact le_of_eq (card_restriction_fiber_eq z)
  have hfactor (z : B →ₗ[F2] W) (hz : Function.Surjective z) :
      adaptedFiberCoefficient z f T =
        (∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ) := by
    rw [adaptedFiberCoefficient, hybrid_fiber_coefficient_factorization z hz κ hκ f hf T]
    have he : (∑ ψ : Extension (C := C) z, b ψ.val * H ψ.val) =
        ∑ ψ with r ψ = z, b ψ * H ψ := by
      exact sum_extensions_eq_filter z (fun ψ => b ψ * H ψ)
    change _ = (∑ v, a v) * _
    rw [← he]
    congr 1
    simp only [a, Finset.sum_filter]
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z),
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hfactor z (Finset.mem_filter.mp hz).2]
    _ ≤ ∑ z : B →ₗ[F2] W,
        ((∑ v, a v) * (∑ ψ with r ψ = z, b ψ * H ψ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun z _ _ => sq_nonneg _)
    _ ≤ (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 *
        (Fintype.card (C →ₗ[F2] W) : ℝ) * ∑ ψ, H ψ ^ 2 :=
      sum_fiber_product_sq_le r a b H (Fintype.card (C →ₗ[F2] W)) ha hb hr
    _ = _ := by
      rw [sliceEnergy_snd_eq_sum]

omit [Fintype ((B × C) →ₗ[F2] C)] in
/-- The conditional analytic step uses an actual mixed-slice bound as its
only analytic hypothesis. -/
theorem adapted_image_energy_le_of_mixed
    (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))) (hκ : Function.Injective κ)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) (H : ℝ)
    (hH : sliceEnergy (fun U : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp U = LinearMap.snd F2 B C)
      (partialRestrict (smallComponent κ f) (primalA T)) ≤ H) :
    (∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W => Function.Surjective z), adaptedFiberCoefficient z f T ^ 2) ≤
      (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 * (Fintype.card (C →ₗ[F2] W) : ℝ) * H := by
  apply (adapted_image_energy_le_mixed κ hκ f hf T).trans
  exact mul_le_mul_of_nonneg_left hH (by positivity)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

/-- The original image contribution is the actual adapted fiber coefficient
used by the mixed-slice estimate. -/
theorem image_fiber_coefficient_transport (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (z : B →ₗ[F2] W) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) :
    (∑ S : (B × C) →ₗ[F2] (A × U),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = W.subtype.comp z
      then linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S *
        (linearTraceCharacter S T).re else 0) =
      adaptedFiberCoefficient z (imagePullback W D h f) (imageTranslate W D h T) := by
  rw [image_coefficient_sum_transport W D h z f T (Module.finrank F2 (A × (W × C)))]
  let weight : ((B × C) →ₗ[F2] (A × (W × D))) → ℝ := fun S =>
    (if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C)))
          (imagePullback W D h f)) S else 0) *
      (linearTraceCharacter S (imageTranslate W D h T)).re
  have hs : (∑ S with compressBlock S = z.prod (0 : B →ₗ[F2] D), weight S) =
      adaptedFiberCoefficient z (imagePullback W D h f) (imageTranslate W D h T) := by
    exact Finset.sum_subtype
      (Finset.univ.filter fun S : (B × C) →ₗ[F2] (A × (W × D)) =>
        compressBlock S = z.prod (0 : B →ₗ[F2] D)) (by simp) weight
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hh : LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) <;>
    by_cases hc : compressBlock S = z.prod (0 : B →ₗ[F2] D) <;>
    simp [weight, hh, hc]

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_r8a4bb9_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

attribute [local instance] OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.mapFintype
attribute [local instance] OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.submoduleFintype
/-- The original coefficient wrapper agrees with the adapted coefficient
at the exact dimension of the small comparison space. -/
theorem productFiberCoefficient_imageTransport
    (W D : Submodule F2 U) (hD : IsCompl W D) (z : B →ₗ[F2] W)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ)
    (hi : Module.finrank F2 (A × (W × C)) = i) :
    productFiberCoefficient i f T (W.subtype.comp z) =
      adaptedFiberCoefficient z (imagePullback W D hD f) (imageTranslate W D hD T) := by
  simpa only [hi, productFiberCoefficient] using
    image_fiber_coefficient_transport W D hD z f T

/-- The exact energy identity using the product coefficient wrapper. -/
theorem product_energy_eq_filter_coefficient
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] U with
        Module.finrank F2 Z.range = i - (Module.finrank F2 A + Module.finrank F2 C),
        productFiberCoefficient i f T Z ^ 2 := by
  rw [hybridDerivative_rankComponent_product_energy_eq_rank_fibers]
  apply Finset.sum_congr rfl
  intro frequency _
  congr 1
  unfold productFiberCoefficient
  apply Finset.sum_congr rfl
  intro dualMap _
  split_ifs <;> rfl

/-- One actual compressed-image contribution follows from the uniform
mixed-slice premise, retaining the exact finite-coordinate cost. -/
theorem product_image_energy_le_of_mixed
    (i : ℕ) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ)
    (hi : i ≤ Module.finrank F2 (A × U))
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (hMixed : ProductMixedSliceBound i f T L)
    (W : RankImage F2 U (i - (Module.finrank F2 A + Module.finrank F2 C))) :
    (∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
      productFiberCoefficient i f T (W.val.subtype.comp z.val) ^ 2) ≤
      ((2 : ℝ) ^ (Module.finrank F2 C * (Module.finrank F2 U -
        (i - (Module.finrank F2 A + Module.finrank F2 C))))) ^ 2 *
      (2 : ℝ) ^ (Module.finrank F2 C *
        (i - (Module.finrank F2 A + Module.finrank F2 C))) *
      (L / (2 : ℝ) ^ ((2 * Module.finrank F2 C +
        (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U))) := by
  let a := Module.finrank F2 A
  let b := Module.finrank F2 C
  let u := Module.finrank F2 U
  let q := i - (a + b)
  let d := u - q
  let den : ℝ := (2 : ℝ) ^ ((2 * b + q) * Module.finrank F2 (A × U))
  let v : ℝ := (2 : ℝ) ^ (b * d)
  let e : ℝ := (2 : ℝ) ^ (b * q)
  have hq : q + (a + b) = i := Nat.sub_add_cancel ho
  obtain ⟨D, hD⟩ := W.val.exists_isCompl
  have hWD : Module.finrank F2 W.val + Module.finrank F2 D = u :=
    imageCoordinates_finrank W.val D hD
  have hDdim : Module.finrank F2 D = d := by rw [W.property] at hWD; omega
  have hsmall : Module.finrank F2 (A × (W.val × C)) = i := by
    simp only [Module.finrank_prod, W.property]
    change a + (q + b) = i
    omega
  have hlarge : Module.finrank F2 (A × (W.val × D)) =
      Module.finrank F2 (A × U) := by
    simp only [Module.finrank_prod]
    rw [hWD]
  obtain ⟨κ, hκ⟩ := (finrank_le_iff_exists_linearMap
    (R := F2) (M := A × (W.val × C)) (M' := A × (W.val × D))).mp
      (by rw [hsmall, hlarge]; exact hi)
  have hm := hMixed W.val D W.property hD κ hκ
  have hbound := adapted_image_energy_le_of_mixed κ hκ
    (imagePullback W.val D hD f)
    (ambient_basisInvariant_transport (imageAmbientEquiv W.val D hD).symm f hf)
    (imageTranslate W.val D hD T) (L / den) hm
  have hco (z : B →ₗ[F2] W.val) :
      productFiberCoefficient i f T (W.val.subtype.comp z) =
        adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) := by
    exact productFiberCoefficient_imageTransport W.val D hD z f T i hsmall
  change _ ≤ v ^ 2 * e * (L / den)
  calc
    _ = ∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
        adaptedFiberCoefficient z.val (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hco]
    _ = ∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W.val => Function.Surjective z),
        adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2 := by
      exact (Finset.sum_subtype
        (p := fun z : B →ₗ[F2] W.val => Function.Surjective z)
        (Finset.univ.filter fun z : B →ₗ[F2] W.val => Function.Surjective z)
        (by simp) (fun z => adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2)).symm
    _ ≤ (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 *
        (Fintype.card (C →ₗ[F2] W.val) : ℝ) * (L / den) := hbound
    _ = _ := by
      rw [card_linearMap_eq, card_linearMap_eq]
      simp only [Nat.cast_pow, Nat.cast_ofNat, W.property, hDdim]
      simp only [v, e, b, q, a]

/-- Actual product Hybrid derivative energy follows from the actual mixed
slice estimate. Orders above the selected rank are included automatically. -/
theorem product_hybrid_energy_le_of_mixed
    (i : ℕ) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ) (hL : 0 ≤ L)
    (hi : i ≤ Module.finrank F2 (A × U))
    (hMixed : ProductMixedSliceBound i f T L) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) ≤ L := by
  by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
  · let a := Module.finrank F2 A
    let b := Module.finrank F2 C
    let u := Module.finrank F2 U
    let q := i - (a + b)
    let d := u - q
    let den : ℝ := (2 : ℝ) ^ ((2 * b + q) * (a + u))
    let v : ℝ := (2 : ℝ) ^ (b * d)
    let e : ℝ := (2 : ℝ) ^ (b * q)
    have hi' : i ≤ a + u := by simpa only [Module.finrank_prod] using hi
    have ho' : a + b ≤ i := ho
    have hq : q + (a + b) = i := Nat.sub_add_cancel ho'
    have hqu : q ≤ u := by omega
    have hdim : a + u = a + q + d := by dsimp [d]; omega
    let weight : (B →ₗ[F2] U) → ℝ := fun Z => productFiberCoefficient i f T Z ^ 2
    have hEach (W : RankImage F2 U q) :
        (∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val)) ≤ v ^ 2 * e * (L / den) := by
      simpa only [Module.finrank_prod] using
        product_image_energy_le_of_mixed i f hf T L hi ho hMixed W
    have hcountW : (Fintype.card (RankImage F2 U q) : ℝ) ≤
        (2 : ℝ) ^ (q * (a + u - a)) := by
      have hn := card_rank_subspaces_le (U := U) q
      have hr : (Fintype.card (RankImage F2 U q) : ℝ) ≤ (2 : ℝ) ^ (q * u) := by
        exact_mod_cast hn
      simpa only [Nat.add_sub_cancel_left] using hr
    have hcount : (Fintype.card (RankImage F2 U q) : ℝ) * v ^ 2 * e ≤ den :=
      count_budget_le_of_dimension a b q d (a + u) hdim
        (Fintype.card (RankImage F2 U q)) v e (by positivity) (by positivity)
        hcountW le_rfl le_rfl
    have hden : 0 < den := by dsimp [den]; positivity
    calc
      _ = ∑ Z : B →ₗ[F2] U with Module.finrank F2 Z.range = q, weight Z :=
        product_energy_eq_filter_coefficient T f i
      _ = ∑ W : RankImage F2 U q,
          ∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
            weight (W.val.subtype.comp z.val) := by
        rw [Finset.sum_subtype
          (p := fun z : B →ₗ[F2] U => Module.finrank F2 z.range = q)
          (Finset.univ.filter fun z : B →ₗ[F2] U => Module.finrank F2 z.range = q)
          (by simp) weight]
        calc
          _ = ∑ p : Σ W : RankImage F2 U q,
              {z : B →ₗ[F2] W.val // Function.Surjective z},
              weight (p.1.val.subtype.comp p.2.val) := by
            symm
            apply Fintype.sum_equiv
              (rankFrequencyImageEquiv (R := F2) (B := B) (U := U) q).symm
            intro p
            rfl
          _ = _ := Fintype.sum_sigma _
      _ ≤ ∑ _W : RankImage F2 U q, v ^ 2 * e * (L / den) := by
        apply Finset.sum_le_sum
        intro W _
        exact hEach W
      _ = ((Fintype.card (RankImage F2 U q) : ℝ) * v ^ 2 * e) * (L / den) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ den * (L / den) :=
        mul_le_mul_of_nonneg_right hcount (div_nonneg hL hden.le)
      _ = L := mul_div_cancel₀ L (ne_of_gt hden)
  · let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
        ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
      Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
    have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T f i
      (by rw [product_restriction_order]; omega)
    simpa [hzero] using hL

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyTransportSmallMixed
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

variable {A I J F F' : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup F] [Module F2 F]
  [AddCommGroup F'] [Module F2 F']

/-- Transport of the fixed block and the free block commutes with the actual
partial restriction. -/
theorem partialRestrict_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : ((A × I) →ₗ[F2] F') → ℝ) (u : A →ₗ[F2] F) :
    partialRestrict (fun Y => g (b.toLinearMap.comp Y)) u =
      fun X => partialRestrict g (b.toLinearMap.comp u) (b.toLinearMap.comp X) := by
  funext X
  change g (b.toLinearMap.comp (u.coprod X)) =
    g ((b.toLinearMap.comp u).coprod (b.toLinearMap.comp X))
  apply congrArg g
  apply LinearMap.ext
  intro p
  change b (u p.1 + X p.2) = b (u p.1) + b (X p.2)
  exact b.map_add _ _

private theorem arrowCongr_refl_left_apply (b : F ≃ₗ[F2] F') (X : I →ₗ[F2] F) :
    LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
  ext x
  rfl

private theorem arrowCongr_refl_right_apply (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
  ext x
  rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)] in
/-- Exact coefficient transport for a function pulled back only in its
primal codomain. -/
theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply, arrowCongr_refl_right_apply] using
    NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b g T

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Transport the prescribed frequency with the codomain. This identity
requires no surjectivity of the prescribed-frequency projection. -/
theorem sliceEnergy_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (fun X => g (b.toLinearMap.comp X)) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap) g := by
  unfold sliceEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I)).toEquiv
  intro T
  have hp : π.comp (T.comp b.symm.toLinearMap) = ν.comp b.symm.toLinearMap ↔
      π.comp T = ν := by
    constructor
    · intro h
      ext x
      have hx := congrArg (fun M : F' →ₗ[F2] J => M (b x)) h
      simpa using hx
    · intro h
      rw [← LinearMap.comp_assoc, h]
  simp only [LinearEquiv.coe_toEquiv, arrowCongr_refl_right_apply,
    linearCoeff_postcomp_equiv, hp]

variable {E E' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 A]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype ((A × I) →ₗ[F2] F')] [Fintype (F' →ₗ[F2] (A × I))]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
/-- The actual mixed small-component energy is invariant when its ambient
coordinates, embedding, fixed primal map, and prescribed frequency are all
transported together. -/
theorem sliceEnergy_partialRestrict_smallComponent_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : (A × I) →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) (u : A →ₗ[F2] F) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (partialRestrict (smallComponent ι
        (fun M => f (LinearEquiv.arrowCongr a b M))) u) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap)
        (partialRestrict (smallComponent (a.toLinearMap.comp ι) f)
          (b.toLinearMap.comp u)) := by
  rw [smallComponent_pullback, partialRestrict_codomain_pullback]
  exact sliceEnergy_codomain_pullback b _ π ν

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSLowLevelLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Decoder.PositiveMultiplier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

theorem sum_rankEnergy (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) =
      ∑ s, if rank s ≤ r then a s ^ 2 else 0 := by
  unfold rankEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rank s ≤ r
  · simp [eq_comm, Finset.mem_range, hs]
  · simp [eq_comm, Finset.mem_range, hs]

/-- Exact rank multiplier cutoff, without dimension-dependent constants. -/
theorem spectral_cutoff (rank : I → ℕ) (a : I → ℝ) (r : ℕ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) +
        ((2 : ℝ) ^ (r + 1))⁻¹ * ∑ s, a s ^ 2 := by
  rw [sum_rankEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have ht : 0 ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * a s ^ 2 := by positivity
  by_cases hs : rank s ≤ r
  · rw [ite_eq_left hs]
    have hinv : ((2 : ℝ) ^ rank s)⁻¹ ≤ 1 := by
      rw [← one_div]
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hm := mul_le_mul_of_nonneg_right hinv (sq_nonneg (a s))
    nlinarith
  · rw [ite_eq_right hs, zero_add]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (a s))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem spectral_cutoff_of_level_bounds (rank : I → ℕ) (a : I → ℝ)
    (r : ℕ) (C δ : ℝ) (htotal : (∑ s, a s ^ 2) = δ)
    (hlevels : ∀ i ≤ r, rankEnergy rank a i ≤ C * δ) :
    (∑ s, ((2 : ℝ) ^ rank s)⁻¹ * a s ^ 2) ≤
      ((r + 1 : ℕ) * C + ((2 : ℝ) ^ (r + 1))⁻¹) * δ := by
  have hsum : (∑ i ∈ Finset.range (r + 1), rankEnergy rank a i) ≤
      (r + 1 : ℕ) * C * δ := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), C * δ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlevels i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = _ := by simp; ring
  have hcut := spectral_cutoff rank a r
  rw [htotal] at hcut
  nlinarith only [hcut, hsum]
end FiniteCutoff

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniformNoise_apply (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    uniformNoise f X = 𝔼 v : F, 𝔼 l : E →ₗ[F2] F2, f (X + l.smulRight v) := by
  unfold uniformNoise linearRealNoiseOperator
  rw [subspaceLaw_sum]
  simp only [LinearMap.id_apply, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  ring

theorem uniformNoise_energy (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X * uniformNoise f X) =
      ∑ S : F →ₗ[F2] E, ((2 : ℝ) ^ Module.finrank F2 S.range)⁻¹ *
        linearCoeff f S ^ 2 := by
  unfold uniformNoise
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [subspaceLaw_eigenvalue, LinearMap.comp_id]

omit [Fintype F] [Fintype (E →ₗ[F2] F2)] in
theorem rankEnergy_eq (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    rankEnergy (fun S : F →ₗ[F2] E => Module.finrank F2 S.range)
      (linearCoeff f) i = 𝔼 X, rankComponent i f X ^ 2 := by
  rw [rankComponent_energy, Finset.sum_filter]
  rfl

end ActualFourier

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open KMSMomentScalar KMSAnalytic
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

/-- No particular polynomial in the cutoff is required for the scalar step. -/
theorem projection_bound_of_general_fourthMoment {X : Type*} [Fintype X]
    {f : X → ℝ} (hf : IsBoolean f) (g : X → ℝ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hprojection : (𝔼 x, g x ^ 2) = 𝔼 x, g x * f x)
    (hupper : (𝔼 x, g x ^ 4) ≤ C * (𝔼 x, g x ^ 2) * ε) :
    (𝔼 x, g x ^ 2) ≤ (C + 1) * ε ^ ((1 : ℝ) / 4) * (𝔼 x, f x) := by
  let η : ℝ := 𝔼 x, g x ^ 2
  let δ : ℝ := 𝔼 x, f x
  have hη : 0 ≤ η := Finset.expect_nonneg fun x _ => sq_nonneg _
  have hδ : 0 ≤ δ := boolean_average_nonneg hf
  have hlow := projection_fifth_le_density_fourth_moment hf g hprojection
  change η ^ 5 ≤ δ ^ 4 * (𝔼 x, g x ^ 4) at hlow
  have hupper' := mul_le_mul_of_nonneg_left hupper (pow_nonneg hδ 4)
  have hsmall : η ^ 4 ≤ C * ε * δ ^ 4 := by
    by_cases hz : η = 0
    · simpa only [hz, zero_pow (by decide : (4 : ℕ) ≠ 0)] using
        mul_nonneg (mul_nonneg hC hε) (pow_nonneg hδ 4)
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hηpos).mp
      nlinarith only [hlow, hupper']
  have hconstant : C ≤ (C + 1) ^ 4 := by
    nlinarith [sq_nonneg C, pow_nonneg hC 3, pow_nonneg hC 4]
  apply le_of_fourth_power_le hη (by positivity)
  calc
    η ^ 4 ≤ C * ε * δ ^ 4 := hsmall
    _ ≤ (C + 1) ^ 4 * ε * δ ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hε) (pow_nonneg hδ 4)
    _ = _ := by rw [mul_pow, mul_pow, fourth_root_power hε]

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual full-uniform rank-one correlation, with a general moment constant. -/
theorem uniformNoise_bound_of_general_fourthMoments
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (r : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hupper : ∀ i ≤ r, (𝔼 X, rankComponent i f X ^ 4) ≤
      C * (𝔼 X, rankComponent i f X ^ 2) * ε) :
    (𝔼 X, f X * uniformNoise f X) ≤
      ((r + 1 : ℕ) * ((C + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹) * (𝔼 X, f X) := by
  rw [uniformNoise_energy]
  apply spectral_cutoff_of_level_bounds
  · rw [linear_parseval, boolean_squared_average hf]
  · intro i hi
    rw [rankEnergy_eq]
    apply projection_bound_of_general_fourthMoment hf (rankComponent i f)
      C ε hC hε _ (hupper i hi)
    exact (component_inner_self _ f).symm
end ActualFourier

/-- Even an arbitrarily large constant depending on r alone permits the
cutoff and tolerance to be chosen before both dimensions. -/
theorem exists_general_cutoff_parameters (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
        ((2 : ℝ) ^ (r + 1))⁻¹ ≤ ζ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ζ / 4 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  let r := max 1 N
  let D : ℝ := C r + 1
  let t : ℝ := min 1 (ζ / (4 * (r + 1 : ℕ) * D))
  let ε : ℝ := t ^ 4
  have hD : 0 < D := by dsimp [D]; linarith [hC r]
  have hr : 1 ≤ r := le_max_left _ _
  have hden : 0 < 4 * (r + 1 : ℕ) * D := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hζ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hε : 0 < ε := pow_pos ht _
  have hε1 : ε ≤ 1 := pow_le_one₀ ht.le ht1
  have hroot : ε ^ ((1 : ℝ) / 4) = t := by
    have hpow : (ε ^ ((1 : ℝ) / 4)) ^ 4 = t ^ 4 := fourth_root_power hε.le
    have hn : 0 ≤ ε ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hε.le _
    exact le_antisymm (le_of_fourth_power_le hn ht.le hpow.le)
      (le_of_fourth_power_le ht.le hn hpow.symm.le)
  have hlow : (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) ≤ ζ / 4 := by
    rw [hroot]
    have ht' : t ≤ ζ / (4 * (r + 1 : ℕ) * D) := min_le_right _ _
    have hm := (le_div_iff₀ hden).mp ht'
    nlinarith only [hm]
  have htail : ((2 : ℝ) ^ (r + 1))⁻¹ < ζ / 4 := by
    have hmon : (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right 1 N) (Nat.le_succ r))
    simpa only [one_div, inv_pow] using hmon.trans_lt hN
  refine ⟨r, hr, ε, hε, hε1, ?_⟩
  change (r + 1 : ℕ) * (D * ε ^ ((1 : ℝ) / 4)) + _ ≤ ζ / 2
  linarith

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

namespace UniqueGamesTheorem.Inverse.KMSMomentToExpansion
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSMomentScalar KMSAnalytic KMSLowLevel

/-- Any proved dimension-independent upper moment with a finite local budget
supplies the exact ordered-basis expansion interface. This lemma is conditional
until the genuine KMS small-component induction supplies `hupper`. -/
theorem liftExpansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    LiftExpansionPrinciple := by
  intro ζ hζ _hζ1
  obtain ⟨r, _hr, ε, hε, hε1, hcut⟩ := exists_general_cutoff_parameters C hC hζ
  refine ⟨ε, hε, hε1, R r, ellMin r, ?_⟩
  intro ell hell
  refine ⟨0, ?_⟩
  intro n _hn S hS hPseudo
  have hf : IsBoolean (liftedIndicator S) := by
    intro X
    unfold liftedIndicator
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 ≤ liftDensity S := boolean_average_nonneg hf
  have hc := uniformNoise_bound_of_general_fourthMoments (liftedIndicator S) hf
    r (C r) ε (hC r) hε.le (hupper r ε hε.le hε1 ell hell n S hPseudo)
  have heq : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) =
      𝔼 X : BasisMap n ell, liftedIndicator S X * uniformNoise (liftedIndicator S) X := by
    apply Finset.expect_congr rfl
    intro X _
    congr 1
    rw [fullStepRetention_eq_noise, uniformNoise_apply]
  apply liftRetention_le_of_correlation_le S hS ζ
  rw [heq]
  apply hc.trans
  change ((r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
    ((2 : ℝ) ^ (r + 1))⁻¹) * liftDensity S ≤ ζ * liftDensity S
  apply mul_le_mul_of_nonneg_right _ hδ
  exact hcut.trans (by linarith)

/-- Checked finite bridges and parameter choices reduce the full KMS expansion
principle to the displayed actual upper-moment estimate, and nothing weaker. -/
theorem expansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    KMS.ExpansionPrinciple :=
  expansion_of_liftExpansion (liftExpansion_of_upperMoments C hC R ellMin hupper)

end
end UniqueGamesTheorem.Inverse.KMSMomentToExpansion

end

section

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v
attribute [local instance] mapFintype

variable {E A I J : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 A]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J] [FiniteDimensional F2 F]
  [Fintype E] [Fintype A] [Fintype I] [Fintype J] [Fintype F]

theorem mixedRankConstant_nonneg (R : ℕ) : 0 ≤ mixedRankConstant R := by
  unfold mixedRankConstant
  exact mul_nonneg (by positivity) (pow_nonneg (mixedStepFactor_nonneg R) _)

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

universe u v w

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

section Transport

variable {E' : Type u} {F' : Type w}
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype E'] [Fintype F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- Ambient and codomain coordinate pullback preserves every actual mixed
slice, while the exponent is unchanged by ambient dimension invariance. -/
theorem UniformMixedBound.pullback {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : UniformMixedBound r L f) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι u π hπ ν hr
  rw [sliceEnergy_partialRestrict_smallComponent_pullback a b ι f π ν u,
    a.finrank_eq]
  exact hf A I J (a.toLinearMap.comp ι) (a.injective.comp hι)
    (b.toLinearMap.comp u) π hπ (ν.comp b.symm.toLinearMap) hr

end Transport

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The shortcode inverse principle uses an arbitrary table function, full uniform
factor sampling, and an affine intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

/-- The fiber/Grassmann route produces the constant affine target `0,u`.
Keeping `u` is essential: this result does not claim a homogeneous target. -/
theorem Slice.constantAgreement_eq_affine {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) :
    S.constantAgreement f u = S.affineAgreement f 0 u := by
  simp [Slice.constantAgreement, Slice.affineAgreement]

theorem hasAffineSlice_of_constant {ell m : ℕ} (f : Mat ell m → Vector ell)
    (α : ℝ) (r : ℕ) (S : Slice ell m) (hrows : S.rows ≤ r)
    (hcolumns : S.columns ≤ r) (hne : S.points.Nonempty) (u : Vector ell)
    (h : α ≤ S.constantAgreement f u) : HasAffineSlice f α r := by
  exact ⟨S, hrows, hcolumns, hne, 0, u, by
    simpa only [S.constantAgreement_eq_affine f u] using h⟩

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

/-- The chart degree in the actual KMS vertex type. -/
theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open KMSAnalytic KMSFourthMoment

universe u

attribute [local instance] mapFintype

section Product
variable {A U B C : Type u}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- Each image-adapted slice in the product proof is one of the actual
uniform mixed slices. The dimension equality exactly matches its weight. -/
theorem productMixedSliceBound_of_uniform (i : ℕ) (L : ℝ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hMixed : UniformMixedBound i L f)
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (T : (A × U) →ₗ[F2] (B × C)) : ProductMixedSliceBound i f T L := by
  intro W D hW hD κ hκ
  have hm := UniformMixedBound.pullback (imageAmbientEquiv (A := A) W D hD)
    (LinearEquiv.refl F2 (B × C)) f hMixed
  have hm' : UniformMixedBound i L (imagePullback W D hD f) := by
    exact hm
  have hr : Module.finrank F2 A + Module.finrank F2 (W × C) ≤ i := by
    rw [Module.finrank_prod, hW]
    omega
  have hπ : Function.Surjective (LinearMap.snd F2 W C) := by
    intro c
    exact ⟨(0, c), rfl⟩
  have hh := hm' A (W × C) C κ hκ (primalA (imageTranslate W D hD T))
    (LinearMap.snd F2 W C) hπ (LinearMap.snd F2 B C) hr
  have hdim : Module.finrank F2 (A × (W × D)) = Module.finrank F2 (A × U) :=
    (imageAmbientEquiv (A := A) W D hD).finrank_eq
  have hexp : (Module.finrank F2 (W × C) + Module.finrank F2 C) *
      Module.finrank F2 (A × (W × D)) =
      (2 * Module.finrank F2 C + (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U) := by
    rw [Module.finrank_prod, hW, hdim]
    congr 1
    omega
  rw [hexp] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_comm]

end Product

section General
variable {E F : Type u}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

omit [FiniteDimensional F2 E] [Fintype E] in
theorem map_leftRange_complement (A U : Submodule F2 E) (h : IsCompl A U) :
    (LinearMap.range (LinearMap.inl F2 A U)).map
      (Submodule.prodEquivOfIsCompl A U h).toLinearMap = A := by
  rw [← LinearMap.range_comp]
  have hc : (Submodule.prodEquivOfIsCompl A U h).toLinearMap.comp
      (LinearMap.inl F2 A U) = A.subtype := by
    apply LinearMap.ext
    intro a
    change (a : E) + (0 : E) = (a : E)
    simp
  rw [hc, Submodule.range_subtype]

/-- The actual hybrid derivative is uniformly bounded whenever all actual
mixed slices are bounded. Both selector subspaces and every affine translate
are arbitrary. -/
theorem hybridDerivative_energy_le_of_uniform
    (i : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hMixed : UniformMixedBound i L f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ L := by
  obtain ⟨U, hU⟩ := A.exists_isCompl
  obtain ⟨C, hC⟩ := B.exists_isCompl
  let a : (A × U) ≃ₗ[F2] E := Submodule.prodEquivOfIsCompl A U hU
  let b : (B × C) ≃ₗ[F2] F := Submodule.prodEquivOfIsCompl B C hC
  let f' : ((A × U) →ₗ[F2] (B × C)) → ℝ :=
    fun M => f (LinearEquiv.arrowCongr a b M)
  let T' : (A × U) →ₗ[F2] (B × C) := (LinearEquiv.arrowCongr a b).symm T
  have hf' : KMSBasisInvariant.IsBasisInvariant f' := basisInvariant_pullback a b f hf
  have hm' : UniformMixedBound i L f' := UniformMixedBound.pullback a b f hMixed
  have hi' : i ≤ Module.finrank F2 (A × U) := by rw [a.finrank_eq]; exact hi
  have hcoord : (𝔼 N, hybridDerivative
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T' (rankComponent i f') N ^ 2) ≤ L := by
    by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
    · exact product_hybrid_energy_le_of_mixed i f' hf' T' L hL hi'
        (productMixedSliceBound_of_uniform i L f' hm' ho T')
    · have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
        (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) T' f' i
        (by rw [product_restriction_order]
            change i < Module.finrank F2 A + Module.finrank F2 C
            omega)
      simpa [hzero] using hL
  have he := hybridDerivative_rankComponent_energy_pullback a b f i
    (LinearMap.range (LinearMap.inl F2 A U))
    (LinearMap.range (LinearMap.inl F2 B C)) T'
  have hA : (LinearMap.range (LinearMap.inl F2 A U)).map a.toLinearMap = A :=
    map_leftRange_complement A U hU
  have hB : (LinearMap.range (LinearMap.inl F2 B C)).map b.toLinearMap = B :=
    map_leftRange_complement B C hC
  have hT : LinearEquiv.arrowCongr a b T' = T :=
    (LinearEquiv.arrowCongr a b).apply_symm_apply T
  rw [hA, hB, hT] at he
  exact he ▸ hcoord

/-- Genuine KMS hybrid energy bound from basis invariance and actual local
squared density. This is the analytic input to the permitted generic fourth
moment inequality; no hybrid estimate is included among its hypotheses. -/
theorem hybridDerivative_energy_bound
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε :=
  hybridDerivative_energy_le_of_uniform i (mixedRankConstant i * ε)
    (mul_nonneg (mixedRankConstant_nonneg i) hε) f hf
    (uniformMixedBound_of_affineDensityBound i ε hε f hf hd) hi A B T

end General
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-! Explicit dimension-independent constants for the KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with another rank-level constant is needed. -/

namespace UniqueGamesTheorem.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

theorem fourthMomentConstant_pos (r : ℕ) : 0 < fourthMomentConstant r := by
  unfold fourthMomentConstant
  positivity

theorem fourthMomentConstant_nonneg (r : ℕ) : 0 ≤ fourthMomentConstant r :=
  (fourthMomentConstant_pos r).le

/-- The closed mixed estimate's literal constant has a quadratic exponent. -/
theorem mixedRankConstant_eq (r : ℕ) :
    mixedRankConstant r = (2 : ℝ) ^ (6 * r * r + 2 * r) := by
  unfold mixedRankConstant mixedStepFactor
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Multiplying by the actual selector-count and A5 constant is exact. -/
theorem a5_mul_mixedRankConstant (r : ℕ) :
    (2 : ℝ) ^ (103 * r * r) * mixedRankConstant r = fourthMomentConstant r := by
  rw [mixedRankConstant_eq, ← pow_add]
  unfold fourthMomentConstant
  congr 1
  ring

theorem fourthMomentConstant_mono {i r : ℕ} (hi : i ≤ r) :
    fourthMomentConstant i ≤ fourthMomentConstant r := by
  unfold fourthMomentConstant
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 109 hi) hi)
    (Nat.mul_le_mul_left 2 hi)

/-- The complete numerical closure, retaining the density and projection
energy factors in the order used by the expansion interface. -/
theorem a5_mixed_bound {i r : ℕ} (hi : i ≤ r) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    (2 : ℝ) ^ (103 * i * i) * (mixedRankConstant i * ε) * η ≤
      fourthMomentConstant r * η * ε := by
  calc
    _ = fourthMomentConstant i * (η * ε) := by
      rw [← a5_mul_mixedRankConstant]
      ring
    _ ≤ fourthMomentConstant r * (η * ε) :=
      mul_le_mul_of_nonneg_right (fourthMomentConstant_mono hi) (mul_nonneg hη hε)
    _ = _ := by ring

end
end UniqueGamesTheorem.Inverse.KMSMomentConstants

end

section

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace UniqueGamesTheorem.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

/-- The upper moment has a constant depending only on the cutoff. Its tuple
budget is 2r and its domain threshold is r, both fixed before the dimensions. -/
theorem lifted_fourth_moment_bound
    (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
    (i : ℕ) (hi : i ≤ r) :
    (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
      fourthMomentConstant r *
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε := by
  have hf := liftedIndicator_basisInvariant S
  have hd : AffineDensityBound i ε (liftedIndicator S) :=
    AffineDensityBound.mono hi ε (liftedIndicator S)
      (KMSBasisComparisonAffineDensity.lifted_affineDensityBound_of_tuple S hS)
  have hidim : i ≤ Module.finrank F2 (Ambient ell) := by
    simpa [KMS.Ambient] using hi.trans hell
  have hm := rankComponent_fourth_moment_le_of_hybrid i (liftedIndicator S)
    (mixedRankConstant i * ε) (mul_nonneg (mixedRankConstant_nonneg i) hε)
    (by
      intro A B T _
      have hh := KMSAnalyticHybridEnergy.hybridDerivative_energy_bound
        i ε hε (liftedIndicator S) hf hd hidim A B T
      have hp : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient ell) (W := Ambient n) = basisMapFintype n ell :=
        Subsingleton.elim _ _
      have hq : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient n) (W := Ambient ell) = basisMapFintype ell n :=
        Subsingleton.elim _ _
      rw [hp, hq] at hh
      exact hh)
  exact hm.trans (a5_mixed_bound hi ε _ hε
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)))

end
end UniqueGamesTheorem.Inverse.KMSMomentTheorem

end

section

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
the fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

namespace UniqueGamesTheorem.Inverse.KMSExpansion
noncomputable section

/-- The KMS expansion theorem with constants independent of both dimensions
and with the ambient threshold chosen after the plane dimension. -/
theorem kms_expansion : KMS.ExpansionPrinciple := by
  apply KMSMomentToExpansion.expansion_of_upperMoments
    KMSMomentConstants.fourthMomentConstant
    KMSMomentConstants.fourthMomentConstant_nonneg
    (fun r => 2 * r) (fun r => r)
  intro r ε hε _hε1 ell hell n S hS i hi
  exact KMSMomentTheorem.lifted_fourth_moment_bound r ε hε ell hell n S hS i hi

end
end UniqueGamesTheorem.Inverse.KMSExpansion

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFiberLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

theorem matrixWeight_probability (ell m : ℕ) :
    IsProbability (matrixWeight (ell := ell) (m := m)) := by
  constructor
  · intro M
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [matrixWeight, hcard]

theorem matrixKernel_nonneg {ell m : ℕ} (M N : Mat ell m) :
    0 ≤ matrixKernel M N := by
  apply Finset.expect_nonneg
  intro a _
  apply Finset.expect_nonneg
  intro l _
  split <;> norm_num

theorem matrixKernel_probability {ell m : ℕ} (M : Mat ell m) :
    IsProbability (matrixKernel M) := by
  refine ⟨matrixKernel_nonneg M, ?_⟩
  unfold matrixKernel
  rw [← Finset.expect_sum_comm]
  have hpoint (a : Vector ell) :
      (∑ N : Mat ell m, 𝔼 l : Vector m,
        if N = M + rankOne a l then (1 : ℝ) else 0) = 1 := by
    rw [← Finset.expect_sum_comm]
    simp
  simp only [hpoint]
  simp

theorem matrixKernel_equality {ell m : ℕ} (f : Mat ell m → Vector ell)
    (M : Mat ell m) :
    (∑ N, matrixKernel M N * if f M = f N then (1 : ℝ) else 0) =
      𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0 := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem equalityAcceptance_eq_kernel {ell m : ℕ} (f : Mat ell m → Vector ell) :
    equalityAcceptance f = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
  calc
    equalityAcceptance f = ∑ M, matrixWeight M *
        (𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then (1 : ℝ) else 0) := by
      unfold equalityAcceptance matrixWeight
      rw [Fintype.expect_eq_sum_div_card]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_comm]
    _ = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
      unfold EqualityFiber.equalityAcceptance
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      convert (matrixKernel_equality f M).symm using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro N _
      by_cases h : f M = f N <;> simp [h]

/-- Positive-mass fibers, with their actual transition flow, are obtained from
the full uniform factor law. This is the first step before conditioning both
factors to be nonzero and passing to Grassmann neighbors. -/
theorem exists_output_fiber {ell m : ℕ} (f : Mat ell m → Vector ell)
    {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y : Vector ell, 0 < EqualityFiber.fiberMass matrixWeight f y ∧
      η ≤ EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
        EqualityFiber.fiberMass matrixWeight f y := by
  apply EqualityFiber.exists_fiber_retention matrixWeight matrixKernel
    (matrixWeight_probability ell m) matrixKernel_probability f
  rwa [← equalityAcceptance_eq_kernel]

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

/-- The slice and the interval intersected with the chart correspond exactly.
The hypothesis states equality of the actual membership predicates. -/
theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

/-- Uniform agreement on a slice is the actual Grassmann fiber density in the
chart-intersected interval.  Empty sets are allowed on both sides of this
identity, with the standard zero-denominator convention. -/
theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode UniqueGamesTheorem.Foundations.Information

theorem matrixKernel_average {ell m : ℕ} (M : Mat ell m) (g : Mat ell m → ℝ) :
    (∑ N, matrixKernel M N * g N) = 𝔼 a, 𝔼 l, g (M + rankOne a l) := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp [ite_mul]

theorem fiberMass_eq_card {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberMass matrixWeight f y =
      ((matrixFiber f y).card : ℝ) / Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberMass
  calc
    _ = ∑ M ∈ matrixFiber f y, matrixWeight M := by
      rw [matrixFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _
      by_cases h : f M = y <;> simp [h]
    _ = _ := by simp [matrixWeight, div_eq_mul_inv]

theorem fiberMass_pos_iff {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    0 < EqualityFiber.fiberMass matrixWeight f y ↔ (matrixFiber f y).Nonempty := by
  rw [fiberMass_eq_card]
  have hcard : (0 : ℝ) < Fintype.card (Mat ell m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]

theorem fiberFlow_eq {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y =
      (∑ M ∈ matrixFiber f y,
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) /
        Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberFlow
  simp_rw [matrixKernel_average]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [matrixFiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : f M = y
  · simp [h, matrixWeight, mul_comm]
  · simp [h]

theorem fiber_retention_eq_factor_average {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
      EqualityFiber.fiberMass matrixWeight f y =
        𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  rw [fiberFlow_eq, fiberMass_eq_card]
  have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : (𝔼 a, 𝔼 l, fiberFactorRetention f y a l) =
      (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
    unfold fiberFactorRetention
    calc
      _ = 𝔼 a, (matrixFiber f y).expect (fun M =>
          𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
      _ = _ := Finset.expect_comm _ _ _
  rw [hswap, Finset.expect_eq_sum_div_card]
  simp [div_div_div_cancel_right₀ hcard]

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

/-- A nonempty actual output fiber whose retention under the full factor law
is at least the original equality acceptance threshold. -/
theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := Shortcode.exists_output_fiber f haccept
  exact ⟨y, (fiberMass_pos_iff f y).mp hy,
    by simpa only [fiber_retention_eq_factor_average] using hret⟩

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFiberConditioning
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

/-- Exact decomposition of a uniform two-factor law with a self-loop on either
zero factor. No nonemptiness is required of the nonzero subtypes. -/
theorem uniform_pair_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Zero A] [Zero B] (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) *
        (𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0}, h p.1.val p.2.val) := by
  let R : ℝ := 𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0},
    h p.1.val p.2.val
  have : Nonempty A := ⟨0⟩
  have : Nonempty B := ⟨0⟩
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNA : (Fintype.card {a : A // a ≠ 0} : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNB : (Fintype.card {b : B // b ≠ 0} : ℝ) =
      (Fintype.card B : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : B => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNZ : (∑ a : {a : A // a ≠ 0}, ∑ b : {b : B // b ≠ 0}, h a.val b.val) =
      (Fintype.card {a : A // a ≠ 0} : ℝ) *
        (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type] using
      (Fintype.card_mul_expect
        (fun p : {a : A // a ≠ 0} × {b : B // b ≠ 0} => h p.1.val p.2.val)).symm
  have hinner (a : A) : (∑ b : B, h a b) =
      1 + ∑ b : {b : B // b ≠ 0}, h a b.val := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, hright]
  have hsum : (∑ a : A, ∑ b : B, h a b) =
      (Fintype.card B : ℝ) + (Fintype.card {a : A // a ≠ 0} : ℝ) +
        (Fintype.card {a : A // a ≠ 0} : ℝ) *
          (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a : A => ∑ b : B, h a b) 0]
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, hNZ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hfull : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) = ∑ a, ∑ b, h a b := by
    calc
      _ = (Fintype.card B : ℝ) *
          ((Fintype.card A : ℝ) * (𝔼 a, 𝔼 b, h a b)) := by ring
      _ = (Fintype.card B : ℝ) * (∑ a, 𝔼 b, h a b) := by
        rw [Fintype.card_mul_expect]
      _ = _ := by
        rw [Finset.mul_sum]
        simp_rw [Fintype.card_mul_expect]
  have hbalance : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ) + (Fintype.card B : ℝ) - 1 +
        ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    rw [hfull, hsum, hNA, hNB]
    ring
  apply mul_left_cancel₀ (mul_ne_zero hA hB)
  rw [hbalance]
  change _ = (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
    ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
      (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) * R)
  field_simp [hA, hB]
  ring

private theorem vector_card_real (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg (ell m : ℕ) :
    0 ≤ ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ := by
  have ha : 0 ≤ ((2 : ℝ) ^ ell)⁻¹ := by positivity
  have hb : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hb1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pow_add, mul_inv]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb1)]

/-- The actual equality test has a nonempty output fiber retaining at least
`η/2` after both factors are conditioned to be nonzero. The displayed order
samples a uniform matrix in that fiber first, as required by the Grassmann
neighbor correspondence. -/
theorem conditioned_output_fiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ ≤ η / 2)
    (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧
      η / 2 ≤ (matrixFiber f y).expect (fun M =>
        𝔼 p : {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0},
          if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := by
  obtain ⟨y, hy, hret⟩ := exists_output_fiber_factor_retention f haccept
  refine ⟨y, hy, ?_⟩
  have hmix := uniform_pair_mixture (fiberFactorRetention f y)
    (fiberFactorRetention_zero_left f y hy) (fiberFactorRetention_zero_right f y hy)
  simp only [vector_card_real, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg ell m) hzero (hmix ▸ hret)
  apply hconditioned.trans
  apply le_of_eq
  unfold fiberFactorRetention
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr (by ext p; simp)
  intro p _
  rfl

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFromGrassmannLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- A common lower bound on both dimensions makes the zero-factor probability
as small as required. This threshold depends only on the acceptance parameter.
-/
theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-!
The exact finite sampling conversion in the v2 shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- Relative density is uniform expectation on the predicate subtype. -/
theorem relativeDensity_filter_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (P : Ω → Prop) [DecidablePred P] :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- Lifting a finite set along an injection preserves its uniform starting
law. No regularity or nonempty-neighbor hypothesis is needed for this step. -/
theorem retention_image {X : Type*} [DecidableEq X] {n ell : ℕ}
    (S : Finset X) (e : X → KMS.Vertex n ell) (he : Function.Injective e) :
    KMS.retention (S.image e) =
      S.expect fun x => KMS.relativeDensity (S.image e) (KMS.neighbors (e x)) := by
  have h : KMS.retention (S.image e) =
      (S.image e).expect fun L => KMS.relativeDensity (S.image e) (KMS.neighbors L) := by
    rw [Finset.expect_eq_sum_div_card]
    rfl
  rw [h]
  exact Finset.expect_image he.injOn

/-- At every starting matrix the full-neighbor retention is half the uniform
nonzero-factor retention. This follows from exact finite bijections and degree
counts; the zero-factor law is handled separately before this theorem. -/
theorem relativeDensity_neighbors_eq_nonzero_average_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M)) =
      (𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  let C := KMS.neighbors (matrixVertex M) ∩ matrixChart ell m
  have hC : C = Finset.univ.filter (fun L : KMS.Vertex (ell + m) ell =>
      KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m) := by
    ext L
    simp [C, KMS.neighbors]
  have hcardC : C.card = (2 ^ ell - 1) * (2 ^ m - 1) := by
    rw [hC]
    have h := card_matrixVertexChartNeighbors M
    simpa only [MatrixVertexChartNeighbors, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hcard : (KMS.neighbors (matrixVertex M)).card = 2 * C.card := by
    rw [hcardC]
    exact card_full_neighbors_twice M
  have hnumerator : liftedFiber f y ∩ C =
      liftedFiber f y ∩ KMS.neighbors (matrixVertex M) :=
    KMS.inter_chart_eq _ _ _ (liftedFiber_subset_chart f y)
  have hhalf : KMS.relativeDensity (liftedFiber f y)
      (KMS.neighbors (matrixVertex M)) =
        KMS.relativeDensity (liftedFiber f y) C / 2 := by
    unfold KMS.relativeDensity
    rw [hcard, ← hnumerator, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (2 : ℝ), div_mul_eq_div_div]
  rw [hhalf]
  congr 1
  rw [hC]
  trans (𝔼 L : MatrixVertexChartNeighbors M,
    if L.val ∈ liftedFiber f y then (1 : ℝ) else 0)
  · exact relativeDensity_filter_eq_expect (liftedFiber f y)
      (fun L => KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m)
  symm
  apply Fintype.expect_equiv (vectorFactorsEquivMatrixVertexChartNeighbors M)
  intro p
  simp only [vectorFactorsEquivMatrixVertexChartNeighbors_apply,
    matrixVertex_mem_liftedFiber]

/-- The exact Grassmann retention of an output fiber is half its retention
under independent uniform nonzero vector factors. Empty fibers and degenerate
dimensions also satisfy this identity with zero-expectation conventions. -/
theorem liftedFiber_retention_eq_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    KMS.retention (liftedFiber f y) =
      (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  unfold liftedFiber
  rw [retention_image _ _ matrixVertex_injective]
  change (𝔼 M ∈ matrixFiber f y,
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M))) = _
  simp_rw [relativeDensity_neighbors_eq_nonzero_average_half]
  exact (Finset.expect_div _ _ _).symm

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- The finite sampling bridge has no expansion or inverse premise. -/
theorem chartFiberRetention : ChartFiberRetention := by
  intro ell m _hell _hm η hη hη1 hzero f haccept
  obtain ⟨y, hnonempty, hretention⟩ :=
    conditioned_output_fiber f hη hη1 hzero haccept
  refine ⟨y, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hnonempty
  · rw [liftedFiber_retention_eq_half]
    have h : η / 2 ≤ (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := hretention
    linarith

/-- Conditional Grassmann-to-matrix implication, preserving all quantifiers
and the affine target. KMS expansion is the sole remaining displayed premise.
-/
theorem inversePrinciple_of_expansion (hKMS : KMS.ExpansionPrinciple) :
    Shortcode.InversePrinciple :=
  inversePrinciple_of_expansion_and_chart hKMS chartFiberRetention

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The Grassmann theorem, chart retention, zero-factor correction,
output-fiber extraction, and affine row/column slice construction yield the
unconditional affine matrix inverse theorem. -/

namespace UniqueGamesTheorem.Inverse.ShortcodeTheorem
noncomputable section

/-- Full-factor sampling includes zero. The conclusion retains an affine
intercept and applies to arbitrary matrix labelings without a folding premise. -/
theorem inversePrinciple_oai : Shortcode.InversePrinciple :=
  ShortcodeFromGrassmann.inversePrinciple_of_expansion KMSExpansion.kms_expansion

end
end UniqueGamesTheorem.Inverse.ShortcodeTheorem

end

end OAI
end

theorem solution : type_of% @OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple_oai := @OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple_oai
