-- Prove2me | solution 1 for OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:07:31.402349+00:00
-- url     : https://prove2.me/submissions/83192071-1c5e-408a-9ccb-7320e980de60

import Mathlib
import Definitions.Def_OAIQ085D027
import Theorems.Thm_OAI_DFVSGames_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
import Theorems.Thm_OAI_DFVSGames_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_Deletion
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Fourier.MatrixRestrictions

open DFVSGames.Integration.BinaryLinear
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

end DFVSGames.Fourier.MatrixRestrictions


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
attribute [-instance] _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear

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

end DFVSGames.Fourier.MatrixCharacters
end

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open DFVSGames.Fourier.MatrixCharacters

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

end DFVSGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.CompressionCount

open Module
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C]

theorem natCard_linearMap : Nat.card (U →ₗ[F2] C) =
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

end DFVSGames.Appendix.CompressionCount

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_StageData
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.Restriction

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in

theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (DFVSGames.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair DFVSGames.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in

theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, DFVSGames.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : DFVSGames.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    DFVSGames.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (DFVSGames.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : DFVSGames.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + DFVSGames.Fourier.MatrixRestrictions.embed A B N)]
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

end DFVSGames.Appendix.Restriction
end

namespace DFVSGames.Appendix.Level.LinearRank

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

end DFVSGames.Appendix.Level.LinearRank

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CoordinateTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem span_generators (S : Submodule K V) (k : ℕ) (h : finrank K S = k) :
    Submodule.span K (Set.range (generators S k h)) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  change Submodule.span K (Set.range (S.subtype ∘ b)) = S
  rw [Set.range_comp, Submodule.span_image, b.span_eq]
  simp

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

theorem card_subspaces_rank_le_field_power [Finite K] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤
      Nat.card K ^ (finrank K V * k) := by
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  have h := card_subspaces_rank_le (K := K) (V := V) k
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_mul] at h

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

end DFVSGames.Appendix.SubspaceCounting

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Derivatives
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.Derivatives
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
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

end DFVSGames.Appendix.Derivatives
end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives

section General

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

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

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier

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

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

end
end DFVSGames.Inverse.KMSAnalytic

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open DFVSGames.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
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

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

theorem productFrequencyEquiv_finrank
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Module.finrank F2 (productFrequencyEquiv Z).range = Module.finrank F2 Z.range := by
  change Module.finrank F2
    (((quotientRightEquiv (R := F2) (A := A) (U := U)).toLinearMap.comp Z).comp
      (leftRangeEquiv (R := F2) (B := B) (C := C)).toLinearMap).range = _
  rw [LinearEquiv.range_comp, LinearMap.range_comp]
  exact (quotientRightEquiv (R := F2) (A := A) (U := U)).finrank_map_eq Z.range

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_A4IndexCount
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.RestrictionTransport

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixRestrictions

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

end SameRange

end DFVSGames.Appendix.RestrictionTransport

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyImageSplit
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem imageCoordinates_frequency {X : Type*} [AddCommGroup X] [Module K X]
    (W D : Submodule K V) (h : IsCompl W D) (z : X →ₗ[K] W) :
    (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) =
      z.prod (0 : X →ₗ[K] D) := by
  apply LinearMap.ext
  intro x
  exact imageCoordinates_subtype W D h (z x)

theorem imageCoordinates_finrank [FiniteDimensional K V]
    (W D : Submodule K V) (h : IsCompl W D) :
    Module.finrank K W + Module.finrank K D = Module.finrank K V := by
  simpa only [Module.finrank_prod] using (Submodule.prodEquivOfIsCompl W D h).finrank_eq

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open DFVSGames.Appendix

private theorem psi_split_inline_KMSAnalyticHybridCoordinatesConditions {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (b : B) (c : C) :
    p.psi (b, c) = z b + p.psi (0, c) := by
  have hleft : p.psi (b, 0) = z b :=
    congrArg (fun L : B →ₗ[R] W => L b) p.psi_left
  calc
    p.psi (b, c) = p.psi ((b, 0) + (0, c)) := by simp
    _ = p.psi (b, 0) + p.psi (0, c) := p.psi.map_add _ _
    _ = z b + p.psi (0, c) := by rw [hleft]

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
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, neg_add_cancel]
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
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, sub_add_cancel]
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

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

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

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in

theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in

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
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

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
end DFVSGames.Inverse.KMSKernelOrbits

namespace DFVSGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

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
end DFVSGames.Inverse.KMSBasisInvariant

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NaturalTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.NaturalTransport
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives DFVSGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

attribute [local instance] OAI.DFVSGames.Appendix.NaturalTransport.naturalTransportQuotientFinite
attribute [local instance] OAI.DFVSGames.Appendix.NaturalTransport.naturalTransportCompressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rank_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F') (L : E →ₗ[F2] F) :
    Module.finrank F2 (LinearEquiv.arrowCongr a b L).range =
      Module.finrank F2 L.range := by
  have hh : LinearEquiv.arrowCongr a b L =
      (b.toLinearMap.comp L).comp a.symm.toLinearMap := by
    ext x
    rfl
  rw [hh, LinearEquiv.range_comp, LinearMap.range_comp]
  exact b.finrank_map_eq L.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem trace_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTracePair (LinearEquiv.arrowCongr a b M) (LinearEquiv.arrowCongr b a Z) =
      linearTracePair M Z := by
  unfold linearTracePair
  rw [← LinearEquiv.arrowCongr_comp]
  exact LinearMap.trace_conj' (M.comp Z) b

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem character_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTraceCharacter (LinearEquiv.arrowCongr b a Z) (LinearEquiv.arrowCongr a b M) =
      linearTraceCharacter Z M := by
  simp only [linearTraceCharacter_apply, trace_arrowCongr]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
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

end DFVSGames.Appendix.NaturalTransport
end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix
open DFVSGames.Inverse.KMSAnalytic

variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']

private theorem mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport (a : E ≃ₗ[F2] E')
    (A : Submodule F2 E) (x : E) :
    a x ∈ A.map a.toLinearMap ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp h
    exact (a.injective heq) ▸ hy
  · intro h
    exact Submodule.mem_map.mpr ⟨x, h, rfl⟩

theorem hybrid_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (S : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F) :
    LinearIdentities.Hybrid (LinearEquiv.arrowCongr b a S)
      (A.map a.toLinearMap) (B.map b.toLinearMap) ↔
      LinearIdentities.Hybrid S A B := by
  constructor
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := hr ((mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A x).mpr hx)
      refine ⟨b.symm y, a.injective hy⟩
    · intro y hy
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B y).mp
      apply hk
      change (LinearEquiv.arrowCongr b a S) (b y) ∈ A.map a.toLinearMap
      simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
        using (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A (S y)).mpr hy
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
      have hy' : S (b.symm y) ∈ A := (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A _).mp hy
      have hm := (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mpr (hk hy')
      simpa only [LinearEquiv.apply_symm_apply] using hm

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
      have heq := hk ((mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport a A x).mpr hx)
      have heq' : b (M x) = b 0 := by
        simpa only [LinearMap.mem_ker, LinearEquiv.arrowCongr_apply,
          LinearEquiv.symm_apply_apply, map_zero] using heq
      exact b.injective heq'
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mp
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
      apply (mem_map_equiv_iff_inline_KMSAnalyticHybridEnergyTransport b B _).mpr
      exact hr ⟨a.symm x, rfl⟩

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

theorem hybridProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F) :
    hybridProjector A B (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [hybridProjector, linearCoeff_spectralProjector,
    NaturalTransport.linearCoeff_pullback, hybrid_arrowCongr]

theorem rankComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ) :
    rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankComponent i f (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankComponent, coeff_component,
    NaturalTransport.linearCoeff_pullback, NaturalTransport.rank_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, DFVSGames.Fourier.MatrixRestrictions.translate, hybridProjector_pullback, map_add]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B))
    (embedding (A.map a.toLinearMap) (B.map b.toLinearMap))
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective A B))
    (embed_injective _ _) (hybrid_embedding_range a b A B)
    (fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
      (LinearEquiv.arrowCongr a b T + M) ^ 2)

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

noncomputable section
namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSKernelOrbitsFourier

open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant
open DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]

theorem coefficient_eq_of_ker_eq (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (S T : F →ₗ[F2] E) (hker : S.ker = T.ker) :
    linearCoeff f S = linearCoeff f T := by
  obtain ⟨g, hg⟩ := exists_postcomp_equiv_of_ker_eq S T hker
  have h := coefficient_change f hf g S
  rw [hg] at h
  exact h.symm

end
end DFVSGames.Inverse.KMSKernelOrbitsFourier

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    smallCoeff ι f = smallCoeff κ f :=
  smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f
    (KMSKernelOrbitsFourier.coefficient_eq_of_ker_eq f hf)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open KMSAnalyticHybridCoordinates KMSAnalytic

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

variable [Module F2 A] [Module F2 W] [Module F2 D] [Module F2 B] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]

omit [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))] in
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

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergyPhase

noncomputable section
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalyticHybridCoordinates

section Product

variable {H U V : Type*}
  [AddCommGroup H] [Module F2 H]
  [AddCommGroup U] [Module F2 U]
  [AddCommGroup V] [Module F2 V]

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

theorem character_prod (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    linearTraceCharacter (S.prod T) X =
      linearTraceCharacter S (X.comp (LinearMap.inl F2 U V)) *
      linearTraceCharacter T (X.comp (LinearMap.inr F2 U V)) := by
  simp only [linearTraceCharacter_apply, tracePair_prod, binarySign_add]

theorem character_prod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (X : (U × V) →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) X).re =
      (linearTraceCharacter S (X.comp (LinearMap.inl F2 U V))).re *
      (linearTraceCharacter T (X.comp (LinearMap.inr F2 U V))).re := by
  rw [character_prod, Complex.mul_re]
  simp [linearTraceCharacter_apply]

theorem character_prod_coprod_re (S : H →ₗ[F2] U) (T : H →ₗ[F2] V)
    (a : U →ₗ[F2] H) (X : V →ₗ[F2] H) :
    (linearTraceCharacter (S.prod T) (a.coprod X)).re =
      (linearTraceCharacter S a).re * (linearTraceCharacter T X).re := by
  simpa only [LinearMap.coprod_inl, LinearMap.coprod_inr] using
    character_prod_re S T (a.coprod X)

end Product

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

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

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergyPhase

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentMixedRestriction
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment
open DFVSGames.Inverse.KMSAnalyticHybridEnergyPhase

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

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

theorem coeff_partialRestrict
    (h : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (T : F →ₗ[F2] I) :
    linearCoeff (partialRestrict h a) T =
      ∑ alpha : F →ₗ[F2] A,
        linearCoeff h (alpha.prod T) * (linearTraceCharacter alpha a).re := by
  rw [partialRestrict_eq_synthesis, coeff_synthesis]

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
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

omit [Fintype (B × C →ₗ[F2] W)] [Fintype (C →ₗ[F2] D)] in

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
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical

theorem phase_weighted_sum_sq_le {Ψ : Type*} (s : Finset Ψ)
    (b H : Ψ → ℝ) (hb : ∀ ψ ∈ s, b ψ ^ 2 ≤ 1) :
    (∑ ψ ∈ s, b ψ * H ψ) ^ 2 ≤ (s.card : ℝ) * ∑ ψ ∈ s, H ψ ^ 2 := by
  have hphase : (∑ ψ ∈ s, b ψ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _ψ ∈ s, (1 : ℝ) := Finset.sum_le_sum hb
      _ = _ := by simp
  exact (Finset.sum_mul_sq_le_sq_mul_sq s b H).trans
    (mul_le_mul_of_nonneg_right hphase (Finset.sum_nonneg (fun ψ _ => sq_nonneg (H ψ))))

theorem phase_sum_sq_le_card_sq {V : Type*} [Fintype V]
    (a : V → ℝ) (ha : ∀ v, a v ^ 2 ≤ 1) :
    (∑ v, a v) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := phase_weighted_sum_sq_le Finset.univ a (fun _ => (1 : ℝ))
    (fun v _ => ha v)
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, pow_two] using h

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
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix

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

theorem card_linearMap_eq [Fintype (C →ₗ[F2] D)] :
    Fintype.card (C →ₗ[F2] D) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 D) := by
  simpa only [Nat.card_eq_fintype_card] using
    (CompressionCount.natCard_linearMap (U := C) (C := D))

end Injections

section Images

variable {U : Type*} [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]

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

theorem count_exponent_le (a b q d : ℕ) :
    q * (q + d) + (b * d) * 2 + b * q ≤ (2 * b + q) * (a + q + d) := by
  calc
    _ ≤ q * (q + d) + (b * d) * 2 + b * q + ((2 * b + q) * a + b * q) :=
      Nat.le_add_right _ _
    _ = _ := by ring

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
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSFourthMoment

section Slice

variable {F W C : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup W] [Module F2 W]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C]
  [Fintype ((W × C) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (W × C))]
  [Fintype (F →ₗ[F2] W)]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 W] [FiniteDimensional F2 C] in

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

variable {R B W C M : Type*} [Ring R]
  [AddCommGroup B] [Module R B]
  [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]
  [AddCommMonoid M] [Fintype ((B × C) →ₗ[R] W)]

theorem sum_extensions_eq_filter (z : B →ₗ[R] W)
    [Fintype (Extension (C := C) z)] (H : ((B × C) →ₗ[R] W) → M) :
    (∑ ψ : Extension (C := C) z, H ψ.val) =
      ∑ ψ with ψ.comp (LinearMap.inl R B C) = z, H ψ := by
  exact (Finset.sum_subtype
    (p := fun ψ : (B × C) →ₗ[R] W => ψ.comp (LinearMap.inl R B C) = z)
    (Finset.univ.filter (fun ψ : (B × C) →ₗ[R] W =>
      ψ.comp (LinearMap.inl R B C) = z)) (by simp) H).symm

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
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

omit [FiniteDimensional F2 W] [FiniteDimensional F2 B] [FiniteDimensional F2 C] [Fintype (B × C →ₗ[F2] W)] [Fintype (B × C →ₗ[F2] C)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)] [Fintype (W × C →ₗ[F2] B × C)] [Fintype (B × C →ₗ[F2] W × C)] in
theorem traceCharacter_re_sq (S : (B × C) →ₗ[F2] W) (X : W →ₗ[F2] (B × C)) :
    (linearTraceCharacter S X).re ^ 2 = 1 := by
  by_cases h : linearTracePair X S = 0 <;>
    simp [linearTraceCharacter_apply, binarySign, h]

omit [Fintype (B × C →ₗ[F2] C)] in

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

omit [Fintype (B × C →ₗ[F2] C)] in
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
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentZoomTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open DFVSGames.Inverse.KMSAnalytic

variable {E F E' F' I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]

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

private theorem surjective_comp_symm_iff_inline_KMSAnalyticHybridEnergyTransportSmall (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
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

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in

theorem smallCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff ι (fun M => f (LinearEquiv.arrowCongr a b M)) T =
      smallCoeff (a.toLinearMap.comp ι) f (T.comp b.symm.toLinearMap) := by
  have hc : LinearEquiv.arrowCongr b a (ι.comp T) =
      (a.toLinearMap.comp ι).comp (T.comp b.symm.toLinearMap) := by
    ext y
    rfl
  unfold smallCoeff
  rw [surjective_comp_symm_iff_inline_KMSAnalyticHybridEnergyTransportSmall, NaturalTransport.linearCoeff_pullback, hc]

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

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
end DFVSGames.Inverse.KMSAnalytic

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_r2d06d3_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

attribute [local instance] OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.mapFintype
attribute [local instance] OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.submoduleFintype
theorem productFiberCoefficient_imageTransport
    (W D : Submodule F2 U) (hD : IsCompl W D) (z : B →ₗ[F2] W)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ)
    (hi : Module.finrank F2 (A × (W × C)) = i) :
    productFiberCoefficient i f T (W.subtype.comp z) =
      adaptedFiberCoefficient z (imagePullback W D hD f) (imageTranslate W D hD T) := by
  simpa only [hi, productFiberCoefficient] using
    image_fiber_coefficient_transport W D hD z f T

theorem product_energy_eq_filter_coefficient
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] U with
        Module.finrank F2 Z.range = i - (Module.finrank F2 A + Module.finrank F2 C),
        productFiberCoefficient i f T Z ^ 2 := by
  have h := hybridDerivative_rankComponent_product_energy_eq_rank_fibers T f i
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold productFiberCoefficient
  congr 1
  ext Z
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> rfl

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

variable {A I J F F' : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup F] [Module F2 F]
  [AddCommGroup F'] [Module F2 F']

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

private theorem arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed (b : F ≃ₗ[F2] F') (X : I →ₗ[F2] F) :
    LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
  ext x
  rfl

private theorem arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
  ext x
  rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)] in

theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed] using
    NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b g T

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
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
  simp only [LinearEquiv.coe_toEquiv, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed,
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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticSmallTransport
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticCodomainTransport
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

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
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyMixed
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

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
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open DFVSGames.Fourier.MatrixRestrictions
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

theorem hybridDerivative_energy_bound
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε :=
  hybridDerivative_energy_le_of_uniform i (mixedRankConstant i * ε)
    (mul_nonneg (mixedRankConstant_nonneg i) hε) f hf
    (uniformMixedBound_of_affineDensityBound i ε hε f hf hd) hi A B T

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSMomentConstants
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

theorem mixedRankConstant_eq (r : ℕ) :
    mixedRankConstant r = (2 : ℝ) ^ (6 * r * r + 2 * r) := by
  unfold mixedRankConstant mixedStepFactor
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

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
end DFVSGames.Inverse.KMSMomentConstants

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

theorem inLift_comp_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (g : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) (X : BasisMap n ell) :
    InLift S (X.comp g.toLinearMap) ↔ InLift S X := by
  unfold InLift
  rw [LinearMap.range_comp_of_range_eq_top X g.range]

theorem liftedIndicator_basisInvariant {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    KMSBasisInvariant.IsBasisInvariant (liftedIndicator S) := by
  intro g X
  simp only [liftedIndicator, inLift_comp_iff]

end
end DFVSGames.Inverse.KMSBasisComparison

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonPseudorandom
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

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

theorem restrictedLiftDensity_eq_expect (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    restrictedLiftDensity S Q W =
      𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z)) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [liftedIndicator, inLift_tupleMap_iff]
  rw [Finset.sum_boole]
  simp only [restrictedLiftDensity, Nat.card_eq_fintype_card, Fintype.card_subtype]

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSAffineRestrictionComplement

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F]

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

end DFVSGames.Inverse.KMSAffineRestrictionComplement

namespace DFVSGames.Inverse.KMSAffineRestrictionSplit

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

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

theorem expect_restrict [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (T : E →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter D W, restrict f D W T A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (translate D W T (join D U E₀ W hDU hc B C)) :=
  expect_join D U E₀ W hDU hc (restrict f D W T)

end
end DFVSGames.Inverse.KMSAffineRestrictionSplit

namespace DFVSGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open DFVSGames.Fourier.MatrixRestrictions
open KMSAffineRestrictionSplit

variable {n ell q t : ℕ}

theorem translate_join_eq_constr
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0)
    (B : Parameter (localVanishing D U) W) (C : E0 →ₗ[F2] W) :
    DFVSGames.Fourier.MatrixRestrictions.translate D W T (join D U E0 W hDU hc B C) =
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
        DFVSGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_left]
  | inr i =>
      simp only [complementBasis_inr, joinedTuple, Sum.elim_inr,
        DFVSGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_right]
      rfl

end
end DFVSGames.Inverse.KMSAffineRestriction

namespace DFVSGames.Inverse.KMSAffineRestrictionPresentation

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

theorem expect_presentation [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L))) =
      𝔼 A : Parameter L.ker J.range, restrict f L.ker J.range T A := by
  apply Fintype.expect_equiv (parameterEquiv L hL J hJ).toEquiv
  intro X
  exact congrArg f (translate_parameterEquiv L hL J hJ T X).symm

theorem expect_presentation_sq [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) =
      𝔼 A : Parameter L.ker J.range, (restrict f L.ker J.range T A) ^ 2 :=
  expect_presentation L hL J hJ T (fun X => f X ^ 2)

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

theorem order_le_of_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) (r : ℕ)
    (h : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r) :
    order L.ker J.range ≤ r := by
  have hdim := order_add_dimensions L hL J hJ
  omega

end
end DFVSGames.Inverse.KMSAffineRestrictionPresentation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_KMSMomentScalar
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparisonAffineDensity

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAffineRestriction KMSAffineRestrictionSplit
open DFVSGames.Fourier.MatrixRestrictions

variable {n ell q t r : ℕ} {ε : ℝ}

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
end DFVSGames.Inverse.KMSBasisComparisonAffineDensity

namespace DFVSGames.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

theorem lifted_fourth_moment_bound_oai
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
      first | exact hh | (convert hh; all_goals first | rfl | exact Subsingleton.elim _ _))
  exact hm.trans (a5_mixed_bound hi ε _ hε
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)))

end
end DFVSGames.Inverse.KMSMomentTheorem

end OAI
end

theorem solution : type_of% @OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound_oai := @OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound_oai
