-- Prove2me | solution 1 for OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:58:31.667893+00:00
-- url     : https://prove2.me/submissions/20f60927-5b84-4896-b252-f06716a51b99

import Mathlib
import Definitions.Def_OAIQ087A008
import Definitions.Def_OAIQ087A009
import Definitions.Def_OAIQ087A012
import Theorems.Thm_OAI_MaxCutGames_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
import Theorems.Thm_OAI_MaxCutGames_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_KMSKernelOrbits
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace MaxCutGames.Inverse.KMSKernelOrbits

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
end MaxCutGames.Inverse.KMSKernelOrbits

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixCharacters
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear

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

end MaxCutGames.Fourier.MatrixCharacters
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open MaxCutGames.Fourier.MatrixCharacters

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

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

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
end MaxCutGames.Inverse.KMSBasisInvariant

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_KMSKernelOrbitsFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basis-invariant matrix functions have constant actual Fourier coefficients
on kernel fibers. This uses ambient automorphism transitivity proved from the
first isomorphism theorem, followed by the exact change-of-basis identity for
the normalized trace-character transform. -/

namespace MaxCutGames.Inverse.KMSKernelOrbitsFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant
open MaxCutGames.Inverse.KMSKernelOrbits

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
end MaxCutGames.Inverse.KMSKernelOrbitsFourier

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Deletion
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Fourier.MatrixRestrictions

open MaxCutGames.Integration.BinaryLinear
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

end MaxCutGames.Fourier.MatrixRestrictions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RankAdditivity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace MaxCutGames.Appendix.CompressionCount

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

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

end MaxCutGames.Appendix.CompressionCount

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Restriction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.Restriction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (MaxCutGames.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair MaxCutGames.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, MaxCutGames.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    MaxCutGames.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N)]
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

end MaxCutGames.Appendix.Restriction
end

section

namespace MaxCutGames.Appendix.Level.LinearRank

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

end MaxCutGames.Appendix.Level.LinearRank
end

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CoordinateTransport
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

/-!
# Energy after merging a bounded number of frequencies

This finite ordered-ring theorem supplies the Cauchy–Schwarz step in (A.10).
Its fiber-cardinality hypothesis is explicit and remains to be instantiated by
the general rank-additive compression count of Lemma A.2.
-/

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace MaxCutGames.Appendix.SubspaceCounting

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

end MaxCutGames.Appendix.SubspaceCounting

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Derivatives
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.Derivatives
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
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

end MaxCutGames.Appendix.Derivatives

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives

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

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier identities.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier

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

end MaxCutGames.Inverse.KMSAnalytic

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open MaxCutGames.Inverse.KMSAnalytic

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

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
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

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A4IndexCount
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace MaxCutGames.Appendix.RestrictionTransport

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixRestrictions

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

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

end SameRange

end MaxCutGames.Appendix.RestrictionTransport

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageSplit
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open MaxCutGames.Appendix

private theorem psi_split_inline_KMSAnalyticHybridCoordinatesConditions {z : B →ₗ[R] W}
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

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

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

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier

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
/-- Composition with an injection preserves the actual kernel. -/
theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
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
end MaxCutGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticSmallInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier

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
end MaxCutGames.Inverse.KMSAnalytic

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

omit [Fintype (A × W × C →ₗ[F2] B × C)] [Fintype (B × C →ₗ[F2] A × W × C)] in
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

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergyPhase

noncomputable section
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

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

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergyPhase

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentMixedRestriction
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact partial restrictions in product coordinates. Translating the full map
shifts both the fixed and free coordinates. The latter shift preserves every
actual Fourier slice energy, so finite differences of translated functions
cost only the finite Cauchy factor already present before restriction.
-/

/-!
Exact Fourier merging after fixing a primal product block. The coefficient
uses normalized expectation, while the merged frequency sum is unnormalized.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment
open MaxCutGames.Inverse.KMSAnalyticHybridEnergyPhase

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

/-! The actual Fourier coefficient of an adapted hybrid fiber factors into
the complementary-block phase and a mixed partial-restriction coefficient. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

/-!
# Cauchy--Schwarz for the hybrid coefficient fibers

The complementary-vector phase sum contributes the square of its number
of terms. Merging extensions with the same restriction contributes their
largest fiber size. Both factors come from finite Cauchy--Schwarz; summing
the disjoint fibers preserves the unnormalized coefficient energy.
-/

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

/-!
# Cardinality budgets for hybrid coefficient fibers

Extensions are counted by an exact equivalence with linear maps on the
complement. Injective complementary maps are bounded by all linear maps.
Images of fixed dimension are counted using the proved basis encoding of
subspaces. Their combined exponent fits the mixed Fourier denominator.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix

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

/-!
Exact sums on fixed Fourier slices and compressed-frequency extension fibers.
Fixing the last frequency block leaves each first block exactly once, and
passing between an extension subtype and a filtered sum changes no weights.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSFourthMoment

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

end

/-! A single compressed-image contribution is controlled by an actual mixed
slice energy. The only losses are the explicit finite coordinate counts. -/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

omit [Fintype (B × C →ₗ[F2] C)] in
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
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OperatorNorm
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace MaxCutGames.Appendix.NaturalTransport
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

attribute [local instance] OAI.MaxCutGames.Appendix.NaturalTransport.instFiniteQuotientSubmoduleF2
attribute [local instance] OAI.MaxCutGames.Appendix.NaturalTransport.instFintypeLinearMapF2IdSubtypeMemSubmoduleQuotientOfFinite
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

end MaxCutGames.Appendix.NaturalTransport

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine MaxCutGames.Fourier.MatrixRestrictions.translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic

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
quotient restriction, and affine MaxCutGames.Fourier.MatrixRestrictions.translate transported together. -/
theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, MaxCutGames.Fourier.MatrixRestrictions.translate, hybridProjector_pullback, map_add]
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageTransportCore
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The exact transport into the actual adapted fiber used by the mixed bound. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Small-component pullback under ambient coordinate equivalences

The small domain stays fixed while the ambient embedding and primal codomain
are transported together. These are exact identities for the actual Fourier
coefficients and synthesized functions; they require no analytic estimate.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic

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

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
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
  rw [surjective_comp_symm_iff_inline_KMSAnalyticHybridEnergyTransportSmall, NaturalTransport.linearCoeff_pullback, hc]

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

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
end MaxCutGames.Inverse.KMSAnalytic

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_r4ee2df_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

attribute [local instance] OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.mapFintype
attribute [local instance] OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.submoduleFintype
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

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

omit [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)]
  [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Exact coefficient transport for a function pulled back only in its
primal codomain. -/
theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed] using
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
  simp only [LinearEquiv.coe_toEquiv, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed,
    linearCoeff_postcomp_equiv, hp]

variable {E E' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 A]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype ((A × I) →ₗ[F2] F')] [Fintype (F' →ₗ[F2] (A × I))]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentPointShuffle
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

/-!
Exact coordinate alignment for the mixed-norm induction. A chosen fixed point
is moved to the last small coordinate, and an actual ambient complement makes
its injection a pointLift. Small-component transport identifies the resulting
functions exactly, so the next recursive estimate concerns the same law.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

/-!
The actual mixed-energy induction step of KMS Lemma 3.20. Previously fixed
points form A, the remaining Fourier coordinates form I, and the new fixed
point is last. The dependent graphs translate the old fixed points, which
is why the inductive bound must hold uniformly over those prescribed values.
-/

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

theorem mixedStepFactor_nonneg (R : ℕ) : 0 ≤ mixedStepFactor R := by
  unfold mixedStepFactor
  positivity

end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentZoomInvariant
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Point restrictions inherit basis invariance in the remaining coordinates.
Translations split into a shift of the fixed point and a translation of the
remaining matrix; both identities are exact, with no probability loss.
-/

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic

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

/-!
The local-density predicate is invariant under an ambient basis presentation
and consumes exactly the output codimension under a homogeneous restriction.
These are changes of the actual sampled affine maps, without an estimate loss.
-/

/-!
The complete fixed-point induction from the fixed-character base estimate.
The base is kept as a named mathematical input here so its separate character
induction can be assembled independently. This intermediate theorem is not
the final KMS endpoint: its base must be discharged by the proved homogeneous
character estimate. All point-recursion, basis transport and local-density
steps are established within this theorem's proof.
-/

end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Exact orbit grouping for KMS Fourier norms

The frequency fibers are finite sets with their real cardinality as the
multiplicity. No probability normalization or orbit-size estimate is assumed
by the grouping identity. The later kernel-orbit count supplies these sizes
for the actual binary linear maps.
-/

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticRestrictionTransport
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate and budget transport for the genuine homogeneous character
induction. These statements only change presentations of the actual local
squared-density hypothesis and prescribed Fourier sums. -/

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Inverse.KMSAnalytic

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
end MaxCutGames.Inverse.KMSFourthMoment

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

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
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

noncomputable section
namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open MaxCutGames.Fourier.MatrixRestrictions
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
  convert hh using 1 <;> first | rfl | simp only [mul_comm]

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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentConstants
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit dimension-independent constants for the new KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with an earlier rank-level constant is needed. -/

namespace MaxCutGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

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
end MaxCutGames.Inverse.KMSMomentConstants

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

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
end MaxCutGames.Inverse.KMSBasisComparison

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonPseudorandomTupleMap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

namespace MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

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
end MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

/-!
The KMS restricted-tuple bound in any adapted basis, followed by an exact
uniform affine translation of the free coordinates. No generic rank-level
inequality is used: this is a change of coordinates for the actual lift.
-/

/-!
Complements adapted to an affine restriction. The prescribed directions are
contained in a small summand, and the complementary directions are mapped into
the prescribed target subspace. This is ordinary finite-dimensional geometry;
no Fourier inequality or pseudorandomness hypothesis is used.
-/

namespace MaxCutGames.Inverse.KMSAffineRestrictionComplement

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

end MaxCutGames.Inverse.KMSAffineRestrictionComplement

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

namespace MaxCutGames.Inverse.KMSAffineRestrictionSplit

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions
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
end MaxCutGames.Inverse.KMSAffineRestrictionSplit

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace MaxCutGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open MaxCutGames.Fourier.MatrixRestrictions
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
    MaxCutGames.Fourier.MatrixRestrictions.translate D W T (join D U E0 W hDU hc B C) =
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
        MaxCutGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_left]
  | inr i =>
      simp only [complementBasis_inr, joinedTuple, Sum.elim_inr,
        MaxCutGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_right]
      rfl

end
end MaxCutGames.Inverse.KMSAffineRestriction

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

namespace MaxCutGames.Inverse.KMSAffineRestrictionPresentation

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions
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
end MaxCutGames.Inverse.KMSAffineRestrictionPresentation

/-! The actual Grassmann local-density hypothesis discharges the affine
squared-density predicate used by the new KMS point/character inductions. -/

/-!
# Tuple pseudorandomness controls the actual affine squared density

This is the input conversion needed by the ordered-basis expansion theorem.
It starts directly from its tuple pseudorandomness assumption. All affine
intercepts and the full uniform parameter law are preserved by the checked
adapted-complement, split, and presentation equivalences.
-/

namespace MaxCutGames.Inverse.KMSBasisComparisonAffineDensity

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAffineRestriction KMSAffineRestrictionSplit
open MaxCutGames.Fourier.MatrixRestrictions

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
end MaxCutGames.Inverse.KMSBasisComparisonAffineDensity

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentTheorem
attribute [-instance] _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace MaxCutGames.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

/-- The upper moment has a constant depending only on the cutoff. Its tuple
budget is 2r and its domain threshold is r, both fixed before the dimensions. -/
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
      exact hh)
  exact hm.trans (a5_mixed_bound hi ε _ hε
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)))

end
end MaxCutGames.Inverse.KMSMomentTheorem

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

end OAI
end

theorem solution : type_of% @OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound_oai := @OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound_oai
