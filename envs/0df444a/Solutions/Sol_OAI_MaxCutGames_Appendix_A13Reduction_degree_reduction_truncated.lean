-- Prove2me | solution 1 for OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:52:25.759174+00:00
-- url     : https://prove2.me/submissions/310f8233-81df-4fa0-bf00-af8c5149b006

import Mathlib
import Definitions.Def_OAIQ087A009
import Definitions.Def_OAIQ087A012

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
-- module Solutions.OAIQ087_MC.MaxCut_Games_RankAdditivity
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

namespace MaxCutGames.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

end MaxCutGames.Appendix.RankAdditivity

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

omit [FiniteDimensional F2 C] in
theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

omit [FiniteDimensional F2 C] in
theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

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
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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
namespace MaxCutGames.Appendix.DegreeCover

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

private theorem binary_cross_inline_DegreeCover {a b c d : V} (h : a + b = c + d) : c + a = d + b := by
  calc
    c + a = (c + a) + (b + b) := by simp
    _ = c + (a + b) + b := by abel
    _ = c + (c + d) + b := by rw [h]
    _ = (c + c) + (d + b) := by abel
    _ = d + b := by simp

theorem exists_cover_component (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R : W →ₗ[F2] V,
      (∀ w ∈ LinearMap.ker Z, R w = Y w) ∧
      (∀ w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z), R w = 0) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y := by
  have cov : LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) = ⊤ := by
    simpa only [sup_assoc, sup_comm, sup_left_comm] using cover
  have compatible : ∀ w ∈ LinearMap.ker Z,
      w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z) → Y w = 0 := by
    intro w hw hz
    change Z w = 0 at hw
    rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, hab⟩
    change Y a = 0 at ha
    change (Y + Z) b = 0 at hb
    have hYb : Y b = Z b := by
      have h := congrArg (fun v : V => v + Z b) hb
      simpa only [LinearMap.add_apply, add_assoc, binary_add_self, add_zero, zero_add] using h
    have hYw : Y w = Z b := by rw [← hab, map_add, ha, zero_add, hYb]
    have hmem : Y w ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z :=
      ⟨⟨⟨w, by simp only [LinearMap.add_apply, hw, add_zero]⟩, ⟨w, rfl⟩⟩,
        ⟨b, hYw.symm⟩⟩
    rw [triple] at hmem
    exact hmem
  obtain ⟨R, hRZ, hRYX⟩ := exists_glue_zero (LinearMap.ker Z)
    (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) Y cov compatible
  refine ⟨R, hRZ, hRYX, ?_⟩
  rintro v ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) := by
    rw [cov]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  have heq : R w = Y a := by rw [← hab, map_add, hRZ a ha, hRYX b hb, add_zero]
  refine ⟨⟨a, ?_⟩, ⟨a, heq.symm⟩⟩
  change Z a = 0 at ha
  rw [LinearMap.add_apply, ha, add_zero, heq]

/-- A general, dimension-free decomposition with pairwise disjoint images.
These are exactly the linear-algebra data used to establish the cover in A.1. -/
theorem exists_disjoint_decomposition (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Disjoint (LinearMap.range R) (LinearMap.range S) ∧
      Disjoint (LinearMap.range R) (LinearMap.range C) ∧
      Disjoint (LinearMap.range S) (LinearMap.range C) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y ∧
      LinearMap.range S ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Z ∧
      LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
  obtain ⟨R, hRZ, hRYX, rangeR⟩ := exists_cover_component Y Z triple cover
  obtain ⟨S, hSY, hSZX, rangeS⟩ := exists_cover_component Z Y
    (by simpa only [add_comm Z Y, inf_assoc, inf_comm, inf_left_comm] using triple)
    (by simpa only [add_comm Z Y, sup_assoc, sup_comm, sup_left_comm] using cover)
  rw [add_comm Z Y] at hSZX rangeS
  have eqX : Set.EqOn (R + S) (Y + Z) (LinearMap.ker (Y + Z)) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    rw [LinearMap.add_apply, hRYX w (Submodule.mem_sup_right hw), hSZX w (Submodule.mem_sup_right hw)]
    simpa only [zero_add] using hw.symm
  have eqY : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Y) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Y w = 0 at hw
    simp only [LinearMap.add_apply, hRYX w (Submodule.mem_sup_left hw), hSY w hw, hw, zero_add]
  have eqZ : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Z) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Z w = 0 at hw
    simp only [LinearMap.add_apply, hRZ w hw, hSZX w (Submodule.mem_sup_left hw), hw, add_zero]
  have hRS : R + S = Y + Z := by
    ext w
    exact LinearMap.eqOn_sup (LinearMap.eqOn_sup eqX eqY) eqZ (cover ▸ Submodule.mem_top)
  let C := Y + R
  have hC : C = Z + S := by
    ext w
    exact binary_cross_inline_DegreeCover (congrArg (fun f : W →ₗ[F2] V => f w) hRS)
  have hY : Y = R + C := by
    ext w
    change Y w = R w + (Y w + R w)
    rw [add_left_comm, binary_add_self, add_zero]
  have hZ : Z = S + C := by
    rw [hC]
    ext w
    change Z w = S w + (Z w + S w)
    rw [add_left_comm, binary_add_self, add_zero]
  have rangeC : LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
    apply le_inf
    · exact (LinearMap.range_add_le Y R).trans (sup_le le_rfl (rangeR.trans inf_le_right))
    · rw [hC]
      exact (LinearMap.range_add_le Z S).trans (sup_le le_rfl (rangeS.trans inf_le_right))
  have kill : ∀ v, v ∈ LinearMap.range (Y + Z) → v ∈ LinearMap.range Y →
      v ∈ LinearMap.range Z → v = 0 := by
    intro v hx hy hz
    have h : v ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z := ⟨⟨hx, hy⟩, hz⟩
    rwa [triple] at h
  refine ⟨R, S, C, hRS.symm, hY, hZ, ?_, ?_, ?_, rangeR, rangeS, rangeC⟩
  · exact Submodule.disjoint_def.mpr (fun v hr hs => kill v (rangeR hr).1 (rangeR hr).2 (rangeS hs).2)
  · exact Submodule.disjoint_def.mpr (fun v hr hc => kill v (rangeR hr).1 (rangeR hr).2 (rangeC hc).2)
  · exact Submodule.disjoint_def.mpr (fun v hs hc => kill v (rangeS hs).1 (rangeC hc).1 (rangeS hs).2)

/-- Rank additivity needs image containment as well as disjointness. -/
theorem rank_add_of_disjoint [FiniteDimensional F2 V] (R S : W →ₗ[F2] V)
    (hd : Disjoint (LinearMap.range R) (LinearMap.range S))
    (hR : LinearMap.range R ≤ LinearMap.range (R + S))
    (hS : LinearMap.range S ≤ LinearMap.range (R + S)) :
    Module.finrank F2 (LinearMap.range (R + S)) =
      Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) := by
  have heq := le_antisymm (LinearMap.range_add_le R S) (sup_le hR hS)
  rw [heq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range R) (LinearMap.range S)
  have hb : LinearMap.range R ⊓ LinearMap.range S = ⊥ := hd.eq_bot
  rw [hb, finrank_bot, add_zero] at h
  exact h

/-- The cover F(X) \ F₂(X) ⊆ F₁(X), with all three rank-additive decompositions.
There is no bound on dimension, and both bad-event exclusions are discharged. -/
theorem outside_bad_rank_cover [FiniteDimensional F2 V] (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Module.finrank F2 (LinearMap.range (Y + Z)) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) ∧
      Module.finrank F2 (LinearMap.range Y) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range C) ∧
      Module.finrank F2 (LinearMap.range Z) =
        Module.finrank F2 (LinearMap.range S) + Module.finrank F2 (LinearMap.range C) := by
  obtain ⟨R, S, C, hX, hY, hZ, dRS, dRC, dSC, rR, rS, rC⟩ :=
    exists_disjoint_decomposition Y Z triple cover
  refine ⟨R, S, C, hX, hY, hZ, ?_, ?_, ?_⟩
  · rw [hX]
    exact rank_add_of_disjoint R S dRS
      (hX ▸ rR.trans inf_le_left) (hX ▸ rS.trans inf_le_left)
  · rw [hY]
    exact rank_add_of_disjoint R C dRC
      (hY ▸ rR.trans inf_le_right) (hY ▸ rC.trans inf_le_left)
  · rw [hZ]
    exact rank_add_of_disjoint S C dSC
      (hZ ▸ rS.trans inf_le_right) (hZ ▸ rC.trans inf_le_right)

end MaxCutGames.Appendix.DegreeCover

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Identities
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

variable [FiniteDimensional K W] [FiniteDimensional K V]

/-! ## The unique selector in (A.4) -/

omit [FiniteDimensional K V] in
theorem a4_codomain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A₀ = (B.map Y) ⊓ A := by
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  apply le_antisymm
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hwX := hk hwy
    rw [hker] at hwX
    exact ⟨⟨w, hwX, hw⟩, hA ha⟩
  · intro a ha
    rcases ha.1 with ⟨b, hb, hYb⟩
    let bb : B₀ := ⟨b, hB hb⟩
    have hxb : X bb = 0 := by
      have hx : bb ∈ LinearMap.ker X := by rw [hker]; exact hb
      exact hx
    have hymem : compress Y A₀ B₀ bb ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y b, by rw [hYb]; exact ha.2, rfl⟩
    have hzmem : compress Y A₀ B₀ bb ∈ LinearMap.range (compress Y A₀ B₀ - X) :=
      ⟨bb, by change compress Y A₀ B₀ bb - X bb = compress Y A₀ B₀ bb; rw [hxb, sub_zero]⟩
    have hz := Submodule.disjoint_def.mp hd (compress Y A₀ B₀ bb) hymem hzmem
    have hm : Y b ∈ LinearMap.ker A₀.mkQ := hz
    rw [Submodule.ker_mkQ, hYb] at hm
    exact hm

omit [FiniteDimensional K V] in
theorem a4_domain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    B₀ = B ⊔ A.comap Y := by
  have hrange := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hcover := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).2
  apply le_antisymm
  · intro w hw
    let ww : B₀ := ⟨w, hw⟩
    have ht : ww ∈ LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) := by
      rw [hcover]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨b, hb, p, hp, hbp⟩
    have hbB : (b : W) ∈ B := by rw [hker] at hb; exact hb
    have hpEq : compress Y A₀ B₀ p = X p := by
      have hz : compress Y A₀ B₀ p - X p = 0 := hp
      exact sub_eq_zero.mp hz
    have hq : A₀.mkQ (Y p) ∈ A.map A₀.mkQ := by
      rw [← himage]
      change compress Y A₀ B₀ p ∈ LinearMap.range X
      rw [hpEq]
      exact ⟨p, rfl⟩
    have hpA : (p : W) ∈ A.comap Y :=
      (quotient_mem_image_iff A₀ A hA (Y p)).mp hq
    exact Submodule.mem_sup.mpr ⟨(b : W), hbB, (p : W), hpA, congrArg Subtype.val hbp⟩
  · apply sup_le hB
    intro w hw
    have hqx : A₀.mkQ (Y w) ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y w, hw, rfl⟩
    rcases hrange hqx with ⟨c, hc⟩
    have hdiff : Y w - Y c ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc.symm
    have hwc : w - c ∈ B₀ := inner.2 (by
      change Y (w - c) ∈ A₀
      simpa only [map_sub] using hdiff)
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

omit [FiniteDimensional K V] in
theorem a4_apply_on_preimage (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀))
    (p : B₀) (hp : Y p ∈ A) : X p = A₀.mkQ (Y p) := by
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  have hy : compress Y A₀ B₀ p ∈ LinearMap.range X := by
    rw [himage]
    exact ⟨Y p, hp, rfl⟩
  have hx : X p ∈ LinearMap.range X := ⟨p, rfl⟩
  have hzX : (compress Y A₀ B₀ - X) p ∈ LinearMap.range X :=
    (LinearMap.range X).sub_mem hy hx
  have hzR : (compress Y A₀ B₀ - X) p ∈ LinearMap.range (compress Y A₀ B₀ - X) := ⟨p, rfl⟩
  have hz := Submodule.disjoint_def.mp hd ((compress Y A₀ B₀ - X) p) hzX hzR
  exact (sub_eq_zero.mp hz).symm

omit [FiniteDimensional K V] in
theorem a4_map_unique (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X₁ X₂ : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hk₁ : LinearMap.ker X₁ = B.comap B₀.subtype)
    (hk₂ : LinearMap.ker X₂ = B.comap B₀.subtype)
    (hi₁ : LinearMap.range X₁ = A.map A₀.mkQ)
    (hi₂ : LinearMap.range X₂ = A.map A₀.mkQ)
    (hr₁ : RankAdditivity.RankBelow X₁ (compress Y A₀ B₀))
    (hr₂ : RankAdditivity.RankBelow X₂ (compress Y A₀ B₀)) : X₁ = X₂ := by
  have hd := a4_domain_forced Y A₀ A B B₀ X₁ hA hB inner hk₁ hi₁ hr₁
  ext w
  have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hd]; exact w.property
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
  let bb : B₀ := ⟨b, hB hb⟩
  have hpB₀ : p ∈ B₀ := by rw [hd]; exact Submodule.mem_sup_right hp
  let pp : B₀ := ⟨p, hpB₀⟩
  have heq : w = bb + pp := Subtype.ext hbp.symm
  have hb₁ : X₁ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₁ := by rw [hk₁]; exact hb
    exact h
  have hb₂ : X₂ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₂ := by rw [hk₂]; exact hb
    exact h
  have hp₁ := a4_apply_on_preimage Y A₀ A B₀ X₁ hi₁ hr₁ pp hp
  have hp₂ := a4_apply_on_preimage Y A₀ A B₀ X₂ hi₂ hr₂ pp hp
  rw [heq, map_add, map_add, hb₁, hb₂, hp₁, hp₂]

omit [FiniteDimensional K V] in
theorem a4_weak_selector_of_summand (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B := by
  have hi := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    have hqa : A₀.mkQ a ∈ LinearMap.range X := by rw [himage]; exact ⟨a, ha, rfl⟩
    rcases hi hqa with ⟨c, hc⟩
    have hdiff : Y c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc
    rcases inner.1 hdiff with ⟨w, hw⟩
    refine ⟨(c : W) - w, ?_⟩
    rw [map_sub, hw]
    abel
  · intro w hw
    have hyw : Y w = 0 := hw
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hyw]; exact A₀.zero_mem)
    have hwq : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change A₀.mkQ (Y w) = 0
      rw [hyw, map_zero]
    have hwx := hk hwq
    rw [hker] at hwx
    exact hwx

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_kernel_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA₀ : A₀ = (B.map Y) ⊓ A) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hKY : LinearMap.ker Y ≤ B)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.ker X = B.comap B₀.subtype := by
  ext w
  constructor
  · intro hw
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    have hxp : X pp = 0 := by
      have hxw : X w = 0 := hw
      rw [heq, map_add, hzero bb hb, zero_add] at hxw
      exact hxw
    have hqp : A₀.mkQ (Y p) = 0 := (hcopy pp hp).symm.trans hxp
    have hy₀ : Y p ∈ A₀ := by
      have hm : Y p ∈ LinearMap.ker A₀.mkQ := hqp
      simpa only [Submodule.ker_mkQ] using hm
    rw [hA₀] at hy₀
    rcases hy₀.1 with ⟨b', hb', hYb'⟩
    have hpk : p - b' ∈ LinearMap.ker Y := by
      change Y (p - b') = 0
      rw [map_sub, hYb', sub_self]
    have hpB : p ∈ B := by
      have h := B.add_mem (hKY hpk) hb'
      simpa only [sub_add_cancel] using h
    have h := B.add_mem hb hpB
    change (w : W) ∈ B
    exact hbp ▸ h
  · intro hw
    exact hzero w hw

omit [FiniteDimensional K V] in
theorem disjoint_quotient_images_of_intersection
    (A₀ A C : Submodule K V) (hA₀ : A₀ = C ⊓ A) :
    Disjoint (A.map A₀.mkQ) (C.map A₀.mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro v hvA hvC
  rcases hvA with ⟨a, ha, hqa⟩
  rcases hvC with ⟨c, hc, hqc⟩
  have hdiff : c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp (hqc.trans hqa.symm)
  have hdiffA : c - a ∈ A := by rw [hA₀] at hdiff; exact hdiff.2
  have hcA : c ∈ A := by
    have h := A.add_mem hdiffA ha
    simpa only [sub_add_cancel] using h
  have hc₀ : c ∈ A₀ := by rw [hA₀]; exact ⟨hc, hcA⟩
  have hqzero : A₀.mkQ c = 0 := by
    change c ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hc₀
  exact hqc.symm.trans hqzero

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_range_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hB₀ : B₀ = B ⊔ A.comap Y) (hAY : A ≤ LinearMap.range Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range X = A.map A₀.mkQ := by
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    refine ⟨Y p, hp, ?_⟩
    rw [← hw, heq, map_add, hzero bb hb, hcopy pp hp, zero_add]
  · rintro v ⟨a, ha, hqa⟩
    rcases hAY ha with ⟨p, hp⟩
    have hpA : p ∈ A.comap Y := by change Y p ∈ A; rw [hp]; exact ha
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hpA
    let pp : B₀ := ⟨p, hp₀⟩
    refine ⟨pp, ?_⟩
    rw [hcopy pp hpA, hp, hqa]

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem a4_remainder_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range (compress Y A₀ B₀ - X) ≤ (B.map Y).map A₀.mkQ ∧
      LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) = ⊤ := by
  have decomp : ∀ w : B₀, ∃ b p : B₀,
      (b : W) ∈ B ∧ Y p ∈ A ∧ b + p = w := by
    intro w
    have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    exact ⟨⟨b, hb₀⟩, ⟨p, hp₀⟩, hb, hp, Subtype.ext hbp⟩
  constructor
  · rintro v ⟨w, hw⟩
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hz : (compress Y A₀ B₀ - X) w = A₀.mkQ (Y b) := by
      rw [← hbp, map_add]
      change (compress Y A₀ B₀ b - X b) + (compress Y A₀ B₀ p - X p) = A₀.mkQ (Y b)
      rw [hzero b hb, hcopy p hp]
      simp only [compress_apply, sub_zero, sub_self, add_zero]
    exact ⟨Y b, ⟨(b : W), hb, rfl⟩, hz.symm.trans hw⟩
  · apply le_antisymm le_top
    intro w _
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hpker : p ∈ LinearMap.ker (compress Y A₀ B₀ - X) := by
      change compress Y A₀ B₀ p - X p = 0
      rw [hcopy p hp]
      exact sub_self _
    exact Submodule.mem_sup.mpr ⟨b, hzero b hb, p, hpker, hbp⟩

omit [FiniteDimensional K V] in
theorem a4_surviving_index_unique (Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (p q : A4Index (K := K) (W := W) (V := V))
    (hp : A4Survives Y A B p) (hq : A4Survives Y A B q) : p = q := by
  rcases p with ⟨A₀, B₀, X₀⟩
  rcases q with ⟨A₁, B₁, X₁⟩
  rcases hp with ⟨ha₀, hb₀, hi₀, hk₀, him₀, hr₀⟩
  rcases hq with ⟨ha₁, hb₁, hi₁, hk₁, him₁, hr₁⟩
  have heA : A₀ = A₁ := (a4_codomain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_codomain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  have heB : B₀ = B₁ := (a4_domain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_domain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  subst A₁
  subst B₁
  have heX := a4_map_unique Y A₀ A B B₀ X₀ X₁ ha₀ hb₀ hi₀ hk₀ hk₁ him₀ him₁ hr₀ hr₁
  cases heX
  rfl

end MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.BinaryA4

open LinearIdentities

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]

omit [FiniteDimensional F2 W] [FiniteDimensional F2 V] in
/-- Construct the actual linear map in the canonical (A.4) summand by
gluing zero on `B` with `Q_A₀ Y` on `Y⁻¹(A)`. -/
theorem canonical_glued_map (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    ∃ X : ↥(B ⊔ A.comap Y) →ₗ[F2] (V ⧸ ((B.map Y) ⊓ A)),
      (∀ b : ↥(B ⊔ A.comap Y), (b : W) ∈ B → X b = 0) ∧
      (∀ p : ↥(B ⊔ A.comap Y), Y p ∈ A → X p = ((B.map Y) ⊓ A).mkQ (Y p)) := by
  let P := A.comap Y
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ P
  let pp := P.comap B₀.subtype
  let bb := B.comap B₀.subtype
  let f := compress Y A₀ B₀
  have hc : pp ⊔ bb = ⊤ := by
    apply le_antisymm le_top
    intro w _
    rcases Submodule.mem_sup.mp w.property with ⟨b, hb, p, hp, hbp⟩
    let pv : B₀ := ⟨p, Submodule.mem_sup_right hp⟩
    let bv : B₀ := ⟨b, Submodule.mem_sup_left hb⟩
    refine Submodule.mem_sup.mpr ⟨pv, hp, bv, hb, ?_⟩
    apply Subtype.ext
    change p + b = (w : W)
    rw [add_comm]
    exact hbp
  have compat : ∀ w ∈ pp, w ∈ bb → f w = 0 := by
    intro w hp hb
    have hm : Y w ∈ A₀ := ⟨⟨(w : W), hb, rfl⟩, hp⟩
    change Y w ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hm
  obtain ⟨X, hcopy, hzero⟩ := DegreeCover.exists_glue_zero pp bb f hc compat
  refine ⟨X, ?_, ?_⟩
  · intro b hb
    exact hzero b hb
  · intro p hp
    exact hcopy p hp

theorem a4_selector_exists (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hAY : A ≤ LinearMap.range Y) (hKY : LinearMap.ker Y ≤ B) :
    ∃ p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  obtain ⟨X, hzero, hcopy⟩ := canonical_glued_map Y A B
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ A.comap Y
  have inner : Hybrid Y A₀ B₀ := by
    constructor
    · intro a ha
      rcases ha.1 with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    · intro w hw
      have hy : Y w ∈ (B.map Y) ⊓ A := hw
      exact Submodule.mem_sup_right hy.2
  have hk := a4_kernel_of_gluing Y A₀ A B B₀ X rfl rfl hKY hzero hcopy
  have hi := a4_range_of_gluing Y A₀ A B B₀ X rfl hAY hzero hcopy
  have hr := a4_remainder_of_gluing Y A₀ A B B₀ X rfl hzero hcopy
  have hd := disjoint_quotient_images_of_intersection A₀ A (B.map Y) rfl
  have hl : RankAdditivity.RankBelow X (compress Y A₀ B₀) := by
    apply (RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mpr
    refine ⟨?_, hr.2⟩
    rw [hi]
    exact hd.mono_right hr.1
  exact ⟨⟨A₀, B₀, X⟩, inf_le_right, le_sup_left, inner, hk, hi, hl⟩

/-- The complete unique-index selector identity in (A.4) for arbitrary
finite-dimensional binary vector spaces. The index records both subspaces
and the genuine linear map with the required kernel and range. -/
theorem a4_unique_selector (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    (A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B) ↔
      ∃! p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨p, hp⟩ := a4_selector_exists Y A B ha hb
    exact ⟨p, hp, fun q hq => a4_surviving_index_unique Y A B q p hq hp⟩
  · rintro ⟨⟨A₀, B₀, X⟩, hp, _⟩
    rcases hp with ⟨_, _, inner, hk, hi, hr⟩
    exact a4_weak_selector_of_summand Y A₀ A B B₀ X inner hk hi hr

end MaxCutGames.Appendix.BinaryA4

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CoordinateTransport
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.CoordinateTransport

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end MaxCutGames.Appendix.CoordinateTransport

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace MaxCutGames.Appendix.FullCompression

open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.CoordinateTransport
open Module

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

end MaxCutGames.Appendix.FullCompression

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
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T) =
      MaxCutGames.Fourier.MatrixRestrictions.restrict
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
    (θ : N → MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) (p : ℕ) :
    (𝔼 T, 𝔼 n, spectralProjector Q
      (MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T) (θ n) ^ p) =
      𝔼 M, spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p := by
  simp_rw [spectralProjector_restriction]
  exact Restriction.real_translation_average
    (fun n => MaxCutGames.Fourier.MatrixRestrictions.embed A B (θ n))
    (fun M => spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p)

end MaxCutGames.Appendix.Derivatives

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

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

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A4IndexCount
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace MaxCutGames.Appendix.A4IndexCount

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

theorem factorViaRange_injective {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker = P.ker) :
    Function.Injective (factorViaRange X P hker.le) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := X.surjective_rangeRestrict a
  obtain ⟨v, rfl⟩ := X.surjective_rangeRestrict b
  rw [factorViaRange_apply, factorViaRange_apply] at hab
  have hp : u - v ∈ P.ker := by
    change P (u - v) = 0
    rw [map_sub, hab, sub_self]
  have hx : u - v ∈ X.ker := by rwa [hker]
  apply Subtype.ext
  apply sub_eq_zero.mp
  change X u - X v = 0
  simpa only [LinearMap.mem_ker, map_sub] using hx

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

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem aToRange_surjective (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) :
    Function.Surjective (aToRange A A0 B0 X hR) := by
  intro c
  have hc : (c : V ⧸ A0) ∈ A.map A0.mkQ := by rw [← hR]; exact c.property
  rcases Submodule.mem_map.mp hc with ⟨a, ha, he⟩
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem encodeFixed_relation (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (a : A) (b : B0) :
    encodeFixed A A0 B B0 X hK hR a = B.mkQ (b : W) ↔ A0.mkQ (a : V) = X b := by
  let P := quotientRestriction B B0
  have hXP : X.ker = P.ker := hK.trans (ker_quotientRestriction B B0).symm
  change factorViaRange X P hXP.le (aToRange A A0 B0 X hR a) = P b ↔ _
  rw [← factorViaRange_apply X P hXP.le b,
    (factorViaRange_injective X P hXP).eq_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

theorem ker_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).ker = A0.comap A.subtype := by
  ext a
  have h := encodeFixed_relation A A0 B B0 X hK hR a (0 : B0)
  simpa using h

theorem range_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).range = (quotientRestriction B B0).range := by
  rw [encodeFixed, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (aToRange_surjective A A0 B0 X hR))]
  exact factorViaRange_range _ _ _

theorem recover_A0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hA : A0 ≤ A) :
    (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype = A0 := by
  rw [ker_encodeFixed]
  ext a
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    exact Submodule.mem_map.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem recover_B0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hB : B ≤ B0) :
    (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ = B0 := by
  rw [range_encodeFixed]
  ext w
  change B.mkQ w ∈ (quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hm : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hm) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem encodeFixed_injective (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X X' : B0 →ₗ[K] (V ⧸ A0))
    (hK : X.ker = B.comap B0.subtype) (hR : X.range = A.map A0.mkQ)
    (hK' : X'.ker = B.comap B0.subtype) (hR' : X'.range = A.map A0.mkQ)
    (h : encodeFixed A A0 B B0 X hK hR = encodeFixed A A0 B B0 X' hK' hR') : X = X' := by
  apply LinearMap.ext
  intro b
  have hb : X b ∈ A.map A0.mkQ := by rw [← hR]; exact ⟨b, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨a, ha, he⟩
  have henc : encodeFixed A A0 B B0 X hK hR ⟨a, ha⟩ = B.mkQ (b : W) :=
    (encodeFixed_relation A A0 B B0 X hK hR ⟨a, ha⟩ b).mpr he
  have henc' : encodeFixed A A0 B B0 X' hK' hR' ⟨a, ha⟩ = B.mkQ (b : W) := by
    rw [← h]
    exact henc
  exact he.symm.trans
    ((encodeFixed_relation A A0 B B0 X' hK' hR' ⟨a, ha⟩ b).mp henc')

theorem encode_injective (A : Submodule K V) (B : Submodule K W) :
    Function.Injective (encode A B) := by
  rintro ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩ ⟨⟨A0', B0', X'⟩, hA', hB', hK', hR'⟩ h
  change encodeFixed A A0 B B0 X hK hR = encodeFixed A A0' B B0' X' hK' hR' at h
  have hAeq : A0 = A0' := by
    calc
      A0 = (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype :=
        (recover_A0 A A0 B B0 X hK hR hA).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').ker.map A.subtype :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.ker.map A.subtype) h
      _ = A0' := recover_A0 A A0' B B0' X' hK' hR' hA'
  have hBeq : B0 = B0' := by
    calc
      B0 = (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ :=
        (recover_B0 A A0 B B0 X hK hR hB).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').range.comap B.mkQ :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.range.comap B.mkQ) h
      _ = B0' := recover_B0 A A0' B B0' X' hK' hR' hB'
  cases hAeq
  cases hBeq
  have hXeq := encodeFixed_injective A A0 B B0 X X' hK hR hK' hR' h
  cases hXeq
  rfl

end Generic

open Integration.BinaryLinear

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_index_le (A : Submodule F2 V) (B : Submodule F2 W) :
    Nat.card (Index A B) ≤
      2 ^ (Module.finrank F2 A * Module.finrank F2 (W ⧸ B)) := by
  have hc := CompressionCount.natCard_linearMap (U := A) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode A B) (encode_injective A B)
  rwa [hc] at h

end MaxCutGames.Appendix.A4IndexCount

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix.Derivatives

namespace MaxCutGames.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

private theorem indicator_eq_sum_of_unique_inline_OperatorPartitions {I : Type*} [Fintype I]
    (P : Prop) (R : I → Prop) (a : ℝ)
    (hpart : P → ∃! i, R i) (hback : ∀ i, R i → P) :
    (if P then a else 0) = ∑ i, if R i then a else 0 := by
  classical
  by_cases hp : P
  · obtain ⟨i, hi, hu⟩ := hpart hp
    rw [ite_eq_left hp]
    symm
    calc
      (∑ j, if R j then a else 0) = if R i then a else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact ite_eq_right (fun hj => hji (hu j hj))
        · simp
      _ = a := ite_eq_left hi
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hp (hback i hi))

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem spectralProjector_partition {I : Type*} [Fintype I]
    (P : (F →ₗ[F2] E) → Prop) (R : I → (F →ₗ[F2] E) → Prop)
    (hpart : ∀ Y, P Y → ∃! i, R i Y)
    (hback : ∀ i Y, R i Y → P Y) (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P f = ∑ i, spectralProjector (R i) f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_spectralProjector, linearCoeff_sum]
  simp only [linearCoeff_spectralProjector]
  exact indicator_eq_sum_of_unique_inline_OperatorPartitions (P Y) (fun i => R i Y)
    (linearCoeff f Y) (hpart Y) (fun i => hback i Y)

variable [Finite E] [Finite F]

open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem a4Mask_unique (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (hY : A ≤ Y.range ∧ Y.ker ≤ B) :
    ∃! i : A4GeometricIndex A B, a4Mask A B i Y := by
  obtain ⟨p, hp, hu⟩ := (BinaryA4.a4_unique_selector Y A B).mp hY
  rcases hp with ⟨hA, hB, hinner, hker, hrange, hrank⟩
  let i : A4GeometricIndex A B := ⟨p, hA, hB, hker, hrange⟩
  refine ⟨i, ⟨hinner, hrank⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjA, hjB, hjker, hjrange⟩
  exact ⟨hjA, hjB, hj.1, hjker, hjrange, hj.2⟩

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F]
  [FiniteDimensional F2 E] in
theorem a4Mask_implies_weak (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E)
    (hi : a4Mask A B i Y) : A ≤ Y.range ∧ Y.ker ≤ B := by
  rcases i.property with ⟨_, _, hker, hrange⟩
  exact a4_weak_selector_of_summand Y i.val.1 A B i.val.2.1 i.val.2.2
    hi.1 hker hrange hi.2

omit [Finite E] [Finite F] in
theorem a4_projector_partition (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f =
      ∑ i : A4GeometricIndex A B, spectralProjector (a4Mask A B i) f := by
  exact spectralProjector_partition _ _
    (a4Mask_unique A B) (a4Mask_implies_weak A B) f

end MaxCutGames.Appendix.OperatorPartitions
end

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LevelInequality
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

noncomputable section

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

namespace MaxCutGames.Appendix.DerivativeDegree

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

attribute [local instance] OAI.MaxCutGames.Appendix.DerivativeDegree.quotientFinite
attribute [local instance] OAI.MaxCutGames.Appendix.DerivativeDegree.compressedDualFintype
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

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
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

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

/-- The support cutoff keeps the total order intact even when `order A B > d`. -/
theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end MaxCutGames.Appendix.DerivativeDegree

/-! The degree-zero base case in the actual finite binary Fourier model. -/
namespace MaxCutGames.Appendix.DegreeZero
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier

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

end MaxCutGames.Appendix.DegreeZero

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OperatorNorm
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

namespace MaxCutGames.Appendix.OperatorNorm

theorem energy_sum_sq_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 2) ^ 2 ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, (𝔼 n, g i n ^ 2) ^ 2 := by
  classical
  let e : I → ℝ := fun i => 𝔼 n, g i n ^ 2
  let E : ℝ := 𝔼 n, (∑ i, g i n) ^ 2
  let N : ℝ := Fintype.card I
  have hE : 0 ≤ E := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have he (i : I) : 0 ≤ e i := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hs : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he i
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp (n : Ω) : (∑ i, g i n) ^ 2 ≤ N * ∑ i, g i n ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) (fun i => g i n))
  have hEbound : E ≤ N * ∑ i, e i := by
    calc
      E ≤ 𝔼 n, N * ∑ i, g i n ^ 2 :=
        Finset.expect_le_expect fun n _ => hp n
      _ = N * ∑ i, e i := by
        rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hsq : E ^ 2 ≤ (N * ∑ i, e i) ^ 2 :=
    (sq_le_sq₀ hE (mul_nonneg hN hs)).mpr hEbound
  have hcs : (∑ i, e i) ^ 2 ≤ N * ∑ i, e i ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) e)
  change E ^ 2 ≤ N ^ 3 * ∑ i, e i ^ 2
  calc
    E ^ 2 ≤ N ^ 2 * (∑ i, e i) ^ 2 := by simpa [mul_pow] using hsq
    _ ≤ N ^ 2 * (N * ∑ i, e i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg N)
    _ = N ^ 3 * ∑ i, e i ^ 2 := by ring

theorem fourth_sum_le_card_cube {I : Type*} [Fintype I] (a : I → ℝ) :
    (∑ i, a i) ^ 4 ≤ (Fintype.card I : ℝ) ^ 3 * ∑ i, a i ^ 4 := by
  have h := energy_sum_sq_le_card_cube (Ω := Unit) (fun i _ => a i)
  simpa [← pow_mul] using h

theorem average_fourth_sum_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
  calc
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
        𝔼 n, (Fintype.card I : ℝ) ^ 3 * ∑ i, g i n ^ 4 :=
      Finset.expect_le_expect fun n _ => fourth_sum_le_card_cube (fun i => g i n)
    _ = (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.MaxCutGames.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.MaxCutGames.Appendix.OperatorNorm.compressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem compressFrequency_eq_compress (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : Restriction.compressFrequency A B Y = compress Y A B := by
  ext x
  rfl

theorem map_hybrid_fourth_average
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

theorem a4_fourth_average_le (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
      ∑ i : A4GeometricIndex A B,
        𝔼 T, 𝔼 N, mapDerivative i.val.2.2
          (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
  classical
  rw [a4_projector_partition A B f]
  simp only [Finset.sum_apply]
  calc
    (𝔼 M, (∑ i : A4GeometricIndex A B,
        spectralProjector (a4Mask A B i) f M) ^ 4) ≤
      (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B, 𝔼 M,
          spectralProjector (a4Mask A B i) f M ^ 4 :=
      average_fourth_sum_le_card_cube
        (fun (i : A4GeometricIndex A B) M => spectralProjector (a4Mask A B i) f M)
    _ = (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B,
          𝔼 T, 𝔼 N, mapDerivative i.val.2.2
            (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
      apply congrArg (fun r : ℝ =>
        (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      change (𝔼 M, spectralProjector
        (fun Y => Hybrid Y i.val.1 i.val.2.1 ∧
          RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)) f M ^ 4) = _
      exact (map_hybrid_fourth_average i.val.1 i.val.2.1 i.val.2.2 f).symm

end MaxCutGames.Appendix.OperatorNorm
end

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5Scalar
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

/-! Finite Gram-energy estimates used in Lemma A.1. The witness relation and
frequency-count instantiations are separate obligations. -/
namespace MaxCutGames.Appendix.F1Gram
open scoped BigOperators

/-- The squared entries of a Gram matrix are bounded by the squared total
energy of its underlying rows. This is a pairwise Cauchy–Schwarz argument. -/
theorem gram_energy_le {R C : Type*} [Fintype R] [Fintype C] (p : R → C → ℝ) :
    (∑ r, ∑ s, (∑ c, p r c * p s c)^2) ≤
      (∑ r, ∑ c, p r c^2)^2 := by
  classical
  let e : R → ℝ := fun r => ∑ c, p r c^2
  calc
    _ ≤ ∑ r, ∑ s, e r * e s := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p r) (p s)
    _ = (∑ r, e r) * (∑ s, e s) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ r, ∑ c, p r c^2)^2 := (pow_two _).symm

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end MaxCutGames.Appendix.F1Gram

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace MaxCutGames.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_horizontal [FiniteDimensional K V] (B : Submodule K V) :
    Module.finrank K (horizontal B) = Module.finrank K B := (horizontalEquiv B).finrank_eq.symm

theorem finrank_extension [FiniteDimensional K V] (B : Submodule K V) (q : V ⧸ B) :
    Module.finrank K (extension B q) = Module.finrank K B + 1 := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have h := (extensionEquiv B q v hv).finrank_eq.symm
  simpa only [Module.finrank_prod,Module.finrank_self] using h

theorem card_eq_pow_finrank [Finite K] [Finite V] [FiniteDimensional K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  have h := Fintype.card_congr (Module.finBasis K V).equivFun.toEquiv
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card] using h

attribute [local instance] OAI.MaxCutGames.Appendix.SubspaceExtensions.subspaceFintype
attribute [local instance] OAI.MaxCutGames.Appendix.SubspaceExtensions.quotientFintype
theorem quotient_card_mul_pow [Finite K] [Finite V] [FiniteDimensional K V] (B : Submodule K V) :
    (Nat.card (V ⧸ B) : ℤ) * (Nat.card K : ℤ)^Module.finrank K B =
      (Nat.card K : ℤ)^Module.finrank K V := by
  rw [card_eq_pow_finrank (K:=K) (V:=V ⧸ B)]
  simp only [Nat.cast_pow]
  rw [← pow_add, B.finrank_quotient_add_finrank]

theorem weightedTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V × K) w =
      ∑ B : Submodule K V, (w (Module.finrank K B) +
        (Nat.card (V ⧸ B) : ℤ) * w (Module.finrank K B + 1)) := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ a : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B),
        w (Module.finrank K (encode a)) :=
      (Equiv.sum_comp ((splitEquiv (K:=K) (V:=V)).symm) _).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_sigma,encode,Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro B _
        exact congrArg w (finrank_horizontal B)
      · apply Finset.sum_congr rfl
        intro B _
        calc
          _ = ∑ _q : V ⧸ B, w (Module.finrank K B + 1) := by
            apply Finset.sum_congr rfl
            intro q _
            exact congrArg w (finrank_extension B q)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem mobiusTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V × K) =
      (1 - (Nat.card K : ℤ)^Module.finrank K V) * mobiusTotal (K:=K) (V:=V) := by
  classical
  unfold mobiusTotal
  rw [weightedTotal_prod]
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, (1-(Nat.card K:ℤ)^Module.finrank K V) *
        mobiusWeight (Nat.card K) (Module.finrank K B) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [mobiusWeight]
      have hcard := quotient_card_mul_pow (K:=K) B
      calc
        _ = mobiusWeight (Nat.card K) (Module.finrank K B) -
            ((Nat.card (V ⧸ B):ℤ)*(Nat.card K:ℤ)^Module.finrank K B) *
              mobiusWeight (Nat.card K) (Module.finrank K B) := by ring
        _ = _ := by rw [hcard]; ring
    _ = _ := by rw [Finset.mul_sum]

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem finrank_map_equiv (e : V ≃ₗ[K] W) (B : Submodule K V) :
    Module.finrank K (B.map e.toLinearMap) = Module.finrank K B := (subspaceMapEquiv e B).finrank_eq.symm

theorem weightedTotal_equiv [Finite V] [Finite W] (e : V ≃ₗ[K] W) (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V) w = weightedTotal (K:=K) (V:=W) w := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, w (Module.finrank K (B.map e.toLinearMap)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [finrank_map_equiv]
    _ = _ := by
      change (∑ B : Submodule K V, w (Module.finrank K (subspaceEquiv e B))) = _
      exact Equiv.sum_comp (subspaceEquiv e) (fun B : Submodule K W => w (Module.finrank K B))

theorem mobiusTotal_equiv [Finite K] [Finite V] [Finite W] (e : V ≃ₗ[K] W) :
    mobiusTotal (K:=K) (V:=V) = mobiusTotal (K:=K) (V:=W) :=
  weightedTotal_equiv e _

theorem mobiusTotal_subsingleton [Finite K] [Finite V] [Subsingleton V] :
    mobiusTotal (K:=K) (V:=V) = 1 := by
  classical
  have hB : ∀ B : Submodule K V, B = ⊥ := by
    intro B
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  unfold mobiusTotal weightedTotal
  rw [Finset.sum_eq_single ⊥]
  · simp [mobiusWeight]
  · intro B _ hne
    exact (hne (hB B)).elim
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem coordinate_total_succ [Finite K] (n : Nat) :
    mobiusTotal (K:=K) (V:=Fin (n+1) → K) = 0 := by
  induction n with
  | zero =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) 0),mobiusTotal_prod]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) (n+1)),mobiusTotal_prod,ih,mul_zero]

theorem mobiusTotal_eq_if [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V) = if Module.finrank K V = 0 then 1 else 0 := by
  rw [mobiusTotal_equiv (Module.finBasis K V).equivFun]
  cases hd : Module.finrank K V with
  | zero => simpa [hd] using (mobiusTotal_subsingleton (K:=K) (V:=Fin 0 → K))
  | succ n => simpa [hd] using (coordinate_total_succ (K:=K) n)

theorem mobiusWeight_closed (q n : Nat) :
    mobiusWeight q n = (-1:ℤ)^n * (q:ℤ)^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    rw [mobiusWeight,ih,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,pow_add,pow_succ]
    ring

theorem binary_subspace_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] :
    weightedTotal (K:=ZMod 2) (V:=E) (fun d => (-1:ℤ)^d * 2^(d.choose 2)) =
      if Module.finrank (ZMod 2) E = 0 then 1 else 0 := by
  have h := mobiusTotal_eq_if (K:=ZMod 2) (V:=E)
  have hq : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [mobiusTotal,weightedTotal,mobiusWeight_closed,hq,Nat.cast_ofNat] using h

end
end MaxCutGames.Appendix.SubspaceExtensions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SubmoduleInterval
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

theorem lowerInterval_finrank (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    finrank 𝕜 (lowerIntervalEquiv I A) = finrank 𝕜 A.val :=
  (lowerIntervalSpaceEquiv I A).finrank_eq.symm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.MaxCutGames.Appendix.SubmoduleInterval.submoduleFinite
theorem lowerWeightedTotal_eq [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) :
    lowerWeightedTotal I w = SubspaceExtensions.weightedTotal (K := 𝕜) (V := I) w := by
  classical
  let := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  let := SubspaceExtensions.subspaceFintype (K := 𝕜) (V := I)
  unfold lowerWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (lowerIntervalEquiv I)
    (fun A : {A : Submodule 𝕜 V // A ≤ I} => w (finrank 𝕜 A.val))
    (fun B : Submodule 𝕜 I => w (finrank 𝕜 B))
    (fun A => congrArg w (lowerInterval_finrank I A).symm)

theorem binary_lower_interval_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] (I : Submodule (ZMod 2) E) :
    lowerWeightedTotal I (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if I = ⊥ then 1 else 0 := by
  rw [lowerWeightedTotal_eq, SubspaceExtensions.binary_subspace_mobius]
  simp only [Submodule.finrank_eq_zero]

end MaxCutGames.Appendix.SubmoduleInterval

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

namespace MaxCutGames.Appendix.TotalPredecessorCount
open Module
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_recovery (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) (x : E) :
    ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) = R.val x := by
  have hq : Y.quotKerEquivRange.symm (Y.rangeRestrict x) = Y.ker.mkQ x :=
    Y.quotKerEquivRange.symm_apply_apply (Y.ker.mkQ x)
  dsimp only [predecessorEnd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hq]
  rfl

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_injective (Y : E →ₗ[F2] F) :
    Function.Injective (predecessorEnd Y) := by
  intro R S h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  calc
    R.val x = ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) :=
      (predecessorEnd_recovery Y R x).symm
    _ = ((predecessorEnd Y S (Y.rangeRestrict x) : Y.range) : F) :=
      congrArg (fun P : Y.range →ₗ[F2] Y.range => (P (Y.rangeRestrict x) : F)) h
    _ = S.val x := predecessorEnd_recovery Y S x

omit [FiniteDimensional F2 F] in
theorem card_predecessors_le [Finite E] [Finite F] (Y : E →ₗ[F2] F) :
    Nat.card {R : E →ₗ[F2] F // RankBelow R Y} ≤
      2 ^ (finrank F2 Y.range ^ 2) := by
  classical
  let : Finite (Y.range →ₗ[F2] Y.range) :=
    Finite.of_injective (fun f : Y.range →ₗ[F2] Y.range => (f : Y.range → Y.range))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective (predecessorEnd Y)
    (predecessorEnd_injective Y)
  rw [CompressionCount.natCard_linearMap] at h
  simpa only [pow_two] using h
end MaxCutGames.Appendix.TotalPredecessorCount

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Multiplication of the real binary trace characters. -/
theorem linearTraceCharacter_re_add (S T : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter (S + T) X).re =
      (linearTraceCharacter S X).re * (linearTraceCharacter T X).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply]
  rw [← linearTraceCharacter_real S X, ← linearTraceCharacter_real T X]
  simp

variable [Fintype (E →ₗ[F2] F)]

/-- Multiplication by a trace character translates frequency. -/
theorem linearCoeff_mul_character (f : (E →ₗ[F2] F) → ℝ)
    (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * (linearTraceCharacter T X).re) S =
      linearCoeff f (S + T) := by
  simp only [linearCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [linearTraceCharacter_re_add]
  ac_rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Products transform to counting-measure convolution of normalized coefficients. -/
theorem linearCoeff_mul (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * g X) S =
      ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T) := by
  have hexpand : (fun X : E →ₗ[F2] F => f X * g X) =
      ∑ T : F →ₗ[F2] E, linearCoeff f T •
        (fun X => g X * (linearTraceCharacter T X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      f X * g X =
          (∑ T : F →ₗ[F2] E, linearCoeff f T * (linearTraceCharacter T X).re) * g X := by
        rw [linear_fourier_inversion]
      _ = ∑ T : F →ₗ[F2] E,
          linearCoeff f T * (g X * (linearTraceCharacter T X).re) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ac_rfl
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_mul_character]

/-- The actual fourth moment equals the squared coefficient-convolution mass. -/
theorem expect_fourth_eq_sum_convolution_sq (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X ^ 4) =
      ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
  calc
    (𝔼 X, f X ^ 4) = 𝔼 X, (f X * f X) ^ 2 := by
      apply Finset.expect_congr rfl
      intro X _
      rw [← pow_two, ← pow_mul]
    _ = ∑ S : F →ₗ[F2] E, linearCoeff (fun X => f X * f X) S ^ 2 :=
      (linear_parseval (fun X => f X * f X)).symm
    _ = ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
      simp only [linearCoeff_mul, coefficientConvolution]

end MaxCutGames.Fourier.MatrixProducts

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
namespace MaxCutGames.Appendix.F1Energy
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

theorem rank_le_of_rankBelow {R Y : G} (h : RankBelow R Y) : rank R ≤ rank Y := by
  change rank Y = rank R + rank (Y - R) at h
  omega

theorem boundedSplit_rank (d : ℕ) (X : G) (R : BoundedSplit d X) : rank X ≤ 2*d := by
  have h := R.property.1
  change rank X = rank R.val + rank (X - R.val) at h
  simp only [sub_eq_add_neg, DegreeCover.binary_neg] at h
  have hR := R.property.2.1
  have hS := R.property.2.2
  omega

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The checked geometric cover supplies exactly the F1 witness condition. -/
theorem good_of_trivial_intersections (X Y : G)
    (hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥)
    (hk : X.ker ⊔ Y.ker ⊔ (X+Y).ker = ⊤) : Good X Y := by
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  obtain ⟨R,S,C,hX,hY,hZ,hrX,hrY,hrZ⟩ :=
    DegreeCover.outside_bad_rank_cover Y (X+Y)
      (by simpa only [hc] using hi) (by simpa only [hc] using hk)
  have hXS : X = R+S := hc.symm.trans hX
  have hXR : X-R = S := by rw [hXS]; abel
  have hYR : Y-R = C := by rw [hY]; abel
  have hZS : (X+Y)-S = C := by rw [hZ]; abel
  have hSR : X+R = S := by simpa only [sub_eq_add_neg, DegreeCover.binary_neg] using hXR
  change rank (Y+(X+Y)) = rank R + rank S at hrX
  rw [hc] at hrX
  change rank Y = rank R + rank C at hrY
  change rank (X+Y) = rank S + rank C at hrZ
  refine ⟨R, ?_, ?_, ?_⟩
  · change rank X = rank R + rank (X-R)
    rw [hXR]
    exact hrX
  · change rank Y = rank R + rank (Y-R)
    rw [hYR]
    exact hrY
  · rw [hSR]
    change rank (X+Y) = rank S + rank ((X+Y)-S)
    rw [hZS]
    exact hrZ

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem sum_translate (R : G) (f : G → ℝ) :
    (∑ X, f (X+R)) = ∑ X, f X := Equiv.sum_comp (translate R) f

omit [FiniteDimensional F2 F] in
theorem card_bounded_splits_le (d : ℕ) (X : G) :
    Nat.card (BoundedSplit d X) ≤ 2^(4*d^2) := by
  classical
  by_cases h : Nonempty (BoundedSplit d X)
  · have hr := boundedSplit_rank d X (Classical.choice h)
    let inc : BoundedSplit d X → {R : G // RankBelow R X} :=
      fun R => ⟨R.val, R.property.1⟩
    have hinj : Function.Injective inc := by
      intro R S hRS
      exact Subtype.ext (congrArg (fun T : {R : G // RankBelow R X} => T.val) hRS)
    have hc := Nat.card_le_card_of_injective inc hinj
    have hp := TotalPredecessorCount.card_predecessors_le X
    change Nat.card {R : G // RankBelow R X} ≤ 2^(rank X^2) at hp
    have hs : rank X^2 ≤ 4*d^2 := by nlinarith
    exact hc.trans (hp.trans (Nat.pow_le_pow_right (by decide) hs))
  · have hz : Fintype.card (BoundedSplit d X) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun R => h ⟨R⟩⟩
    simp only [Nat.card_eq_fintype_card, hz, zero_le]

omit [FiniteDimensional F2 F] in
theorem card_predecessors_cast_le (d : ℕ) (Y : G) (hy : rank Y ≤ d) :
    (Fintype.card {R : G // RankBelow R Y} : ℝ) ≤ (2:ℝ)^(d^2) := by
  have h := TotalPredecessorCount.card_predecessors_le Y
  change Nat.card {R : G // RankBelow R Y} ≤ 2^(rank Y^2) at h
  have hs : rank Y^2 ≤ d^2 := by nlinarith
  have hp := h.trans (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.card_eq_fintype_card] at hp
  exact_mod_cast hp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_nonneg (a : G → ℝ) (R C : G) :
    0 ≤ predecessorCoefficient a R C := by
  unfold predecessorCoefficient
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem gram_nonneg (a : G → ℝ) (R S : G) : 0 ≤ gram a R S :=
  Finset.sum_nonneg (fun C _ => mul_nonneg
    (predecessorCoefficient_nonneg a R C) (predecessorCoefficient_nonneg a S C))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_sq (a : G → ℝ) (R C : G) :
    predecessorCoefficient a R C ^ 2 =
      if RankBelow R (R+C) then a (R+C)^2 else 0 := by
  unfold predecessorCoefficient
  split <;> simp only [sq_abs, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_eq (a : G → ℝ) :
    predecessorEnergy a =
      ∑ Y, (Fintype.card {R : G // RankBelow R Y} : ℝ) * a Y^2 := by
  unfold predecessorEnergy
  calc
    _ = ∑ R, ∑ Y, if RankBelow R Y then a Y^2 else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [predecessorCoefficient_sq]
      simpa only [add_comm] using
        sum_translate R (fun Y => if RankBelow R Y then a Y^2 else 0)
    _ = ∑ Y, ∑ R, if RankBelow R Y then a Y^2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← F1Gram.sum_subtype_eq (fun R => RankBelow R Y) (fun _ => a Y^2)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_nonneg (a : G → ℝ) : 0 ≤ predecessorEnergy a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 F] in
theorem predecessor_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    predecessorEnergy a ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by
  rw [predecessor_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : rank Y ≤ d
  · exact mul_le_mul_of_nonneg_right (card_predecessors_cast_le d Y hY) (sq_nonneg _)
  · rw [hdegree Y (Nat.lt_of_not_ge hY)]
    simp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_nonneg (a : G → ℝ) (X : G) : 0 ≤ goodConvolution a X := by
  apply Finset.sum_nonneg
  intro Y _
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- Each supported good term has a bounded split witness. Its summand is
counted with shared residual C=Y+R; all other summands are nonnegative. -/
theorem good_term_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X Y : G) :
    (if Good X Y then |a Y| * |a (X+Y)| else 0) ≤
      ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) := by
  have hnonneg : 0 ≤ ∑ R : BoundedSplit d X,
      predecessorCoefficient a R.val (Y+R.val) *
        predecessorCoefficient a (X+R.val) (Y+R.val) :=
    Finset.sum_nonneg (fun R _ => mul_nonneg
      (predecessorCoefficient_nonneg a _ _) (predecessorCoefficient_nonneg a _ _))
  by_cases hg : Good X Y
  · rw [ite_eq_left hg]
    by_cases ha : a Y = 0
    · simpa only [ha, abs_zero, zero_mul] using hnonneg
    by_cases hb : a (X+Y) = 0
    · simpa only [hb, abs_zero, mul_zero] using hnonneg
    have hY : rank Y ≤ d := by
      by_contra hn
      exact ha (hdegree Y (Nat.lt_of_not_ge hn))
    have hZ : rank (X+Y) ≤ d := by
      by_contra hn
      exact hb (hdegree (X+Y) (Nat.lt_of_not_ge hn))
    obtain ⟨R,hRX,hRY,hSZ⟩ := hg
    let r : BoundedSplit d X := ⟨R,hRX,
      (rank_le_of_rankBelow hRY).trans hY, (rank_le_of_rankBelow hSZ).trans hZ⟩
    have h1 : R+(Y+R) = Y := by
      calc
        _ = (Y+R)+R := by abel
        _ = Y := add_self_cancel Y R
    have h2 : (X+R)+(Y+R) = X+Y := by
      calc
        _ = (X+Y)+(R+R) := by abel
        _ = X+Y := by rw [DegreeCover.binary_add_self, add_zero]
    have heq : predecessorCoefficient a r.val (Y+r.val) *
        predecessorCoefficient a (X+r.val) (Y+r.val) = |a Y| * |a (X+Y)| := by
      change predecessorCoefficient a R (Y+R) *
        predecessorCoefficient a (X+R) (Y+R) = _
      simp only [predecessorCoefficient, h1, h2, ite_eq_left hRY, ite_eq_left hSZ]
    rw [← heq]
    exact Finset.single_le_sum (fun (s : BoundedSplit d X) _ => mul_nonneg
      (predecessorCoefficient_nonneg a s.val (Y+s.val))
      (predecessorCoefficient_nonneg a (X+s.val) (Y+s.val)))
      (Finset.mem_univ r)
  · rw [ite_eq_right hg]
    exact hnonneg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_le_gram (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) := by
  calc
    _ ≤ ∑ Y, ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) :=
      Finset.sum_le_sum (fun Y _ => good_term_le a d hdegree X Y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R.val (fun C =>
        predecessorCoefficient a R.val C * predecessorCoefficient a (X+R.val) C)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_sq_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ^ 2 ≤ (2:ℝ)^(4*d^2) *
      ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
  have hg := goodConvolution_le_gram a d hdegree X
  have hn := goodConvolution_nonneg a X
  have hs : 0 ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) :=
    Finset.sum_nonneg (fun _ _ => gram_nonneg a _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BoundedSplit d X => (1:ℝ)) (fun R => gram a R.val (X+R.val))
  have hcard : (Fintype.card (BoundedSplit d X) : ℝ) ≤ (2:ℝ)^(4*d^2) := by
    have h := card_bounded_splits_le d X
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ R : BoundedSplit d X, gram a R.val (X+R.val))^2 := by nlinarith
    _ ≤ (Fintype.card (BoundedSplit d X):ℝ) *
        ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by simpa using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem split_gram_energy_le (a : G → ℝ) (d : ℕ) :
    (∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2) ≤
      predecessorEnergy a ^ 2 := by
  calc
    _ ≤ ∑ X, ∑ R : G, gram a R (X+R)^2 := by
      apply Finset.sum_le_sum
      intro X _
      exact F1Gram.sum_comp_le (fun R : BoundedSplit d X => R.val)
        Subtype.val_injective (fun R => gram a R (X+R)^2) (fun _ => sq_nonneg _)
    _ = ∑ R, ∑ S, gram a R S^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R (fun S => gram a R S^2)
    _ ≤ predecessorEnergy a ^ 2 := F1Gram.gram_energy_le (predecessorCoefficient a)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, goodConvolution a X^2) ≤ (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
  have he := predecessor_energy_le a d hdegree
  have hn := predecessor_energy_nonneg a
  have hb : 0 ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by positivity
  calc
    _ ≤ (2:ℝ)^(4*d^2) *
        ∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun X _ => goodConvolution_sq_le a d hdegree X)
    _ ≤ (2:ℝ)^(4*d^2) * predecessorEnergy a^2 :=
      mul_le_mul_of_nonneg_left (split_gram_energy_le a d) (by positivity)
    _ ≤ (2:ℝ)^(4*d^2) * ((2:ℝ)^(d^2) * ∑ Y, a Y^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      omega

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- The complement of any bad event covered by `Good` is bounded without
changing the signs of the coefficients in the bad part. -/
theorem abs_complement_sum_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    |∑ Y, if bad Y then 0 else a Y * a (X+Y)| ≤ goodConvolution a X := by
  calc
    _ ≤ ∑ Y, |if bad Y then 0 else a Y * a (X+Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ goodConvolution a X := by
      apply Finset.sum_le_sum
      intro Y _
      by_cases hb : bad Y
      · simp only [ite_eq_left hb, abs_zero]
        split <;> positivity
      · simp only [ite_eq_right hb, ite_eq_left (hcover Y hb), abs_mul, le_refl]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem convolution_split_square_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 +
      2 * (∑ Y, if bad Y then a Y * a (X+Y) else 0)^2 := by
  let u : ℝ := ∑ Y, if bad Y then 0 else a Y * a (X+Y)
  let v : ℝ := ∑ Y, if bad Y then a Y * a (X+Y) else 0
  have hs : (∑ Y, a Y * a (X+Y)) = u+v := by
    dsimp only [u,v]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hb : bad Y <;> simp only [hb, ite_true, if_true, ite_false, add_zero, zero_add]
  have hu : |u| ≤ goodConvolution a X := abs_complement_sum_le a X bad hcover
  have hp := mul_nonneg (sub_nonneg.mpr hu)
    (add_nonneg (goodConvolution_nonneg a X) (abs_nonneg u))
  have hu2 : u^2 ≤ goodConvolution a X^2 := by nlinarith [sq_abs u]
  change (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 + 2*v^2
  rw [hs]
  nlinarith [sq_nonneg (u-v)]

omit [FiniteDimensional F2 F] in
theorem convolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (bad : G → G → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (∑ X, (∑ Y, a Y * a (X+Y))^2) ≤
      2 * ((2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
  calc
    _ ≤ ∑ X, (2 * goodConvolution a X^2 +
        2 * (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2) :=
      Finset.sum_le_sum (fun X _ => convolution_split_square_le a X (bad X) (hcover X))
    _ = 2 * (∑ X, goodConvolution a X^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (goodConvolution_energy_le a d hdegree)
        (show (0:ℝ) ≤ 2 by norm_num)) le_rfl

variable [Fintype (F →ₗ[F2] E)]
open MaxCutGames.Fourier.MatrixFourier MaxCutGames.Fourier.MatrixProducts

/-- The actual fourth-moment identity reduced to the remaining signed bad
convolution. Its geometric cover is supplied by `good_of_trivial_intersections`. -/
theorem fourth_moment_le_good_bad (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0)
    (bad : (F →ₗ[F2] E) → (F →ₗ[F2] E) → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (𝔼 X, f X^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2) +
      2 * ∑ X, (∑ Y, if bad X Y then linearCoeff f Y * linearCoeff f (X+Y) else 0)^2 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  unfold coefficientConvolution
  simpa only [linear_parseval] using
    convolution_energy_le (linearCoeff f) d hdegree bad hcover

end MaxCutGames.Appendix.F1Energy
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_UpperMobius
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MaxCutGames.Appendix.UpperMobius
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

attribute [local instance] OAI.MaxCutGames.Appendix.UpperMobius.quotientFinite
attribute [local instance] OAI.MaxCutGames.Appendix.UpperMobius.dualFinite
attribute [local instance] OAI.MaxCutGames.Appendix.UpperMobius.submoduleFinite
omit [FiniteDimensional F2 W] [Finite W] in
theorem quotient_comap_codim (K : Submodule F2 W)
    (S : Submodule F2 (W ⧸ K)) :
    Module.finrank F2 (W ⧸ S.comap K.mkQ) =
      Module.finrank F2 ((W ⧸ K) ⧸ S) := by
  let π := S.mkQ.comp K.mkQ
  have hπ : Function.Surjective π := S.mkQ_surjective.comp K.mkQ_surjective
  have hker : π.ker = S.comap K.mkQ := by simp [π, LinearMap.ker_comp]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq.symm.trans
    (π.quotKerEquivOfSurjective hπ).finrank_eq

omit [FiniteDimensional F2 W] [Finite W] in
theorem upperQuotientEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) := by
  have hB : (upperQuotientEquiv K B).comap K.mkQ = B.val :=
    congrArg Subtype.val ((Submodule.comapMkQRelIso K).apply_symm_apply B)
  exact (Submodule.quotEquivOfEq _ _ hB).finrank_eq.symm.trans
    (quotient_comap_codim K (upperQuotientEquiv K B))

omit [Finite W] in
theorem upperDualSubspaceEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 (upperDualSubspaceEquiv K B) := by
  calc
    _ = Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) :=
      upperQuotientEquiv_codim K B
    _ = Module.finrank F2 (upperQuotientEquiv K B).dualAnnihilator :=
      (Subspace.quotEquivAnnihilator (upperQuotientEquiv K B)).finrank_eq
    _ = _ := rfl

theorem upperWeightedTotal_eq_dual (K : Submodule F2 W) (w : ℕ → ℤ) :
    upperWeightedTotal K w =
      SubspaceExtensions.weightedTotal
        (K := F2) (V := Module.Dual F2 (W ⧸ K)) w := by
  classical
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  let := SubspaceExtensions.subspaceFintype (K := F2) (V := Module.Dual F2 (W ⧸ K))
  unfold upperWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (upperDualSubspaceEquiv K)
    (fun B : {B : Submodule F2 W // K ≤ B} => w (Module.finrank F2 (W ⧸ B.val)))
    (fun S : Submodule F2 (Module.Dual F2 (W ⧸ K)) => w (Module.finrank F2 S))
    (fun B => congrArg w (upperDualSubspaceEquiv_codim K B))

omit [Finite W] in
theorem quotient_finrank_zero_iff (K : Submodule F2 W) :
    Module.finrank F2 (W ⧸ K) = 0 ↔ K = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := K.finrank_quotient_add_finrank
    omega
  · intro h
    subst K
    have hr := (⊤ : Submodule F2 W).finrank_quotient_add_finrank
    rw [finrank_top] at hr
    omega

theorem binary_upper_interval_mobius (K : Submodule F2 W) :
    upperWeightedTotal K (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if K = ⊤ then 1 else 0 := by
  classical
  rw [upperWeightedTotal_eq_dual]
  rw [SubspaceExtensions.binary_subspace_mobius]
  simp only [Subspace.dual_finrank_eq, quotient_finrank_zero_iff]
end MaxCutGames.Appendix.UpperMobius

open scoped BigOperators

namespace MaxCutGames.Appendix.DyadicError

private theorem pow_le_one_aux_inline_DyadicError (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih hq0).trans (by simpa using hq1)

private theorem pow_antitone_aux_inline_DyadicError (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a b : ℕ) (hab : a ≤ b) : q^b ≤ q^a := by
  have hb : a + (b-a) = b :=
    (Nat.add_comm a (b-a)).trans (Nat.sub_add_cancel hab)
  calc
    q^b = q^(a+(b-a)) := congrArg (fun n : ℕ => q^n) hb.symm
    _ = q^a * q^(b-a) := by rw [pow_add]
    _ ≤ q^a * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one_aux_inline_DyadicError q hq0 hq1 (b-a)) (pow_nonneg hq0 a)
    _ = q^a := mul_one _

theorem half_power_le_quarter (d n : ℕ) (hd : 1 ≤ d) :
    (1/2 : ℝ)^(3*d*n) ≤ (1/4 : ℝ)^n := by
  have h3 : 2 ≤ 3*d := le_trans (by decide : 2 ≤ 3)
    (by simpa using Nat.mul_le_mul_left 3 hd)
  have hexp : 2*n ≤ 3*d*n := Nat.mul_le_mul_right n h3
  calc
    (1/2 : ℝ)^(3*d*n) ≤ (1/2 : ℝ)^(2*n) :=
      pow_antitone_aux_inline_DyadicError (1/2) (by norm_num) (by norm_num) _ _ hexp
    _ = (1/4 : ℝ)^n := by
      rw [pow_mul]
      congr 1
      norm_num

theorem quarterSum_nonneg (n : ℕ) : 0 ≤ quarterSum n := by
  unfold quarterSum
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num : (0:ℝ)≤1/4) i)

theorem quarterSum_residual (n : ℕ) :
    quarterSum n + (4/3 : ℝ)*(1/4 : ℝ)^n = 4/3 := by
  induction n with
  | zero => norm_num [quarterSum]
  | succ n ih =>
    have hstep : quarterSum (n+1) = quarterSum n + (1/4 : ℝ)^n := by
      exact Finset.sum_range_succ _ _
    rw [hstep, pow_succ]
    nlinarith

theorem quarterSum_le (n : ℕ) : quarterSum n ≤ (4/3 : ℝ) := by
  have hp : (0 : ℝ) ≤ (1/4 : ℝ)^n := pow_nonneg (by norm_num) n
  have h := quarterSum_residual n
  nlinarith

theorem quarterError_add_one (n : ℕ) (hn : 0 < n) :
    quarterError n + 1 = (quarterSum n)^2 := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hpair (i j : ℕ) :
      (if i=0 ∧ j=0 then (0:ℝ) else (1/4 : ℝ)^(i+j)) +
        (if i=0 ∧ j=0 then (1:ℝ) else 0) =
          (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [hi,hj,pow_add]
  have hsum : quarterError n +
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i=0 ∧ j=0 then (1:ℝ) else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    unfold quarterError
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hpair i j
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range n, if i=0 ∧ j=0 then (1:ℝ) else 0) =
        if i=0 then 1 else 0 := by
    by_cases hi : i=0
    · simp [hi,h0]
    · simp [hi]
  have hdelta : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i=0 ∧ j=0 then (1:ℝ) else 0) = 1 := by
    simp_rw [hinner]
    simp [h0]
  have hproduct : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (1/4 : ℝ)^i * (1/4 : ℝ)^j) = (quarterSum n)^2 := by
    simp only [quarterSum,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hdelta,hproduct] at hsum
  exact hsum

theorem quarterError_le_seven_ninths (n : ℕ) (hn : 0 < n) :
    quarterError n ≤ (7/9 : ℝ) := by
  have hbound := quarterSum_le n
  have hnonneg := quarterSum_nonneg n
  have hsq := mul_le_mul hbound hbound hnonneg (by norm_num : (0:ℝ)≤4/3)
  have hid := quarterError_add_one n hn
  nlinarith

theorem dyadicError_le_quarterError (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ quarterError (d+1) := by
  unfold dyadicError quarterError
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hzero : i=0 ∧ j=0
  · simp [hzero]
  · simp only [hzero]
    exact half_power_le_quarter d (i+j) hd

theorem dyadicError_le_seven_ninths (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ (7/9 : ℝ) :=
  (dyadicError_le_quarterError d hd).trans
    (quarterError_le_seven_ninths (d+1) (Nat.succ_pos d))

theorem finite_dyadic_error_le_one (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
      if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))) ≤ 1 := by
  change dyadicError d ≤ 1
  exact (dyadicError_le_seven_ninths d hd).trans (by norm_num)

end MaxCutGames.Appendix.DyadicError
end

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace MaxCutGames.Appendix.BadConvolution
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

private theorem sum_masked_eq_subtype_inline_BadConvolution {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (f : α → M) :
    (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) f

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

omit [Finite W] [Finite V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pairDimension_eq_zero_iff (p : Submodule F2 V × Submodule F2 W) :
    pairDimension p = 0 ↔ p = (⊥,⊤) := by
  rw [pairDimension, Nat.add_eq_zero_iff]
  rw [Submodule.finrank_eq_zero, UpperMobius.quotient_finrank_zero_iff]
  constructor
  · rintro ⟨hA,hB⟩
    exact Prod.ext hA hB
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem lower_mobius_sum (I : Submodule F2 V) :
    (∑ A : Submodule F2 V, if A ≤ I then mobius (finrank F2 A) else 0) =
      if I = ⊥ then 1 else 0 := by
  let := Fintype.ofFinite {A : Submodule F2 V // A ≤ I}
  rw [sum_masked_eq_subtype_inline_BadConvolution]
  have h := SubmoduleInterval.binary_lower_interval_mobius I
  unfold SubmoduleInterval.lowerWeightedTotal at h
  unfold mobius
  exact_mod_cast h

theorem upper_mobius_sum (K : Submodule F2 W) :
    (∑ B : Submodule F2 W, if K ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) =
      if K = ⊤ then 1 else 0 := by
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  rw [sum_masked_eq_subtype_inline_BadConvolution]
  have h := UpperMobius.binary_upper_interval_mobius K
  unfold UpperMobius.upperWeightedTotal at h
  unfold mobius
  exact_mod_cast h

omit [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
private theorem triple_incidence_iff_inline_BadConvolution (p : Submodule F2 V × Submodule F2 W)
    (X Y : W →ₗ[F2] V) :
    (Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)) ↔
      p.1 ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range ∧
        (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ p.2 := by
  simp only [Incidence, le_inf_iff, sup_le_iff]
  tauto

theorem triple_mobius_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then pairWeight p else 0) = if Bad X Y then 0 else 1 := by
  simp_rw [triple_incidence_iff_inline_BadConvolution]
  calc
    _ = (∑ A : Submodule F2 V,
        if A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range then mobius (finrank F2 A) else 0) *
        (∑ B : Submodule F2 W,
        if (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hA : A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range <;>
        by_cases hB : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B <;>
        simp [pairWeight, hA, hB]
    _ = _ := by
      rw [lower_mobius_sum, upper_mobius_sum]
      by_cases hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥ <;>
        by_cases hk : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker = ⊤ <;>
        simp [Bad, hi, hk]

theorem signed_triple_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then signedWeight p else 0) = if Bad X Y then 1 else 0 := by
  have htop : finrank F2 (W ⧸ (⊤ : Submodule F2 W)) = 0 :=
    (UpperMobius.quotient_finrank_zero_iff ⊤).mpr rfl
  have hterm (p : Submodule F2 V × Submodule F2 W) :
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then pairWeight p else 0) +
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then signedWeight p else 0) = if p = (⊥,⊤) then 1 else 0 := by
    by_cases hp : p = (⊥,⊤)
    · subst p
      simp [Incidence, pairWeight, signedWeight, mobius, htop]
    · by_cases h : Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      all_goals simp [signedWeight, hp, h]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun p _ => hterm p)
  rw [Finset.sum_add_distrib, triple_mobius_sum] at hs
  have hdelta : (∑ p : Submodule F2 V × Submodule F2 W,
      if p = (⊥,⊤) then (1:ℝ) else 0) = 1 := by simp
  rw [hdelta] at hs
  by_cases hbad : Bad X Y <;> simp [hbad] at hs ⊢ <;> linarith

variable [Fintype (W →ₗ[F2] V)]

/-- Exact Möbius expansion; no degree or positivity assumption is used. -/
theorem badConvolution_expansion (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) :
    badConvolution a X =
      ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p * pieceConvolution p.1 p.2 a X else 0 := by
  calc
    _ = ∑ Y, (if Bad X Y then (1:ℝ) else 0) * (a Y * a (X+Y)) := by
      unfold badConvolution
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h : Bad X Y <;> simp [h]
    _ = ∑ Y, ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p *
          (filteredCoefficient p.1 p.2 a Y * filteredCoefficient p.1 p.2 a (X+Y)) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← signed_triple_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X <;>
        by_cases hY : Incidence p.1 p.2 Y <;>
        by_cases hZ : Incidence p.1 p.2 (X+Y) <;>
        simp [filteredCoefficient, hX, hY, hZ]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X
      · simp only [hX, ite_true, if_true, pieceConvolution, Finset.mul_sum]
      · simp [hX]

omit [Fintype (Submodule F2 V)] in
theorem card_lower_rank_le (I : Submodule F2 V) (n i : ℕ)
    (hn : finrank F2 I ≤ n) :
    Nat.card {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i} ≤ 2^(n*i) := by
  let : Finite (Submodule F2 I) :=
    Finite.of_injective (fun S : Submodule F2 I => (S : Set I)) SetLike.coe_injective
  let e := SubmoduleInterval.lowerIntervalEquiv I
  let code (A : {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i}) :
      {S : Submodule F2 I // finrank F2 S = i} :=
    ⟨e ⟨A.1, A.2.1⟩,
      (SubmoduleInterval.lowerInterval_finrank I ⟨A.1, A.2.1⟩).trans A.2.2⟩
  have hi : Function.Injective code := by
    intro A B h
    have he : e ⟨A.1, A.2.1⟩ = e ⟨B.1, B.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {A : Submodule F2 V // A ≤ I} => z.val) (e.injective he)
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n i hn)

omit [Finite W] [Fintype (Submodule F2 W)] in
theorem card_upper_codim_le (K : Submodule F2 W) (n j : ℕ)
    (hn : finrank F2 (W ⧸ K) ≤ n) :
    Nat.card {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j} ≤ 2^(n*j) := by
  let D := Module.Dual F2 (W ⧸ K)
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (Submodule F2 D) :=
    Finite.of_injective (fun S : Submodule F2 D => (S : Set D)) SetLike.coe_injective
  let e := UpperMobius.upperDualSubspaceEquiv K
  let code (B : {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j}) :
      {S : Submodule F2 D // finrank F2 S = j} :=
    ⟨e ⟨B.1, B.2.1⟩,
      (UpperMobius.upperDualSubspaceEquiv_codim K ⟨B.1, B.2.1⟩).symm.trans B.2.2⟩
  have hi : Function.Injective code := by
    intro B C h
    have he : e ⟨B.1, B.2.1⟩ = e ⟨C.1, C.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {B : Submodule F2 W // K ≤ B} => z.val) (e.injective he)
  have hdim : finrank F2 D ≤ n := by
    simpa only [D, Subspace.dual_finrank_eq] using hn
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n j hdim)

private theorem finite_pair_level_sum_inline_BadConvolution {α : Type*} (s : Finset α)
    (i j : α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ a ∈ s, i a ≤ d ∧ j a ≤ d)
    (hzero : ∀ a ∈ s, ¬(i a=0 ∧ j a=0))
    (hcount : ∀ u v, (s.filter (fun a => i a=u ∧ j a=v)).card ≤ 2^(2*d*(u+v))) :
    (∑ a ∈ s, (1/2:ℝ)^(5*d*(i a+j a))) ≤ 1 := by
  classical
  have hmap : ∀ a ∈ s, (i a,j a) ∈ Finset.range (d+1) ×ˢ Finset.range (d+1) := by
    intro a ha
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).1),
       Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).2)⟩
  have hcancel (a b : ℕ) :
      (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ = ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(i a+j a)) := by
      have h := Finset.sum_fiberwise_of_maps_to (g := fun a => (i a,j a)) hmap
        (fun a => (1/2:ℝ)^(5*d*(i a+j a)))
      simpa only [Finset.sum_product, Prod.mk.injEq] using h.symm
    _ ≤ ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        if u=0 ∧ v=0 then 0 else (1/2:ℝ)^(3*d*(u+v)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      by_cases hz : u=0 ∧ v=0
      · rw [ite_eq_left hz]
        have hempty : s.filter (fun a => i a=u ∧ j a=v) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro a ha
          have ham := Finset.mem_filter.mp ha
          exact hzero a ham.1 ⟨ham.2.1.trans hz.1, ham.2.2.trans hz.2⟩
        rw [hempty, Finset.sum_empty]
      · rw [ite_eq_right hz]
        have hc : ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) ≤
            (2:ℝ)^(2*d*(u+v)) := by exact_mod_cast hcount u v
        calc
          _ = ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) *
              (1/2:ℝ)^(5*d*(u+v)) := by
            calc
              _ = ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(u+v)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [(Finset.mem_filter.mp ha).2.1, (Finset.mem_filter.mp ha).2.2]
              _ = _ := by simp
          _ ≤ (2:ℝ)^(2*d*(u+v)) * (1/2:ℝ)^(5*d*(u+v)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by
            have he : 5*d*(u+v)=2*d*(u+v)+3*d*(u+v) := by ring
            rw [he, hcancel]
    _ ≤ 1 := DyadicError.finite_dyadic_error_le_one d hd

omit [Finite W] [Fintype (W →ₗ[F2] V)] in
theorem incident_pair_weight_le_one (X : W →ₗ[F2] V) (d : ℕ)
    (hd : 1 ≤ d) (hX : finrank F2 X.range ≤ 2*d) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
          finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
      then (1/2:ℝ)^(5*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) else 0) ≤ 1 := by
  let i (p : Submodule F2 V × Submodule F2 W) := finrank F2 p.1
  let j (p : Submodule F2 V × Submodule F2 W) := finrank F2 (W ⧸ p.2)
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧ i p ≤ d ∧ j p ≤ d
  let s := Finset.univ.filter good
  have hs (p) (hp : p ∈ s) : good p := (Finset.mem_filter.mp hp).2
  have hbound : ∀ p ∈ s, i p ≤ d ∧ j p ≤ d := by
    intro p hp
    exact (hs p hp).2.2.2
  have hzero : ∀ p ∈ s, ¬(i p=0 ∧ j p=0) := by
    intro p hp hz
    apply (hs p hp).1
    apply (pairDimension_eq_zero_iff p).mp
    exact Nat.add_eq_zero_iff.mpr hz
  have hquot : finrank F2 (W ⧸ X.ker) ≤ 2*d := by
    have hq := X.ker.finrank_quotient_add_finrank
    have hr := X.finrank_range_add_finrank_ker
    omega
  have hcount (u v : ℕ) : (s.filter (fun p => i p=u ∧ j p=v)).card ≤ 2^(2*d*(u+v)) := by
    let t := s.filter (fun p => i p=u ∧ j p=v)
    let LA := {A : Submodule F2 V // A ≤ X.range ∧ finrank F2 A=u}
    let LB := {B : Submodule F2 W // X.ker ≤ B ∧ finrank F2 (W ⧸ B)=v}
    let code (p : ↥t) : LA × LB := by
      have hp := Finset.mem_filter.mp p.property
      have hg := hs p.val hp.1
      exact (⟨p.val.1, hg.2.1, hp.2.1⟩, ⟨p.val.2, hg.2.2.1, hp.2.2⟩)
    have hi : Function.Injective code := by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : LA × LB => z.1.val) h
      · exact congrArg (fun z : LA × LB => z.2.val) h
    have hc : t.card ≤ Nat.card (LA × LB) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Nat.card_le_card_of_injective code hi
    calc
      _ ≤ Nat.card (LA × LB) := hc
      _ = Nat.card LA * Nat.card LB := Nat.card_prod _ _
      _ ≤ 2^((2*d)*u) * 2^((2*d)*v) := Nat.mul_le_mul
        (card_lower_rank_le X.range (2*d) u hX)
        (card_upper_codim_le X.ker (2*d) v hquot)
      _ = _ := by rw [← pow_add]; congr 1; ring
  simpa only [s, Finset.sum_filter, good, i, j] using
    finite_pair_level_sum_inline_BadConvolution s i j d hd hbound hzero hcount

theorem mobius_sq (i : ℕ) : (mobius i)^2 = (2:ℝ)^(2*i.choose 2) := by
  have hs : ((-1:ℝ)^i)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
    norm_num
  unfold mobius
  rw [mul_pow, hs, one_mul, ← pow_mul, Nat.mul_comm]

private theorem twice_choose_two_le_square_inline_BadConvolution (i : ℕ) : 2*i.choose 2 ≤ i*i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem mobius_pair_sq_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 ≤ (2:ℝ)^(d*(i+j)) := by
  have he : 2*i.choose 2 + 2*j.choose 2 ≤ d*(i+j) := by
    calc
      _ ≤ i*i+j*j := Nat.add_le_add (twice_choose_two_le_square_inline_BadConvolution i)
        (twice_choose_two_le_square_inline_BadConvolution j)
      _ ≤ d*i+d*j := Nat.add_le_add (Nat.mul_le_mul_right i hi) (Nat.mul_le_mul_right j hj)
      _ = _ := (Nat.mul_add d i j).symm
  have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [mul_pow, mobius_sq, mobius_sq, ← pow_add]
  exact_mod_cast hn

theorem mobius_pair_weight_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 * (1/2:ℝ)^(6*d*(i+j)) ≤ (1/2:ℝ)^(5*d*(i+j)) := by
  calc
    _ ≤ (2:ℝ)^(d*(i+j)) * (1/2:ℝ)^(6*d*(i+j)) :=
      mul_le_mul_of_nonneg_right (mobius_pair_sq_le d i j hi hj) (by positivity)
    _ = _ := by
      have he : 6*d*(i+j) = d*(i+j)+5*d*(i+j) := by ring
      rw [he, pow_add, ← mul_assoc, ← mul_pow]
      norm_num

private theorem exists_nonzero_term_inline_BadConvolution {α : Type*} [Fintype α] (f : α → ℝ)
    (h : (∑ x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro x _
  by_contra hx
  exact hn ⟨x,hx⟩

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem filteredCoefficient_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V)
    (h : filteredCoefficient A B a Y ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  have hi : Incidence A B Y := by
    by_contra hn
    exact h (by simp [filteredCoefficient, hn])
  have hay : a Y ≠ 0 := by
    simpa only [filteredCoefficient, ite_eq_left hi] using h
  have hr : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hay (ha Y (Nat.lt_of_not_ge hn))
  have hA := Submodule.finrank_mono hi.1
  have hB := Submodule.finrank_mono hi.2
  have hq := B.finrank_quotient_add_finrank
  have hY := Y.finrank_range_add_finrank_ker
  constructor <;> omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pieceConvolution_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (X : W →ₗ[F2] V)
    (h : pieceConvolution A B a X ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  obtain ⟨Y,hY⟩ := exists_nonzero_term_inline_BadConvolution _ h
  apply filteredCoefficient_nonzero_dimensions a d ha A B Y
  intro hz
  apply hY
  rw [hz, zero_mul]

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem rank_add_le (Y Z : W →ₗ[F2] V) :
    finrank F2 (Y+Z).range ≤ finrank F2 Y.range + finrank F2 Z.range := by
  have hle := Submodule.finrank_mono (LinearMap.range_add_le Y Z)
  have heq := Submodule.finrank_sup_add_finrank_inf_eq Y.range Z.range
  omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem badConvolution_eq_zero_of_large_rank
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : 2*d < finrank F2 X.range) : badConvolution a X = 0 := by
  by_contra h
  obtain ⟨Y,hY⟩ := exists_nonzero_term_inline_BadConvolution _ h
  have hy : a Y ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hz : a (X+Y) ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hry : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hy (ha Y (Nat.lt_of_not_ge hn))
  have hrz : finrank F2 (X+Y).range ≤ d := by
    by_contra hn
    exact hz (ha (X+Y) (Nat.lt_of_not_ge hn))
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  have hr := rank_add_le Y (X+Y)
  rw [hc] at hr
  omega

private theorem scaled_product_inline_BadConvolution (c q : ℝ) (n : ℕ) :
    (c * (1/2:ℝ)^n) * ((2:ℝ)^n * q) = c*q := by
  have hc : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = c * (((1/2:ℝ)^n * (2:ℝ)^n) * q) := by ring
    _ = _ := by rw [hc, one_mul]

theorem badConvolution_sq_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : finrank F2 X.range ≤ 2*d) :
    badConvolution a X ^ 2 ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
      finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
  let s := Finset.univ.filter good
  let u (p : Submodule F2 V × Submodule F2 W) :=
    signedWeight p * (1/2:ℝ)^(3*d*pairDimension p)
  let v (p : Submodule F2 V × Submodule F2 W) :=
    (2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X
  have heq : badConvolution a X = ∑ p ∈ s, u p * v p := by
    rw [badConvolution_expansion, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg]
      rw [ite_eq_left (show Incidence p.1 p.2 X from ⟨hg.2.1,hg.2.2.1⟩)]
      exact (scaled_product_inline_BadConvolution (signedWeight p) (pieceConvolution p.1 p.2 a X)
        (3*d*pairDimension p)).symm
    · rw [ite_eq_right hg]
      by_cases hi : Incidence p.1 p.2 X
      · rw [ite_eq_left hi]
        by_cases hp : p = (⊥,⊤)
        · simp [signedWeight,hp]
        · by_cases hq : pieceConvolution p.1 p.2 a X = 0
          · rw [hq,mul_zero]
          · exact False.elim (hg ⟨hp,hi.1,hi.2,
              pieceConvolution_nonzero_dimensions a d ha p.1 p.2 X hq⟩)
      · rw [ite_eq_right hi]
  have hu : (∑ p ∈ s, u p ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ s, (1/2:ℝ)^(5*d*pairDimension p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hg : good p := (Finset.mem_filter.mp hp).2
        have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
        change (signedWeight p * (1/2:ℝ)^(3*d*pairDimension p))^2 ≤ _
        rw [signedWeight, ite_eq_right hg.1, mul_pow, neg_sq, ← pow_mul, he]
        exact mobius_pair_weight_le d _ _ hg.2.2.2.1 hg.2.2.2.2
      _ ≤ 1 := by
        simpa only [s,Finset.sum_filter,good,pairDimension] using
          incident_pair_weight_le_one X d hd hX
  have hv0 : 0 ≤ ∑ p ∈ s, v p ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (∑ p ∈ s, v p ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg, ite_eq_left hg.1]
      have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
      change ((2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X)^2 ≤ _
      rw [mul_pow, ← pow_mul, he]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hn : 6*d*pairDimension p ≤ 7*d*pairDimension p :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 6 ≤ 7))
      exact_mod_cast Nat.pow_le_pow_right (n := 2) (by decide) hn
    · rw [ite_eq_right hg]
      split_ifs <;> positivity
  calc
    _ = (∑ p ∈ s, u p * v p)^2 := congrArg (fun x : ℝ => x^2) heq
    _ ≤ (∑ p ∈ s, u p^2) * ∑ p ∈ s, v p^2 := Finset.sum_mul_sq_le_sq_mul_sq s u v
    _ ≤ 1 * ∑ p ∈ s, v p^2 := mul_le_mul_of_nonneg_right hu hv0
    _ = ∑ p ∈ s, v p^2 := one_mul _
    _ ≤ _ := hv

/-- The actual signed bad-convolution estimate of A.1. -/
theorem badConvolution_sq_sum_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ X, badConvolution a X ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
          (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0 := by
  calc
    _ ≤ ∑ X, ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hX : finrank F2 X.range ≤ 2*d
      · exact badConvolution_sq_le a d hd ha X hX
      · rw [badConvolution_eq_zero_of_large_rank a d ha X (Nat.lt_of_not_ge hX), zero_pow (by decide)]
        apply Finset.sum_nonneg
        intro p _
        split_ifs <;> positivity
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = (⊥,⊤)
      · simp [hp]
      · simp [hp,pairDimension,Finset.mul_sum]

end MaxCutGames.Appendix.BadConvolution
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A1Reduction
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MaxCutGames.Appendix.A1Reduction
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier MaxCutGames.Fourier.MatrixProducts
open MaxCutGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem weakFourthSum_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ weakFourthSum d f := by
  apply Finset.sum_nonneg
  intro p _
  split
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact le_rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem linearCoeff_weakProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector (fun Z => A ≤ Z.range ∧ Z.ker ≤ B) f) Y =
      BadConvolution.filteredCoefficient A B (linearCoeff f) Y := by
  simp only [linearCoeff_spectralProjector, BadConvolution.filteredCoefficient,
    BadConvolution.Incidence]
  rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
/-- Actual Parseval/product identity for each signed weakly selected piece. -/
theorem piece_fourth_moment (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ X : F →ₗ[F2] E, BadConvolution.pieceConvolution A B (linearCoeff f) X^2) =
      𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M^4 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  simp only [coefficientConvolution, BadConvolution.pieceConvolution,
    linearCoeff_weakProjector]

omit [Finite E] [Finite F] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem actual_bad_cover (X Y : F →ₗ[F2] E) (hbad : ¬ BadConvolution.Bad X Y) :
    F1Energy.Good X Y := by
  apply F1Energy.good_of_trivial_intersections X Y
  · by_contra hi
    exact hbad (Or.inl hi)
  · by_contra hk
    exact hbad (Or.inr hk)

omit [Finite E] [Finite F] [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem badConvolution_zero_of_degree_zero (a : (F →ₗ[F2] E) → ℝ)
    (ha : ∀ Y, 0 < Module.finrank F2 Y.range → a Y = 0) (X : F →ₗ[F2] E) :
    BadConvolution.badConvolution a X = 0 := by
  classical
  unfold BadConvolution.badConvolution
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : Y = 0
  · subst Y
    by_cases hX : X = 0
    · subst X
      simp [BadConvolution.Bad]
    · have hz := ha X (DegreeZero.rank_pos_of_ne_zero X hX)
      simp [hz]
  · have hz := ha Y (DegreeZero.rank_pos_of_ne_zero Y hY)
    simp [hz]

theorem badConvolution_energy_le_weakFourthSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2) ≤
      weakFourthSum d f := by
  by_cases hd : d = 0
  · subst d
    have hz : ∀ X, BadConvolution.badConvolution (linearCoeff f) X = 0 :=
      badConvolution_zero_of_degree_zero (linearCoeff f) hdegree
    simpa only [hz, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Finset.sum_const_zero] using weakFourthSum_nonneg 0 f
  · have h := BadConvolution.badConvolution_sq_sum_le (linearCoeff f) d (by omega) hdegree
    simpa only [weakFourthSum, piece_fourth_moment] using h

theorem fourth_moment_le_two (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * weakFourthSum d f := by
  have hcore : (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * ∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2 := by
    simpa only [BadConvolution.badConvolution] using
      F1Energy.fourth_moment_le_good_bad f d hdegree BadConvolution.Bad actual_bad_cover
  exact hcore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (badConvolution_energy_le_weakFourthSum f d hdegree) (show (0:ℝ) ≤ 2 by norm_num)))

/-- Lemma A.1, Equation (A.6), for every degree d including zero. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) / 162 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 + weakFourthSum d f := by
  have h := fourth_moment_le_two f d hdegree
  have ha : 0 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 := by positivity
  have hb := weakFourthSum_nonneg d f
  apply (div_le_iff₀ (show (0:ℝ) < 162 by norm_num)).mpr
  nlinarith

end MaxCutGames.Appendix.A1Reduction

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

/-- The exponent comparison after retaining the total degree loss. -/
theorem exponent_le (d i j t : ℕ) (hi : i ≤ t) (hj : j ≤ t) (ht : t ≤ d) :
    7 * d * (i + j) + 3 * i * j ≤ 24 * d * t := by
  have hs : i + j ≤ 2 * t := by omega
  have hp : i * j ≤ d * t :=
    (Nat.mul_le_mul hi hj).trans (Nat.mul_le_mul_right t ht)
  have hfirst := Nat.mul_le_mul_left (7 * d) hs
  have hsecond := Nat.mul_le_mul_left 3 hp
  have hdt : 0 ≤ d * t := Nat.zero_le _
  nlinarith

/-- Degree-forced zero moments allow the same weight bound on every raw triple. -/
theorem weighted_moment_le (d i j t : ℕ) (e : ℝ)
    (hi : i ≤ t) (hj : j ≤ t) (he : 0 ≤ e) (hz : d < t → e = 0) :
    (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) * e ≤
      (2 : ℝ) ^ (24 * d * t) * e := by
  by_cases ht : t ≤ d
  · have hn := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (exponent_le d i j t hi hj ht)
    have hr : (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) ≤
        (2 : ℝ) ^ (24 * d * t) := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_right hr he
  · rw [hz (Nat.lt_of_not_ge ht)]
    simp

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleMoment_nonneg (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleMoment p f := by
  apply Finset.expect_nonneg
  intro T _
  apply Finset.expect_nonneg
  intro N _
  positivity

/-- A.4's native fourth-moment bound with its proved binary index count. -/
theorem weak_fourth_le_counted (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
        ∑ p : A4GeometricIndex A B, tripleMoment p.val f := by
  have hnat := Nat.pow_le_pow_left (A4IndexCount.card_index_le A B) 3
  rw [Nat.card_eq_fintype_card, ← pow_mul] at hnat
  have he : (Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * 3 =
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B) := by ring
  rw [he] at hnat
  have hc : (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) := by
    exact_mod_cast hnat
  have hn : 0 ≤ ∑ p : A4GeometricIndex A B, tripleMoment p.val f :=
    Finset.sum_nonneg fun p _ => tripleMoment_nonneg p.val f
  exact (OperatorNorm.a4_fourth_average_le A B f).trans
    (mul_le_mul_of_nonneg_right hc hn)

/-- Expand one original weak-pair term, retaining its original dimensions. -/
theorem weighted_weak_fourth_le_counted (d : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
      (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    ∑ p : A4GeometricIndex A B,
      (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
        3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f := by
  calc
    _ ≤ (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
        ((2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
          ∑ p : A4GeometricIndex A B, tripleMoment p.val f) :=
      mul_le_mul_of_nonneg_left (weak_fourth_le_counted A B f) (by positivity)
    _ = _ := by simp only [pow_add, Finset.mul_sum, mul_assoc]

theorem tripleMoment_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleMoment p f = 0 :=
  DerivativeDegree.map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    p.1 p.2.1 p.2.2 f hf h

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleTerm_nonneg (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleTerm d p f :=
  mul_nonneg (by positivity) (tripleMoment_nonneg p f)

theorem tripleTerm_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleTerm d p f = 0 := by
  unfold tripleTerm
  rw [tripleMoment_eq_zero_of_lt_size p f hf h, mul_zero]

theorem weighted_geometric_moment_le {d : ℕ}
    (A : Submodule F2 E) (B : Submodule F2 F)
    (p : A4GeometricIndex A B) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f ≤
      tripleTerm d p.val f := by
  have hi : Module.finrank F2 A ≤ A13Index.size p.val := by
    have h := A13Index.dim_weakA p
    unfold A13Index.size MatrixRestrictions.order
    omega
  have hj : Module.finrank F2 (F ⧸ B) ≤ A13Index.size p.val := by
    have h := A13Index.codim_weakB p
    unfold A13Index.size MatrixRestrictions.order
    omega
  exact weighted_moment_le d _ _ _ _ hi hj (tripleMoment_nonneg p.val f)
    (fun h => tripleMoment_eq_zero_of_lt_size p.val f hf h)

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- Apply A.4 and its count, then forget the uniquely reconstructible weak pair.
The old nonzero condition is carried by `positiveMap`; no descendant condition
is substituted for it. -/
theorem weakFourthSum_le_positiveTripleSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    A1Reduction.weakFourthSum d f ≤ positiveTripleSum d f := by
  classical
  have heq : A1Reduction.weakFourthSum d f =
      ∑ p : A13Index.WeakPositive (E := E) (F := F),
        (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.val.1 +
          Module.finrank F2 (F ⧸ p.val.2))) *
          (𝔼 M, spectralProjector
            (fun Y => p.val.1 ≤ Y.range ∧ Y.ker ≤ p.val.2) f M ^ 4) := by
    symm
    exact F1Gram.sum_subtype_eq
      (fun p : Submodule F2 E × Submodule F2 F => p ≠ (⊥, ⊤))
      (fun p => (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.1 +
        Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M ^ 4))
  rw [heq]
  calc
    _ ≤ ∑ p : A13Index.WeakPositive (E := E) (F := F),
        ∑ q : A4GeometricIndex p.val.1 p.val.2, tripleTerm d q.val f := by
      apply Finset.sum_le_sum
      intro p _
      exact (weighted_weak_fourth_le_counted d p.val.1 p.val.2 f).trans
        (Finset.sum_le_sum fun q _ => weighted_geometric_moment_le p.val.1 p.val.2 q f hf)
    _ = ∑ w : A13Index.PositiveWitness (E := E) (F := F),
        tripleTerm d w.2.val f := by
      simp only [Fintype.sum_sigma]
    _ ≤ positiveTripleSum d f :=
      F1Gram.sum_comp_le A13Index.positiveMap A13Index.positiveMap_injective
        (fun q : A13Index.PositiveTriple (E := E) (F := F) => tripleTerm d q.val f)
        (fun q => tripleTerm_nonneg d q.val f)

theorem positiveTripleSum_eq_bounded (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    positiveTripleSum d f = boundedPositiveTripleSum d f := by
  classical
  unfold positiveTripleSum boundedPositiveTripleSum
  rw [F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) => 0 < A13Index.size p)
      (fun p => tripleTerm d p f),
    F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) =>
        0 < A13Index.size p ∧ A13Index.size p ≤ d)
      (fun p => tripleTerm d p f)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < A13Index.size p
  · by_cases ht : A13Index.size p ≤ d
    · rw [ite_eq_left hp, ite_eq_left ⟨hp, ht⟩]
    · rw [ite_eq_left hp, ite_eq_right (fun h => ht h.2)]
      exact tripleTerm_eq_zero_of_lt_size p f hf (Nat.lt_of_not_ge ht)
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

/-- Equation A.13 with the literal positive-triple sum. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + positiveTripleSum d f := by
  have hbase := A1Reduction.degree_reduction f d (fun Y hY => hf Y hY)
  exact hbase.trans (add_le_add le_rfl (weakFourthSum_le_positiveTripleSum f d hf))

/-- Equation A.13 after removing terms whose actual derivative is zero. -/
theorem degree_reduction_truncated_oai (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  simpa only [positiveTripleSum_eq_bounded f d hf] using degree_reduction f d hf

end MaxCutGames.Appendix.A13Reduction
end

/-!
# Exact antecedents of quotient compression

This is the reverse-map count used in Proposition A.5. The compressed map is
fixed, together with the two removed subspaces; neither a prescribed rank nor
an assumed cardinality is part of the antecedent predicate.
-/

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated_oai.{u_1, u_2} := @OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated_oai.{u_1, u_2}
