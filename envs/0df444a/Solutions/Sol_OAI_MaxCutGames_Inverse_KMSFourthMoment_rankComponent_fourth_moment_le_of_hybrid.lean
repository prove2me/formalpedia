-- Prove2me | solution 1 for OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:57:23.578919+00:00
-- url     : https://prove2.me/submissions/f81bbd4c-95b6-4519-a807-1f81066b8181

import Mathlib
import Definitions.Def_OAIQ087A009
import Definitions.Def_OAIQ087A012
import Theorems.Thm_OAI_MaxCutGames_Appendix_A13Reduction_degree_reduction_truncated

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Deletion
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

omit [FiniteDimensional K V] in
theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

omit [FiniteDimensional K V] in
theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

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
theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

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

omit [FiniteDimensional F2 C] in
/-- Lemma A.2 in arbitrary finite-dimensional block coordinates. -/
theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end MaxCutGames.Appendix.CompressionCount

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace MaxCutGames.Fourier.MatrixSubspaceCount

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

section GeneralField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Taking the image of an endomorphism reaches every actual subspace. -/
theorem endomorphism_range_surjective :
    Function.Surjective (fun f : V →ₗ[K] V => LinearMap.range f) := by
  intro S
  obtain ⟨T, hT⟩ := S.exists_isCompl
  exact ⟨S.projection T hT, Submodule.range_projection hT⟩

theorem card_subspaces_le_endomorphisms [Finite V] :
    Nat.card (Submodule K V) ≤ Nat.card (V →ₗ[K] V) := by
  let : Finite (V →ₗ[K] V) := Finite.of_injective
    (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Nat.card_le_card_of_surjective _ endomorphism_range_surjective

end GeneralField

variable {C : Type*} [AddCommGroup C] [Module F2 C] [Module.Finite F2 C]

private theorem finite_color_space_inline_MatrixSubspaceCount : Finite C :=
  Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective

theorem card_binary_subspaces_le :
    Nat.card (Submodule F2 C) ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite C := finite_color_space_inline_MatrixSubspaceCount
  calc
    _ ≤ Nat.card (C →ₗ[F2] C) := card_subspaces_le_endomorphisms
    _ = _ := MaxCutGames.Appendix.CompressionCount.natCard_linearMap

theorem card_binary_subspaces_le_of_finrank_le (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (Submodule F2 C) ≤ 2 ^ (s * s) := by
  exact card_binary_subspaces_le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs))

end MaxCutGames.Fourier.MatrixSubspaceCount

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

theorem compress_sub (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    compress (Y - X) A B = compress Y A B - compress X A B := by
  ext b
  simp only [compress_apply, LinearMap.sub_apply, map_sub]

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

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
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

omit [FiniteDimensional K V] in
/-- The reverse summand of (A.5) really satisfies the hybrid selector for
the remainder `Y - X`. The hypotheses here are exactly the inner hybrid
selector, complement conditions, and the compressed rank-order selector.
No image-lifting or disjointness conclusion is assumed separately. -/
theorem reverse_hybrid_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (Y - X) A₀ B₀ := by
  have hker := RankAdditivity.ker_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  have himg := RankAdditivity.range_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hxA : X w ∈ A₀ := by
      have hx : X w ∈ LinearMap.ker A₀.mkQ := hker hwy
      simpa only [Submodule.ker_mkQ] using hx
    have hx : X w = 0 := Submodule.disjoint_def.mp hdis (X w) hxA ⟨w, rfl⟩
    exact ⟨w, by change Y w - X w = a; rw [hw, hx, sub_zero]⟩
  · intro w hw
    have hwZ : Y w - X w ∈ A₀ := hw
    have hwtop : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    have hxb : X b = X w := by
      rw [← hbk, map_add, show X k = 0 from hk, add_zero]
    have hxran : compress X A₀ B₀ ⟨b, hb⟩ ∈ LinearMap.range (compress X A₀ B₀) :=
      ⟨⟨b, hb⟩, rfl⟩
    rcases himg hxran with ⟨c, hc⟩
    have hdiff : X w - Y c ∈ A₀ := by
      rw [← hxb]
      exact (Submodule.Quotient.eq A₀).mp hc.symm
    have hsum : Y (w - c) ∈ A₀ := by
      have h := A₀.add_mem hwZ hdiff
      have heq : (Y w - X w) + (X w - Y c) = Y (w - c) := by rw [map_sub]; abel
      exact heq ▸ h
    have hwc : w - c ∈ B₀ := inner.2 hsum
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

omit [FiniteDimensional K V] in
/-- A surviving right-hand summand of (A.5) forces the original rank
order `X ⪯ Y`. This lifts the local rank equation using the two actual
hybrid rank-loss equalities, so it does not assume global rank additivity. -/
theorem rankBelow_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    RankAdditivity.RankBelow X Y := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y inner.1 inner.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) remainder.1 remainder.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  have hloc : Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
      Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
      Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) := by
    rw [compress_sub]
    exact hlocal
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X))
  omega

omit [FiniteDimensional K V] in
/-- The complement in the codomain is forced by the remainder image. -/
theorem image_inter_complement_eq (A₀ I J : Submodule K V)
    (hA : A₀ ≤ J) (hdis : Disjoint I J) : J ⊓ (A₀ ⊔ I) = A₀ := by
  apply le_antisymm
  · intro v hv
    rcases Submodule.mem_sup.mp hv.2 with ⟨a, ha, i, hi, hai⟩
    have hiJ : i ∈ J := by
      have h := J.sub_mem hv.1 (hA ha)
      have heq : v - a = i := by rw [← hai]; abel
      exact heq ▸ h
    have hi0 := Submodule.disjoint_def.mp hdis i hi hiJ
    rw [hi0, add_zero] at hai
    exact hai ▸ ha
  · intro a ha
    exact ⟨hA ha, (show A₀ ≤ A₀ ⊔ I from le_sup_left) ha⟩

omit [FiniteDimensional K W] in
/-- The complement in the domain is forced by the remainder kernel. -/
theorem domain_complement_eq (B₀ K₀ J : Submodule K W)
    (hJ : J ≤ B₀) (hcover : K₀ ⊔ J = ⊤) : B₀ = (B₀ ⊓ K₀) ⊔ J := by
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ K₀ ⊔ J := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨k, hk, j, hj, hkj⟩
    have hkB : k ∈ B₀ := by
      have h := B₀.sub_mem hw (hJ hj)
      have heq : w - j = k := by rw [← hkj]; abel
      exact heq ▸ h
    exact Submodule.mem_sup.mpr ⟨k, ⟨hkB, hk⟩, j, hj, hkj⟩
  · exact sup_le inf_le_left hJ

omit [FiniteDimensional K V] in
/-- Every surviving right-hand pair in (A.5) is the displayed canonical pair. -/
theorem surviving_pair_forced (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    A₀ = LinearMap.range (Y - X) ⊓ A ∧ B₀ = B ⊔ LinearMap.ker (Y - X) := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have global := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have geometry := (RankAdditivity.rankBelow_iff X Y).mp global
  constructor
  · have h := image_inter_complement_eq A₀ (LinearMap.range X)
      (LinearMap.range (Y - X)) remainder.1 geometry.1
    rw [hA] at h
    exact h.symm
  · have hker : LinearMap.ker (Y - X) ≤ B₀ := by
      intro w hw
      apply remainder.2
      change (Y - X) w ∈ A₀
      rw [show (Y - X) w = 0 from hw]
      exact A₀.zero_mem
    have h := domain_complement_eq B₀ (LinearMap.ker X) (LinearMap.ker (Y - X)) hker geometry.2
    rw [hB] at h
    exact h

omit [FiniteDimensional K V] in
theorem canonical_inner_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid Y (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · have hz : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
      rw [RankAdditivity.range_remainder_eq_range_on_kernel X Y hrank]
      exact LinearMap.range_domRestrict_le_range Y (LinearMap.ker X)
    exact inf_le_left.trans hz
  · intro w hw
    have hy : Y w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hk : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hrank w hy.1
    have hq : (⟨w, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y w, hy.2, rfl⟩
    have hb : w ∈ B := outer.2 hq
    exact (show B ≤ B ⊔ LinearMap.ker (Y - X) from le_sup_left) hb

omit [FiniteDimensional K V] in
theorem canonical_remainder_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid (Y - X) (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · exact inf_le_left
  · intro w hw
    have hwZ : (Y - X) w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    have hyk : Y k = (Y - X) w := by
      calc
        Y k = (Y - X) k := by
          change Y k = Y k - X k
          rw [show X k = 0 from hk, sub_zero]
        _ = (Y - X) w := hzk
    have hyA : Y k ∈ A := by rw [hyk]; exact hwZ.2
    have hq : (⟨k, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y k, hyA, rfl⟩
    have hkB : k ∈ B := outer.2 hq
    exact Submodule.mem_sup.mpr ⟨k, hkB, j, hj, hkj⟩

omit [FiniteDimensional K V] in
theorem canonical_codomain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Disjoint (LinearMap.range (Y - X) ⊓ A) (LinearMap.range X) ∧
      (LinearMap.range (Y - X) ⊓ A) ⊔ LinearMap.range X = A := by
  have hd := ((RankAdditivity.rankBelow_iff X Y).mp hrank).1
  refine ⟨hd.symm.mono_left inf_le_left, ?_⟩
  apply le_antisymm (sup_le inf_le_right hI)
  intro a ha
  have hqa : (LinearMap.range X).mkQ a ∈ A.map (LinearMap.range X).mkQ := ⟨a, ha, rfl⟩
  rcases outer.1 hqa with ⟨k, hk⟩
  have hi : a - Y k ∈ LinearMap.range X :=
    (Submodule.Quotient.eq (LinearMap.range X)).mp hk.symm
  have hyA : Y k ∈ A := by
    have h := A.sub_mem ha (hI hi)
    have heq : a - (a - Y k) = Y k := by abel
    exact heq ▸ h
  have hyZ : Y k ∈ LinearMap.range (Y - X) :=
    ⟨(k : W), by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]⟩
  exact Submodule.mem_sup.mpr ⟨Y k, ⟨hyZ, hyA⟩, a - Y k, hi, by abel⟩

omit [FiniteDimensional K V] in
theorem canonical_domain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hB : B ≤ LinearMap.ker X) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    (B ⊔ LinearMap.ker (Y - X)) ⊓ LinearMap.ker X = B ∧
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X = ⊤ := by
  constructor
  · apply le_antisymm
    · intro w hw
      rcases Submodule.mem_sup.mp hw.1 with ⟨b, hb, j, hj, hbj⟩
      have hjK : j ∈ LinearMap.ker X := by
        have h := (LinearMap.ker X).sub_mem hw.2 (hB hb)
        have heq : w - b = j := by rw [← hbj]; abel
        exact heq ▸ h
      have hyj : Y j = 0 := by
        have hz : Y j - X j = 0 := hj
        rw [show X j = 0 from hjK, sub_zero] at hz
        exact hz
      have hq : (⟨j, hjK⟩ : LinearMap.ker X) ∈
          (A.map (LinearMap.range X).mkQ).comap
            (compress Y (LinearMap.range X) (LinearMap.ker X)) := by
        change (LinearMap.range X).mkQ (Y j) ∈ A.map (LinearMap.range X).mkQ
        rw [hyj, map_zero]
        exact Submodule.zero_mem _
      have hjB : j ∈ B := outer.2 hq
      have h := B.add_mem hb hjB
      exact hbj ▸ h
    · exact le_inf le_sup_left hB
  · have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    calc
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X =
        B ⊔ (LinearMap.ker X ⊔ LinearMap.ker (Y - X)) := by ac_rfl
      _ = ⊤ := by rw [hc, sup_top_eq]

omit [FiniteDimensional K V] in
theorem compressed_rankBelow_of_hybrids (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (hy : Hybrid Y A₀ B₀) (hz : Hybrid (Y - X) A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hrank : RankAdditivity.RankBelow X Y) :
    RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀) := by
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y hy.1 hy.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) hz.1 hz.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X)) at hrank
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
    Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
    Module.finrank K (LinearMap.range (compress Y A₀ B₀ - compress X A₀ B₀))
  rw [← compress_sub]
  omega

omit [FiniteDimensional K V] in
theorem reverse_outer_hybrid (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype) := by
  have hg := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hz := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hf := surviving_pair_forced X Y A₀ A B B₀ inner hdis hA hcover hB hlocal
  have hI : LinearMap.range X ≤ A := by rw [← hA]; exact le_sup_right
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    have haSum : a ∈ A₀ ⊔ LinearMap.range X := by rw [hA]; exact ha
    rcases Submodule.mem_sup.mp haSum with ⟨a₀, ha₀, i, hi, hai⟩
    rcases inner.1 ha₀ with ⟨w, hw⟩
    have hyZ : Y w ∈ LinearMap.range (Y - X) := by rw [hw]; exact hz.1 ha₀
    have hwK : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hg w hyZ
    refine ⟨⟨w, hwK⟩, ?_⟩
    have hqi : (LinearMap.range X).mkQ i = 0 := by
      change i ∈ LinearMap.ker (LinearMap.range X).mkQ
      rw [Submodule.ker_mkQ]
      exact hi
    change (LinearMap.range X).mkQ (Y w) = (LinearMap.range X).mkQ a
    rw [hw, ← hai, map_add, hqi, add_zero]
  · intro k hk
    have hyA : Y k ∈ A :=
      (quotient_mem_image_iff (LinearMap.range X) A hI (Y k)).mp hk
    have hZk : (Y - X) k = Y k := by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]
    have hyZ : Y k ∈ LinearMap.range (Y - X) := ⟨(k : W), hZk⟩
    have ha₀ : Y k ∈ A₀ := by rw [hf.1]; exact ⟨hyZ, hyA⟩
    have hkB₀ : (k : W) ∈ B₀ := hz.2 (by
      change (Y - X) k ∈ A₀
      rw [hZk]
      exact ha₀)
    change (k : W) ∈ B
    rw [← hB]
    exact ⟨hkB₀, k.property⟩

omit [FiniteDimensional K V] in
/-- The complete unique-summand selector identity in (A.5), in arbitrary
finite dimensions. In characteristic two the remainder `Y-X` is `Y+X`. -/
theorem a5_unique_selector (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hB : B ≤ LinearMap.ker X) :
    (RankAdditivity.RankBelow X Y ∧
      Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
        (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) ↔
      ∃! p : Submodule K V × Submodule K W, A5PairSurvives X Y A B p := by
  constructor
  · rintro ⟨hr, ho⟩
    have hy := canonical_inner_hybrid X Y A B hr ho
    have hz := canonical_remainder_hybrid X Y A B hr ho
    have ha := canonical_codomain_complement X Y A B hI hr ho
    have hb := canonical_domain_complement X Y A B hB hr ho
    have hl := compressed_rankBelow_of_hybrids X Y
      (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) hy hz ha.1 hb.2 hr
    refine ⟨(LinearMap.range (Y - X) ⊓ A, B ⊔ LinearMap.ker (Y - X)),
      ⟨hy, ha.1, ha.2, hb.2, hb.1, hl⟩, ?_⟩
    rintro ⟨A₀, B₀⟩ hp
    rcases hp with ⟨hi, hd, ha', hc, hb', hl'⟩
    have hf := surviving_pair_forced X Y A₀ A B B₀ hi hd ha' hc hb' hl'
    exact Prod.ext hf.1 hf.2
  · rintro ⟨⟨A₀, B₀⟩, hp, _⟩
    rcases hp with ⟨hi, hd, ha, hc, hb, hl⟩
    exact ⟨rankBelow_of_compressed_rankBelow X Y A₀ B₀ hi hd hc hl,
      reverse_outer_hybrid X Y A₀ A B B₀ hi hd ha hc hb hl⟩

/-! ## The unique selector in (A.4) -/

end MaxCutGames.Appendix.LinearIdentities

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CoordinateTransport
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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
/-- Lemma A.2: every compressed rank-r map has exactly `2^(2*k*r)`
rank-additive lifts above an arbitrary rank-k map X. -/
theorem card_fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
    Nat.card (Fiber X Z) = 2 ^ (2 * finrank F2 X.range * finrank F2 Z.range) := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  rw [Nat.card_congr (fiberEquiv X Z P hP C hC), CompressionCount.card_fiber,
    finrank_comp_equiv]

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

namespace MaxCutGames.Appendix.FiberEnergy

open scoped BigOperators

variable {α β R : Type*} [Fintype β] [DecidableEq β] [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R]

/-- The energy of a sum of merged coefficients is bounded by the largest
fiber size times the original coefficient energy. Signs and cancellations
are unrestricted; no injectivity assumption is made. -/
theorem finite_fiber_energy (s : Finset α) (compress : α → β) (a : α → R)
    (bound : R) (hbound : ∀ z,
      ((s.filter (fun y => compress y = z)).card : R) ≤ bound) :
    (∑ z, (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2) ≤
      bound * ∑ y ∈ s, a y ^ 2 := by
  classical
  have hlocal (z : β) :
      (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2 ≤
        bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (s.filter (fun y => compress y = z)) (fun _ => (1 : R)) a
    calc
      _ ≤ ((s.filter (fun y => compress y = z)).card : R) *
          ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by simpa using hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound z)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ z, bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = bound * ∑ y ∈ s, a y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

end MaxCutGames.Appendix.FiberEnergy

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/
namespace MaxCutGames.Appendix.DerivativeEnergy

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Module
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity (RankBelow)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 F] in
theorem supported_fiber_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (s : Finset (E →ₗ[F2] F)) (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d) :
    (∑ Z, (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y ∈ s, a Y^2 := by
  classical
  apply FiberEnergy.finite_fiber_energy
  intro Z
  let t := s.filter (fun Y => FullCompression.compression X Y = Z)
  by_cases ht : t.Nonempty
  · obtain ⟨Y, hY⟩ := ht
    have hy := Finset.mem_filter.mp hY
    have hys := hs Y hy.1
    let yz : FullCompression.Fiber X Z := ⟨Y, hys.1, hy.2⟩
    have hr := FullCompression.fiber_rank X Z yz
    have hz : finrank F2 Z.range ≤ d - finrank F2 X.range := by
      change finrank F2 Y.range = finrank F2 X.range + finrank F2 Z.range at hr
      omega
    let emb : ↥t → FullCompression.Fiber X Z := fun y =>
      ⟨y.val, (hs y.val (Finset.mem_filter.mp y.property).1).1,
        (Finset.mem_filter.mp y.property).2⟩
    have hemb : Function.Injective emb := by
      intro y y' h
      have hv : y.val = y'.val :=
        congrArg (fun z : FullCompression.Fiber X Z => z.val) h
      exact Subtype.ext hv
    let : Finite (FullCompression.Fiber X Z) :=
      Finite.of_injective (fun z : FullCompression.Fiber X Z => z.val)
        (fun _ _ h => Subtype.ext h)
    have hc : t.card ≤ Nat.card (FullCompression.Fiber X Z) := by
      have h := Nat.card_le_card_of_injective emb hemb
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
    rw [FullCompression.card_fiber X Z] at hc
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (Nat.mul_le_mul_left (2 * finrank F2 X.range) hz)
    have hnat : t.card ≤ 2^(2 * finrank F2 X.range * (d - finrank F2 X.range)) :=
      hc.trans hpow
    exact_mod_cast hnat
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

omit [FiniteDimensional F2 F] in
/-- The precise merged-coefficient form of (A.10). Coefficients are arbitrary
real numbers with the stated degree support, not assumed nonnegative. -/
theorem coefficient_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hdegree : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
      then a Y else 0)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
  classical
  let s := Finset.univ.filter (fun Y : E →ₗ[F2] F =>
    RankBelow X Y ∧ finrank F2 Y.range ≤ d)
  have hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d := by
    intro Y hY
    exact (Finset.mem_filter.mp hY).2
  have hsum (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
      (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y) =
        ∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z then a Y else 0 := by
    simp only [s, Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  have henergy : (∑ Y ∈ s, a Y^2) =
      ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  simpa only [hsum, henergy] using supported_fiber_energy X s a d hs

end MaxCutGames.Appendix.DerivativeEnergy

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

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

omit [Module.Finite K V] in
/-- Evaluating on a basis bounds the number of linear maps without counting
arbitrary functions on every vector. -/
theorem card_linearMaps_le [Finite V] :
    Nat.card (U →ₗ[K] V) ≤ Nat.card V ^ finrank K U := by
  let b := Module.finBasis K U
  let code : (U →ₗ[K] V) → (Fin (finrank K U) → V) := fun f i => f (b i)
  have hi : Function.Injective code := by
    intro f g h
    apply b.ext
    exact congrFun h
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hi

omit [Module.Finite K V] in
/-- Every rank-k map factors through the actual coordinate vector space K^k. -/
theorem exists_rank_factorization (f : U →ₗ[K] V) (k : ℕ)
    (hk : finrank K (LinearMap.range f) = k) :
    ∃ (a : (Fin k → K) →ₗ[K] V) (b : U →ₗ[K] (Fin k → K)), a.comp b = f := by
  let e := (Module.finBasisOfFinrankEq K (LinearMap.range f) hk).equivFun
  refine ⟨(LinearMap.range f).subtype.comp e.symm.toLinearMap,
    e.toLinearMap.comp f.rangeRestrict, ?_⟩
  ext x
  simp

/-- Rank-k maps between r- and s-dimensional spaces number at most |K|^((r+s)k).
This is a general finite-field bound, proved by selecting the preceding
factorization and injecting into the pair of factor maps. -/
theorem card_rank_maps_le [Finite K] (k : ℕ) :
    Nat.card {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k} ≤
      Nat.card K ^ ((finrank K U + finrank K V) * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis K U).equivFun
    (Module.finBasis K U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let A := (Fin k → K) →ₗ[K] V
  let B := U →ₗ[K] (Fin k → K)
  let : Finite A := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite B := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hf (f : {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k}) :
      ∃ p : A × B, p.1.comp p.2 = f.1 := by
    obtain ⟨a, b, h⟩ := exists_rank_factorization f.1 k f.2
    exact ⟨(a, b), h⟩
  let code := fun f => Classical.choose (hf f)
  have hi : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    calc
      f.1 = (code f).1.comp (code f).2 := (Classical.choose_spec (hf f)).symm
      _ = (code g).1.comp (code g).2 := congrArg (fun p : A × B => p.1.comp p.2) h
      _ = g.1 := Classical.choose_spec (hf g)
  calc
    _ ≤ Nat.card (A × B) := Nat.card_le_card_of_injective code hi
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _
    _ ≤ Nat.card V ^ k * (Nat.card K ^ k) ^ finrank K U := by
      apply Nat.mul_le_mul
      · simpa [A] using card_linearMaps_le (K := K) (U := Fin k → K) (V := V)
      · simpa [B, Nat.card_fun] using
          card_linearMaps_le (K := K) (U := U) (V := Fin k → K)
    _ = Nat.card K ^ ((finrank K U + finrank K V) * k) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := V)]
      simp only [← pow_mul, ← pow_add]
      congr 1
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

omit [Module.Finite K V] [Module.Finite K U] in
theorem rank_quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    finrank K (LinearMap.range (quotientImageMap Y X hker himage)) =
      finrank K (LinearMap.range X) := by
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range Y), ← LinearMap.range_comp]
  change finrank K (LinearMap.range ((LinearMap.ker Y).liftQ X hker)) = _
  rw [Submodule.range_liftQ]

omit [Module.Finite K V] in
/-- General ambient-independent rank-k bound for maps constrained by the image
and kernel of Y. This counts actual linear maps; neither cardinality nor
rank-additive predecessor estimates are supplied as hypotheses. -/
theorem card_constrained_maps_le [Finite K] (Y : U →ₗ[K] V) (k : ℕ) :
    Nat.card {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} ≤
      Nat.card K ^ (2 * finrank K (LinearMap.range Y) * k) := by
  classical
  let : Finite (LinearMap.range Y) := Finite.of_injective
    (Module.finBasis K (LinearMap.range Y)).equivFun
    (Module.finBasis K (LinearMap.range Y)).equivFun.injective
  let : Finite (U ⧸ LinearMap.ker Y) := Finite.of_injective
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun.injective
  let : Finite ((U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y}) :
      {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} :=
    ⟨quotientImageMap Y X.1 X.2.2.1 X.2.2.2,
      (rank_quotientImageMap Y X.1 X.2.2.1 X.2.2.2).trans X.2.1⟩
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    ext u
    have he := congrArg
      (fun f => ((f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y)
        ((LinearMap.ker Y).mkQ u) : V)) (congrArg Subtype.val h)
    exact he
  have hdim : finrank K (U ⧸ LinearMap.ker Y) = finrank K (LinearMap.range Y) := by
    have hq := (LinearMap.ker Y).finrank_quotient_add_finrank
    have hr := Y.finrank_range_add_finrank_ker
    omega
  calc
    _ ≤ Nat.card {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} := Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card K ^ ((finrank K (U ⧸ LinearMap.ker Y) +
        finrank K (LinearMap.range Y)) * k) :=
      card_rank_maps_le (K := K) (U := U ⧸ LinearMap.ker Y) (V := LinearMap.range Y) k
    _ = _ := by rw [hdim, ← two_mul]

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module (ZMod 2) U] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V] in
theorem binary_add_cancel (X Y : U →ₗ[ZMod 2] V) : X + (Y + X) = Y := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hself (x : V) : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, htwo, zero_smul]
  ext u
  change X u + (Y u + X u) = Y u
  rw [add_comm (Y u) (X u), ← add_assoc, hself, zero_add]

theorem card_binary_predecessors_le (Y : U →ₗ[ZMod 2] V) (d k : ℕ)
    (hd : finrank (ZMod 2) (LinearMap.range Y) ≤ d) :
    Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))} ≤ 2 ^ (3 * d * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis (ZMod 2) U).equivFun
    (Module.finBasis (ZMod 2) U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis (ZMod 2) V).equivFun
    (Module.finBasis (ZMod 2) V).equivFun.injective
  let : Finite (U →ₗ[ZMod 2] V) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))}) :
      {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} := by
    have hr : finrank (ZMod 2) (LinearMap.range (X.1 + (Y + X.1))) =
        finrank (ZMod 2) (LinearMap.range X.1) +
        finrank (ZMod 2) (LinearMap.range (Y + X.1)) := by
      rw [binary_add_cancel]
      exact X.2.2
    refine ⟨X.1, X.2.1, ?_, ?_⟩
    · simpa only [binary_add_cancel] using
        RankAdditivity.ker_add_le_ker_left X.1 (Y + X.1) hr
    · simpa only [binary_add_cancel] using
        RankAdditivity.range_left_le_range_add X.1 (Y + X.1) hr
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    change (code X).1 = (code Z).1
    exact congrArg Subtype.val h
  calc
    _ ≤ Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} :=
      Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card (ZMod 2) ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) :=
      card_constrained_maps_le (K := ZMod 2) Y k
    _ = 2 ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) := by simp
    _ ≤ 2 ^ (3 * d * k) := by
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.mul_le_mul_right
      omega

end MaxCutGames.Appendix.SubspaceCounting

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

namespace MaxCutGames.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

private lemma half_cancel_inline_WeightedFourthMoment (a b : ℕ) :
    (2:ℝ)^a * ((2:ℝ)⁻¹)^(a+b) = ((2:ℝ)⁻¹)^b := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma half_sum_identity_inline_WeightedFourthMoment (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) + 2*((2:ℝ)⁻¹)^n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    norm_num at *
    linarith

private lemma half_sum_le_inline_WeightedFourthMoment (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) ≤ 2 := by
  have hid := half_sum_identity_inline_WeightedFourthMoment n
  have hp : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
  linarith

private lemma finite_level_sum_inline_WeightedFourthMoment {α : Type*} (s : Finset α) (r : α → ℕ) (d : ℕ)
    (hdeg : ∀ x ∈ s, r x ≤ d)
    (hc : ∀ k, ((s.filter (fun x => r x=k)).card : ℝ) ≤ (2:ℝ)^(3*d*k)) :
    (∑ x ∈ s, ((2:ℝ)⁻¹)^(4*d*r x)) ≤ 2 := by
  classical
  have hmap : ∀ x ∈ s, r x ∈ Finset.range (d+1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg x hx))
  have hone (n : ℕ) : ((2:ℝ)⁻¹)^n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
      norm_num at *
      nlinarith
  calc
    _ = ∑ k ∈ Finset.range (d+1), ∑ x ∈ s.filter (fun x => r x=k),
        ((2:ℝ)⁻¹)^(4*d*r x) :=
      (Finset.sum_fiberwise_of_maps_to (g := r) hmap _).symm
    _ ≤ ∑ k ∈ Finset.range (d+1), ((2:ℝ)⁻¹)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hmul : k ≤ d*k := by
        by_cases hd : d=0
        · subst d
          have : k=0 := by omega
          simp [this]
        · have : 1 ≤ d := by omega
          simpa using Nat.mul_le_mul_right k this
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmul
      have hdecay : ((2:ℝ)⁻¹)^(d*k) ≤ ((2:ℝ)⁻¹)^k := by
        rw [hj, pow_add]
        simpa using mul_le_mul_of_nonneg_left (hone j)
          (by positivity : 0 ≤ ((2:ℝ)⁻¹)^k)
      calc
        _ = ((s.filter (fun x => r x=k)).card : ℝ)*((2:ℝ)⁻¹)^(4*d*k) := by
          calc
            _ = ∑ x ∈ s.filter (fun x => r x=k), ((2:ℝ)⁻¹)^(4*d*k) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
            _ = _ := by simp
        _ ≤ (2:ℝ)^(3*d*k)*((2:ℝ)⁻¹)^(4*d*k) :=
          mul_le_mul_of_nonneg_right (hc k) (by positivity)
        _ = ((2:ℝ)⁻¹)^(d*k) := by
          have he : 4*d*k=3*d*k+d*k := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel_inline_WeightedFourthMoment]
        _ ≤ _ := hdecay
    _ ≤ 2 := half_sum_le_inline_WeightedFourthMoment (d+1)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

/-- Sum of predecessor weights, using the actual binary linear-map count. -/
theorem predecessor_weight_sum (Y : E →ₗ[F2] F) (d : ℕ) (hd : rank Y ≤ d) :
    (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
      ((2:ℝ)⁻¹)^(4*d*rank X)) ≤ 2 := by
  classical
  apply finite_level_sum_inline_WeightedFourthMoment _ rank d
  · intro X hX
    have hp := (Finset.mem_filter.mp hX).2
    change rank Y = rank X + rank (Y-X) at hp
    omega
  · intro k
    have hneg (X : E →ₗ[F2] F) : -X = X := by
      have htwo : (1+1:F2)=0 := by decide
      have hxx : X+X=0 := by
        have h := congrArg (fun c:F2 => c • X) htwo
        simpa only [add_smul, one_smul, zero_smul] using h
      exact neg_eq_iff_add_eq_zero.mpr hxx
    have hpred (X : E →ₗ[F2] F) : RankBelow X Y ↔
        rank Y = rank X + rank (Y+X) := by
      change (rank Y = rank X + rank (Y-X)) ↔ _
      rw [sub_eq_add_neg, hneg X]
    have hc := SubspaceCounting.card_binary_predecessors_le Y d k hd
    have hn : ((Finset.univ.filter (fun X => RankBelow X Y)).filter
        (fun X => rank X=k)).card ≤ 2^(3*d*k) := by
      simp_rw [hpred]
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter,
        and_comm, rank] using hc
    exact_mod_cast hn

/-- Corrected Appendix A.4, in exact coefficient form, for arbitrary real
coefficients supported on maps of rank at most d. -/
theorem weighted_fourth_coefficient_energy (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2 := by
  classical
  let A : ℝ := ∑ Y, a Y^2
  let AX (X : E →ₗ[F2] F) : ℝ := ∑ Y, if RankBelow X Y then a Y^2 else 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAX (X : E →ₗ[F2] F) : 0 ≤ AX X := by
    apply Finset.sum_nonneg
    intro Y _
    split_ifs <;> positivity
  have hAXA (X : E →ₗ[F2] F) : AX X ≤ A := by
    apply Finset.sum_le_sum
    intro Y _
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hmass : (∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) ≤ 2*A := by
    calc
      _ = ∑ Y, a Y^2 * (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
          ((2:ℝ)⁻¹)^(4*d*rank X)) := by
        simp only [AX, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Y _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X _
        split_ifs <;> ring
      _ ≤ ∑ Y, a Y^2*2 := by
        apply Finset.sum_le_sum
        intro Y _
        by_cases hy : rank Y ≤ d
        · exact mul_le_mul_of_nonneg_left (predecessor_weight_sum Y d hy) (sq_nonneg _)
        · have hz := hdegree Y (Nat.lt_of_not_ge hy)
          rw [hz]
          simp
      _ = 2*A := by rw [← Finset.sum_mul]; dsimp [A]; ring
  have hE (X : E →ₗ[F2] F) : 0 ≤ energy a X := by
    unfold energy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoarse (X : E →ₗ[F2] F) : energy a X ≤ (2:ℝ)^(2*d*rank X)*AX X := by
    let : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := compressedFintype X
    have h10 := DerivativeEnergy.coefficient_energy X a d hdegree
    have he : 2*rank X*(d-rank X) ≤ 2*d*rank X := by
      calc
        _ ≤ 2*rank X*d := Nat.mul_le_mul_left _ (Nat.sub_le d (rank X))
        _ = _ := by ring
    have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
    have hp : (2:ℝ)^(2*rank X*(d-rank X)) ≤ (2:ℝ)^(2*d*rank X) := by exact_mod_cast hn
    exact h10.trans (mul_le_mul_of_nonneg_right hp (hAX X))
  have hfour (X : E →ₗ[F2] F) : (energy a X)^2 ≤ (2:ℝ)^(4*d*rank X)*(A*AX X) := by
    have hs : (energy a X)^2 ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 :=
      (sq_le_sq₀ (hE X) (mul_nonneg (by positivity) (hAX X))).mpr (hcoarse X)
    have ha : (AX X)^2 ≤ A*AX X := by
      have hh := mul_le_mul_of_nonneg_right (hAXA X) (hAX X)
      simpa [pow_two] using hh
    calc
      _ ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 := hs
      _ = ((2:ℝ)^(2*d*rank X))^2*(AX X)^2 := by rw [mul_pow]
      _ ≤ ((2:ℝ)^(2*d*rank X))^2*(A*AX X) :=
        mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = _ := by
        rw [← pow_mul]
        congr 2
        ring
  calc
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2)
        ≤ ∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*(A*AX X) := by
      apply Finset.sum_le_sum
      intro X _
      calc
        _ ≤ ((2:ℝ)⁻¹)^(8*d*rank X)*((2:ℝ)^(4*d*rank X)*(A*AX X)) :=
          mul_le_mul_of_nonneg_left (hfour X) (by positivity)
        _ = ((2:ℝ)^(4*d*rank X)*((2:ℝ)⁻¹)^(8*d*rank X))*(A*AX X) := by ring
        _ = _ := by
          have he : 8*d*rank X=4*d*rank X+4*d*rank X := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel_inline_WeightedFourthMoment]
    _ = A*(∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    _ ≤ A*(2*A) := mul_le_mul_of_nonneg_left hmass hA
    _ = 2*A^2 := by ring

end MaxCutGames.Appendix.WeightedFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Derivatives
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

theorem spectralProjector_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) = ∑ Y with P Y, linearCoeff f Y ^ 2 := by
  classical
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_spectralProjector]
  split_ifs <;> simp

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

theorem selector_energy_sum {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) =
      ∑ Y : F →ₗ[F2] E, (selectorMultiplicity P Y : ℝ) * linearCoeff f Y ^ 2 := by
  classical
  simp_rw [spectralProjector_energy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    (∑ i : I, if P i Y then linearCoeff f Y ^ 2 else 0) =
        ∑ i : I with P i Y, linearCoeff f Y ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [selectorMultiplicity]

theorem selector_energy_sum_le {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) (M : ℝ)
    (hcount : ∀ Y : F →ₗ[F2] E, linearCoeff f Y ≠ 0 →
      (selectorMultiplicity P Y : ℝ) ≤ M) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) ≤ M * (𝔼 X, f X ^ 2) := by
  classical
  rw [selector_energy_sum, ← linear_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : linearCoeff f Y = 0
  · simp [hY]
  · exact mul_le_mul_of_nonneg_right (hcount Y hY) (sq_nonneg _)

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

theorem mapDerivative_energy_eq_coefficients (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) =
      ∑ Z : X.ker →ₗ[F2] (E ⧸ X.range),
        (∑ Y : F →ₗ[F2] E, if RankAdditivity.RankBelow X Y ∧
          Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_mapDerivative]

/-- The coefficient-energy definition from the weighted estimate is exactly
the normalized squared norm of the actual map derivative. -/
theorem mapDerivative_energy_eq_weighted_energy (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) = WeightedFourthMoment.energy (linearCoeff f) X := by
  let := WeightedFourthMoment.compressedFintype X
  rw [mapDerivative_energy_eq_coefficients]
  unfold WeightedFourthMoment.energy
  simp only [Restriction.compressFrequency, FullCompression.compression]
  congr 1

/-- The corrected weighted fourth-moment estimate for genuine derivative
norms, with the normalized primal measure and counting frequency measure. -/
theorem weighted_fourth_derivative_energy (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2) ≤ 2 * (𝔼 M, f M ^ 2) ^ 2 := by
  calc
    _ = ∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
        WeightedFourthMoment.energy (linearCoeff f) X ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      rw [mapDerivative_energy_eq_weighted_energy]
    _ ≤ _ := by
      simpa only [linear_parseval] using
        WeightedFourthMoment.weighted_fourth_coefficient_energy (linearCoeff f) d hdegree

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (MaxCutGames.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridMomentSum_le_of_uniform_energy (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (ζ : ℝ)
    (hζ : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      MaxCutGames.Fourier.MatrixRestrictions.order A B ≤ d →
        (𝔼 N, hybridDerivative A B T f N ^ 2) ≤ ζ) :
    hybridMomentSum d f ≤ ζ * hybridSelectorEnergy d f := by
  classical
  unfold hybridMomentSum hybridSelectorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2) ≤
        𝔼 T, ζ * (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) := by
      apply Finset.expect_le_expect
      intro T _
      have hn : 0 ≤ 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2 :=
        Finset.expect_nonneg (fun N _ => sq_nonneg _)
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hζ s.val.1 s.val.2 T s.property) hn
    _ = ζ * (𝔼 T, 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) :=
      (Finset.mul_expect _ _ _).symm
    _ = ζ * (𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2) := by
      rw [hybridDerivative_energy_average]

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
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

open Integration.BinaryLinear

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

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (MaxCutGames.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    MaxCutGames.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F]
  [FiniteDimensional F2 E] in
theorem a5Mask_unique (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (Y : F →ₗ[F2] E) (hY : a5OuterMask X A B Y) :
    ∃! i : A5GeometricIndex X A B, a5Mask X A B i Y := by
  obtain ⟨p, hp, hu⟩ := (a5_unique_selector X Y A B hI hB).mp hY
  rcases hp with ⟨hinner, hdis, hA, hcover, hmeet, hlocal⟩
  let i : A5GeometricIndex X A B := ⟨p, hdis, hA, hcover, hmeet⟩
  refine ⟨i, ⟨hinner, hlocal⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjdis, hjA, hjcover, hjmeet⟩
  exact ⟨hj.1, hjdis, hjA, hjcover, hjmeet, hj.2⟩

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F]
  [FiniteDimensional F2 E] in
theorem a5Mask_implies_outer (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E)
    (hi : a5Mask X A B i Y) : a5OuterMask X A B Y := by
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  exact ⟨rankBelow_of_compressed_rankBelow X Y i.val.1 i.val.2
      hi.1 hdis hcover hi.2,
    reverse_outer_hybrid X Y i.val.1 A B i.val.2
      hi.1 hdis hA hcover hmeet hi.2⟩

omit [Finite E] [Finite F] in
theorem a5_projector_partition (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (a5OuterMask X A B) f =
      ∑ i : A5GeometricIndex X A B, spectralProjector (a5Mask X A B i) f := by
  exact spectralProjector_partition _ _
    (a5Mask_unique X A B hI hB) (a5Mask_implies_outer X A B) f

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

noncomputable section

namespace MaxCutGames.Appendix.RestrictionTransport

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

/-- Exact effective annihilator and target of a nested restriction. -/
theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  constructor
  · rintro ⟨N, rfl⟩
    constructor
    · intro x hx
      change (embed C D N (A.mkQ x) : F) = 0
      have hz : embed C D N (A.mkQ x) = 0 := embed_vanishes C D N hx
      rw [hz]
      rfl
    · rintro y ⟨x, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨embed C D N (A.mkQ x), ?_, rfl⟩
      exact embed_range C D N ⟨A.mkQ x, rfl⟩
  · rintro ⟨hker, hrange⟩
    have hA : A ≤ M.ker := by
      intro x hx
      apply hker
      change A.mkQ x ∈ C
      have hz : A.mkQ x = 0 := by simpa using hx
      rw [hz]
      exact C.zero_mem
    have hB : M.range ≤ B := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hrange hy)
      exact b.property
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr ⟨hA, hB⟩
    have hC : C ≤ N.ker := by
      intro q hq
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      change N (A.mkQ x) = 0
      apply Subtype.ext
      change embed A B N x = 0
      rw [hN]
      exact hker hq
    have hD : N.range ≤ D := by
      rintro b ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      have hm : M x ∈ D.map B.subtype := hrange ⟨x, rfl⟩
      have hco : (N (A.mkQ x) : F) = M x := congrArg (fun L : E →ₗ[F2] F => L x) hN
      rw [← hco] at hm
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hm
      have heq' : b = N (A.mkQ x) := Subtype.ext heq
      exact heq' ▸ hb
    obtain ⟨P, hP⟩ := (exists_embed_iff C D N).mpr ⟨hC, hD⟩
    refine ⟨P, ?_⟩
    change embed A B (embed C D P) = M
    rw [hP, hN]

/-- Nested and effective direct restrictions describe exactly the same perturbations. -/
theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Nested

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

namespace MaxCutGames.Appendix.LinearIdentities

variable {K : Type*} {W : Type*} {V : Type*} [Field K]
  [AddCommGroup W] [AddCommGroup V] [Module K W] [Module K V]

/-- A subspace disjoint from the image has exactly the original kernel as preimage. -/
theorem a5_preimage_eq_ker (X : W →ₗ[K] V) (A₀ : Submodule K V)
    (hd : Disjoint A₀ (LinearMap.range X)) : A₀.comap X = LinearMap.ker X := by
  ext w
  constructor
  · intro hw
    exact Submodule.disjoint_def.mp hd (X w) hw ⟨w, rfl⟩
  · intro hw
    change X w ∈ A₀
    rw [show X w = 0 from hw]
    exact A₀.zero_mem

/-- Restricting to a subspace that covers the domain modulo the kernel preserves the image. -/
theorem a5_range_domRestrict_eq_of_cover (X : W →ₗ[K] V) (B₀ : Submodule K W)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    LinearMap.range (X.domRestrict B₀) = LinearMap.range X := by
  apply le_antisymm (LinearMap.range_domRestrict_le_range X B₀)
  rintro v ⟨w, hw⟩
  have ht : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp ht with ⟨b, hb, k, hk, hbk⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change X b = v
  rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]

/-- The A.5 compressed image pulls back to its exact effective annihilator. -/
theorem a5_effective_annihilator (X : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    (LinearMap.range (compress X A₀ B₀)).comap A₀.mkQ = A := by
  rw [compress, LinearMap.range_comp, a5_range_domRestrict_eq_of_cover X B₀ hc,
    Submodule.comap_map_mkQ, hA]

/-- The A.5 compressed kernel maps to its exact effective codomain. -/
theorem a5_effective_codomain (X : W →ₗ[K] V)
    (A₀ : Submodule K V) (B B₀ : Submodule K W)
    (hd : Disjoint A₀ (LinearMap.range X))
    (hB : B₀ ⊓ LinearMap.ker X = B) :
    (LinearMap.ker (compress X A₀ B₀)).map B₀.subtype = B := by
  rw [compress, LinearMap.ker_comp, Submodule.ker_mkQ]
  change ((A₀.comap X).comap B₀.subtype).map B₀.subtype = B
  rw [a5_preimage_eq_ker X A₀ hd, Submodule.map_comap_subtype, hB]

end MaxCutGames.Appendix.LinearIdentities

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

namespace MaxCutGames.Appendix.HybridComposition

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.LinearIdentities
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
variable [Finite E] [Finite F]

local instance quotientFinite_r856fb4_1 (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
local instance compressedDualFintype_r856fb4_1 (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
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

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite F] in
omit [Finite E] in
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

end MaxCutGames.Appendix.HybridComposition
end

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem DegreeAtMost.mono {d e : ℕ} {f : (E →ₗ[F2] F) → ℝ}
    (hf : DegreeAtMost d f) (hde : d ≤ e) : DegreeAtMost e f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hde hY)

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

end MaxCutGames.Appendix.DegreeZero

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

namespace MaxCutGames.Appendix.A5IndexCount

open MaxCutGames.Integration.BinaryLinear (F2)

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

end MaxCutGames.Appendix.A5IndexCount
end

namespace MaxCutGames.Appendix.Induction

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

theorem antecedent_exponent_budget (d i j k t : Nat)
    (ht : t = i + j + k) (hd : t ≤ d) :
    d * (i + j) + 2 * (d * k) + k * k ≤ 3 * (d * t) := by
  have hk : k ≤ d := by omega
  have hm := Nat.mul_le_mul_right k hk
  have he : d * t = d * (i + j) + d * k := by
    rw [ht, Nat.mul_add]
  omega

/-- For positive k the geometric-series exponent has at least d of slack. -/
theorem positive_rank_geometric_slack (d k : Nat) (hk : 1 ≤ k) :
    31 * (d * (k + 1)) + d ≤ 63 * (d * k) := by
  have hm := Nat.mul_le_mul_left d hk
  have he : d * (k + 1) = d * k + d := by simp [Nat.mul_add]
  omega

end MaxCutGames.Appendix.Induction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OperatorNorm
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

theorem a5_outer_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5OuterMask X A B) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let C := A.map X.range.mkQ
  let D := B.comap X.ker.subtype
  let g := spectralProjector (a5OuterMask X A B) f
  let t := MatrixRestrictions.embed X.range X.ker S
  have hp (N : MatrixRestrictions.Parameter C D) :
      hybridDerivative C D S (mapDerivative X f) N =
        g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) := by
    have hm : (fun Y => RankBelow X Y ∧ Hybrid (compress Y X.range X.ker) C D) =
        a5OuterMask X A B := rfl
    have hh := nested_projector_restriction_apply X.range X.ker C D
      (fun Y => RankBelow X Y) (fun Y => Hybrid Y C D) f 0 S N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [hybridDerivative, hybridProjector, mapDerivative, rankProjector,
      g, t, zero_add] using hh
  calc
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have ha : C.comap X.range.mkQ = A := by
        dsimp only [C]
        rw [Submodule.comap_map_mkQ, sup_of_le_right hI]
      have hb : D.map X.ker.subtype = B := by
        dsimp only [D]
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hB]
      have range_eq : (RestrictionTransport.nestedEmbedding X.range X.ker C D).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq, ha, hb]
      let equiv := RestrictionTransport.sameRangeEquiv
        (K := F2) (G := E →ₗ[F2] F)
        (P := MatrixRestrictions.Parameter C D) (Q := MatrixRestrictions.Parameter A B)
        (RestrictionTransport.nestedEmbedding X.range X.ker C D)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
        (MatrixRestrictions.embed_injective A B) range_eq
      apply Fintype.expect_equiv equiv.toEquiv
      intro parameter
      exact congrArg (fun value => g (t + value) ^ 2)
        (RestrictionTransport.sameRangeEquiv_commutes
          (K := F2) (G := E →ₗ[F2] F)
          (P := MatrixRestrictions.Parameter C D) (Q := MatrixRestrictions.Parameter A B)
          (RestrictionTransport.nestedEmbedding X.range X.ker C D)
          (MatrixRestrictions.embedding A B)
          (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
          (MatrixRestrictions.embed_injective A B) range_eq parameter).symm

theorem a5_summand_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
      (hybridDerivative i.val.1 i.val.2
        (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5Mask X A B i) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let A0 := i.val.1
  let B0 := i.val.2
  let Z := compress X A0 B0
  let g := spectralProjector (a5Mask X A B i) f
  let t := MatrixRestrictions.embed X.range X.ker S
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  have hz : MatrixRestrictions.embed A0 B0
      (0 : MatrixRestrictions.Parameter A0 B0) = 0 :=
    (MatrixRestrictions.embedding A0 B0).map_zero
  have hp (N : MatrixRestrictions.Parameter Z.range Z.ker) :
      mapDerivative Z (hybridDerivative A0 B0 t f) N =
        g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) := by
    have hm : (fun Y => Hybrid Y A0 B0 ∧ RankBelow Z (compress Y A0 B0)) =
        a5Mask X A B i := rfl
    have hh := nested_projector_restriction_apply A0 B0 Z.range Z.ker
      (fun Y => Hybrid Y A0 B0) (fun Y => RankBelow Z Y) f t 0 N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [mapDerivative, rankProjector, hybridDerivative, hybridProjector,
      g, hz, add_zero] using hh
  calc
    (𝔼 N, mapDerivative Z (hybridDerivative A0 B0 t f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have range_eq : (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq,
          a5_effective_annihilator X A0 A B0 hA hcover,
          a5_effective_codomain X A0 B B0 hdis hmeet]
      let equiv := RestrictionTransport.sameRangeEquiv
        (K := F2) (G := E →ₗ[F2] F)
        (P := MatrixRestrictions.Parameter Z.range Z.ker) (Q := MatrixRestrictions.Parameter A B)
        (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embed_injective A B) range_eq
      apply Fintype.expect_equiv equiv.toEquiv
      intro parameter
      exact congrArg (fun value => g (t + value) ^ 2)
        (RestrictionTransport.sameRangeEquiv_commutes
          (K := F2) (G := E →ₗ[F2] F)
          (P := MatrixRestrictions.Parameter Z.range Z.ker) (Q := MatrixRestrictions.Parameter A B)
          (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
          (MatrixRestrictions.embedding A B)
          (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
          (MatrixRestrictions.embed_injective A B) range_eq parameter).symm

theorem a5_energySquare_le (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)]
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) ^ 2 ≤
    (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
      ∑ i : A5GeometricIndex X A B,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2
            (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2 := by
  classical
  let J := A5GeometricIndex X A B
  let t := MatrixRestrictions.embed X.range X.ker S
  let g : J → MatrixRestrictions.Parameter A B → ℝ := fun i M =>
    spectralProjector (a5Mask X A B i) f (t + MatrixRestrictions.embed A B M)
  have hp (M : MatrixRestrictions.Parameter A B) :
      spectralProjector (a5OuterMask X A B) f
        (t + MatrixRestrictions.embed A B M) = ∑ i : J, g i M := by
    have h := congrFun (a5_projector_partition X A B hI hB f)
      (t + MatrixRestrictions.embed A B M)
    simpa only [Finset.sum_apply, g] using h
  have ho :
      (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
        S (mapDerivative X f) N ^ 2) = 𝔼 M, (∑ i : J, g i M) ^ 2 := by
    rw [a5_outer_energy X A B hI hB f S]
    exact Finset.expect_congr rfl fun M _ => congrArg (fun r : ℝ => r ^ 2) (hp M)
  have hi (i : J) :
      (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
        (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) = 𝔼 M, g i M ^ 2 :=
    a5_summand_energy X A B i f S
  rw [ho]
  calc
    (𝔼 M, (∑ i : J, g i M) ^ 2) ^ 2 ≤
        (Fintype.card J : ℝ) ^ 3 * ∑ i : J, (𝔼 M, g i M ^ 2) ^ 2 :=
      energy_sum_sq_le_card_cube g
    _ = (Fintype.card J : ℝ) ^ 3 * ∑ i : J,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) ^ 2 := by
      apply congrArg (fun r : ℝ => (Fintype.card J : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => r ^ 2) (hi i).symm

end MaxCutGames.Appendix.OperatorNorm
end

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
theorem rankBelow_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (X Y : F →ₗ[F2] E) :
    RankBelow (LinearEquiv.arrowCongr b a X) (LinearEquiv.arrowCongr b a Y) ↔
      RankBelow X Y := by
  unfold RankBelow
  rw [← map_sub, rank_arrowCongr, rank_arrowCongr, rank_arrowCongr]

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem admissible_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) (M : E →ₗ[F2] F) :
    ((LinearEquiv.arrowCongr b a Z).range ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ (LinearEquiv.arrowCongr b a Z).ker) ↔
    (Z.range ≤ M.ker ∧ M.range ≤ Z.ker) := by
  simp [LinearMap.range_le_ker_iff, ← LinearEquiv.arrowCongr_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
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
  simp only [mapDerivative, restrict, MaxCutGames.Fourier.MatrixRestrictions.translate, zero_add]
  rw [rankProjector_pullback]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker))
    (embedding (LinearEquiv.arrowCongr b a Z).range (LinearEquiv.arrowCongr b a Z).ker)
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective Z.range Z.ker))
    (embed_injective _ _) (derivative_embedding_range a b Z)
    (fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f M ^ 2)

end General

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

attribute [local instance] OAI.MaxCutGames.Appendix.NaturalTransport.instFiniteQuotientSubmoduleF2
attribute [local instance] OAI.MaxCutGames.Appendix.NaturalTransport.instFintypeLinearMapF2IdSubtypeMemSubmoduleQuotientOfFinite
omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem dualFactor_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    Module.finrank F2 (dualFactor A B C D Z).range = Module.finrank F2 Z.range :=
  rank_arrowCongr (outputFactor B D) (quotientFactor A C).symm Z

omit [FiniteDimensional F2 F] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] [Finite E] in
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

end MaxCutGames.Appendix.NaturalTransport

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine MaxCutGames.Fourier.MatrixRestrictions.translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5Scalar
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
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

noncomputable section
open scoped BigOperators

namespace MaxCutGames.Appendix.A5Scalar

theorem absorption {d : ℕ} (hd : 1 ≤ d) :
    (162 : ℝ) * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
      ((2 : ℝ) ^ (31 * d - 1))⁻¹) ≤ 1 := by
  have hdd : 1 ≤ d * d := hd.trans (Nat.le_mul_self d)
  have he₁ : 9 ≤ 94 * d * d := by nlinarith
  have he₂ : 9 ≤ 31 * d - 1 := by omega
  have hp₁ : (512 : ℝ) ≤ (2 : ℝ) ^ (94 * d * d) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₁
  have hp₂ : (512 : ℝ) ≤ (2 : ℝ) ^ (31 * d - 1) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₂
  have hb₁ : (512 : ℝ) * ((2 : ℝ) ^ (94 * d * d))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₁
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (94 * d * d)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (94 * d * d) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  have hb₂ : (512 : ℝ) * ((2 : ℝ) ^ (31 * d - 1))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₂
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (31 * d - 1)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (31 * d - 1) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  linarith

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
        norm_num [pow_add] ; ring
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
        norm_num [pow_add] ; ring

theorem a16_original_range (d k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) :=
  a16_finite_geometric d d d k hd

end MaxCutGames.Appendix.A5Scalar
end

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

noncomputable section

namespace MaxCutGames.Appendix.A5Passage

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem comap_mkQ_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 (E ⧸ P) => A.comap P.mkQ) := by
  intro A B h
  change A.comap P.mkQ = B.comap P.mkQ at h
  ext z
  obtain ⟨v, rfl⟩ := P.mkQ_surjective z
  change v ∈ A.comap P.mkQ ↔ v ∈ B.comap P.mkQ
  rw [h]

theorem map_subtype_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 P => A.map P.subtype) := by
  intro A B h
  change A.map P.subtype = B.map P.subtype at h
  ext z
  constructor
  · intro hz
    have hm : (z : E) ∈ A.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv
  · intro hz
    have hm : (z : E) ∈ B.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv

theorem outer_eq_of_lifted (X : F →ₗ[F2] E) {e : Nat} (s t : OuterIndex X e)
    (hA : LiftedA X s = LiftedA X t) (hB : LiftedB X s = LiftedB X t) : s = t := by
  apply Subtype.ext
  exact Prod.ext (comap_mkQ_injective X.range hA) (map_subtype_injective X.ker hB)

theorem forget_injective (X : F →ₗ[F2] E) (e : Nat) :
    Function.Injective (forget X e) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  change p.val = q.val at h
  have hA : LiftedA X s = LiftedA X t := by
    calc
      LiftedA X s = p.val.1 ⊔ X.range := p.property.2.1.symm
      _ = q.val.1 ⊔ X.range := congrArg (fun A => A ⊔ X.range) (congrArg Prod.fst h)
      _ = LiftedA X t := q.property.2.1
  have hB : LiftedB X s = LiftedB X t := by
    calc
      LiftedB X s = p.val.2 ⊓ X.ker := p.property.2.2.2.symm
      _ = q.val.2 ⊓ X.ker := congrArg (fun B => B ⊓ X.ker) (congrArg Prod.snd h)
      _ = LiftedB X t := q.property.2.2.2
  have hst := outer_eq_of_lifted X s t hA hB
  cases hst
  have hpq : p = q := Subtype.ext h
  cases hpq
  rfl

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

omit [Finite E] [Finite F] [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
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
    MaxCutGames.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 =
      MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 := by
  unfold MaxCutGames.Fourier.MatrixRestrictions.order
  rw [dim_pairA X q, codim_pairB X q]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] in
theorem pair_rank (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (LinearIdentities.compress X q.2.val.1 q.2.val.2).range =
      Module.finrank F2 X.range :=
  LinearIdentities.compress_rank_preserved X q.2.val.1 q.2.val.2
    q.2.property.1 q.2.property.2.2.1

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] in
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
    MaxCutGames.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      MaxCutGames.Fourier.MatrixRestrictions.order A B +
        MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 +
        Module.finrank F2 X.range := by
  rw [HybridComposition.order_effective, NaturalTransport.dualFactor_rank,
    pair_order, pair_rank]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_le (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (d : Nat)
    (h : MaxCutGames.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range ≤ d)
    (q : Passage X (d - (MaxCutGames.Fourier.MatrixRestrictions.order A B +
      Module.finrank F2 X.range))) :
    MaxCutGames.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range ≤ d := by
  rw [effective_order_rank]
  have hq := q.1.property
  change MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 ≤
    d - (MaxCutGames.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range) at hq
  omega

end MaxCutGames.Appendix.A5Passage
end

/-! Finite Gram-energy estimates used in Lemma A.1. The witness relation and
frequency-count instantiations are separate obligations. -/

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SubmoduleInterval
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
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

end MaxCutGames.Appendix.SubmoduleInterval

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

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

end MaxCutGames.Appendix.UpperMobius

open scoped BigOperators

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

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

variable [Fintype (W →ₗ[F2] V)]

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

end MaxCutGames.Appendix.BadConvolution
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A1Reduction
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.DerivativeInduction

open MaxCutGames.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Exact antecedent cardinality in arbitrary complementary subspaces. -/
theorem card_subspaceAntecedent (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) [Module.Finite F2 W] [Module.Finite F2 V] :
    Nat.card (SubspaceAntecedent P Q D hQ Z) =
      2 ^ (Module.finrank F2 Z.range *
        (Module.finrank F2 Q + Module.finrank F2 E)) := by
  rw [Nat.card_congr (subspaceAntecedentEquiv P E Q D hP hQ Z), Nat.card_prod,
    CompressionCount.natCard_linearMap, CompressionCount.natCard_linearMap, ← pow_add]
  congr 1
  ring

end MaxCutGames.Appendix.DerivativeInduction

/-!
# Exact antecedents of quotient compression

This is the reverse-map count used in Proposition A.5. The compressed map is
fixed, together with the two removed subspaces; neither a prescribed rank nor
an assumed cardinality is part of the antecedent predicate.
-/

namespace MaxCutGames.Appendix.AntecedentCount

open MaxCutGames.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

variable [FiniteDimensional F2 W] [FiniteDimensional F2 V]

/-- Exact number of antecedents of a fixed quotient compression. The graph
and omitted-domain parameters have `rank Y * (dim Q + codim P)` bits. -/
theorem card_antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :
    Nat.card (Antecedent P Q Y) =
      2 ^ (Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P))) := by
  obtain ⟨E, hP⟩ := P.exists_isCompl
  obtain ⟨D, hQ⟩ := Q.exists_isCompl
  rw [Nat.card_congr (subspaceEquiv P Q D hQ Y),
    DerivativeInduction.card_subspaceAntecedent P E Q D hP hQ]
  rw [CoordinateTransport.finrank_comp_equiv]
  rw [← (P.quotientEquivOfIsCompl E hP).finrank_eq]

/-- The actual reverse-map multiplicity fits the two graph-parameter budgets
used in (A.16). No additional isomorphism factor is needed. -/
theorem card_antecedent_le (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hQ : Module.finrank F2 Q ≤ d)
    (hP : Module.finrank F2 (W ⧸ P) ≤ d) :
    Nat.card (Antecedent P Q Y) ≤ 2 ^ (2 * d * k) := by
  rw [card_antecedent]
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  calc
    Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P)) ≤ k * (d + d) :=
      Nat.mul_le_mul hY (Nat.add_le_add hQ hP)
    _ = 2 * d * k := by ring

end

end MaxCutGames.Appendix.AntecedentCount

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5ReverseIndex
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.A5ReverseIndex

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem relativeFrequency_rank (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) :
    Module.finrank F2 (relativeFrequency A A' B' B hA hB Y).range =
      Module.finrank F2 Y.range :=
  CoordinateTransport.finrank_range_transport
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm Y

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem relative_codomain_dimension (A A' : Submodule F2 V) (hA : A ≤ A') :
    Module.finrank F2 (A'.map A.mkQ) + Module.finrank F2 A =
      Module.finrank F2 A' := by
  have h₁ := (A'.map A.mkQ).finrank_quotient_add_finrank
  have h₂ := A.finrank_quotient_add_finrank
  have h₃ := A'.finrank_quotient_add_finrank
  have h₄ := (Submodule.quotientQuotientEquivQuotient A A' hA).finrank_eq
  omega

theorem relative_domain_codimension_le (B' B : Submodule F2 W) (hB : B' ≤ B) :
    Module.finrank F2 (B ⧸ B'.comap B.subtype) ≤
      Module.finrank F2 (W ⧸ B') := by
  have h₁ := (B'.comap B.subtype).finrank_quotient_add_finrank
  have h₂ := B'.finrank_quotient_add_finrank
  have h₃ := B.finrank_le
  have h₄ := (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).finrank_eq
  change Module.finrank F2 B' = Module.finrank F2 (B'.comap B.subtype) at h₄
  omega

/-- Each fixed earlier pair contributes at most two graph-parameter budgets. -/
theorem card_local_antecedent_le (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hAd : Module.finrank F2 A' ≤ d)
    (hBd : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (AntecedentCount.Antecedent
      (B'.comap B.subtype) (A'.map A.mkQ)
      (relativeFrequency A A' B' B hA hB Y)) ≤ 2 ^ (2 * d * k) := by
  apply AntecedentCount.card_antecedent_le
  · simpa only [relativeFrequency_rank] using hY
  · have h := relative_codomain_dimension A A' hA
    omega
  · exact (relative_domain_codimension_le B' B hB).trans hBd

local instance quotientFinite {U : Type*} [AddCommGroup U] [Module F2 U]
    [Finite U] (P : Submodule F2 U) : Finite (U ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance linearMapFinite {U Z : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup Z] [Module F2 Z] [Finite U] [Finite Z] :
    Finite (U →ₗ[F2] Z) :=
  Finite.of_injective (fun f : U →ₗ[F2] Z => (f : U → Z)) DFunLike.coe_injective

private theorem card_sigma_le_inline_A5ReverseIndex {I : Type*} [Fintype I]
    (fiber : I → Type*) [∀ i, Finite (fiber i)] (N : ℕ)
    (h : ∀ i, Nat.card (fiber i) ≤ N) :
    Nat.card (Σ i, fiber i) ≤ Nat.card I * N := by
  rw [Nat.card_sigma]
  calc
    (∑ i, Nat.card (fiber i)) ≤ ∑ _i : I, N := Finset.sum_le_sum (fun i _ => h i)
    _ = Nat.card I * N := by simp [Nat.card_eq_fintype_card]

variable [Finite V] [Finite W]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

/-- Sharp graph-based upper bound for the entire actual reverse fiber. -/
theorem card_ancestor_le (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (d * (i + j) + 2 * d * k) := by
  have hlocal (A : EarlierA A' i) (B : EarlierB B' j) :=
    card_local_antecedent_le A.val A' B' B.val A.property.1 B.property.1
      Y d k hY hA hB
  have hinner (A : EarlierA A' i) :
      Nat.card (Σ B : EarlierB B' j,
        AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
          (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)) ≤
        Nat.card (EarlierB B' j) * 2 ^ (2 * d * k) :=
    card_sigma_le_inline_A5ReverseIndex _ _ (hlocal A)
  have htotal : Nat.card (Ancestor A' B' Y i j) ≤
      Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) :=
    card_sigma_le_inline_A5ReverseIndex _ _ hinner
  calc
    Nat.card (Ancestor A' B' Y i j) ≤
        Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) := htotal
    _ ≤ 2 ^ (d * i) * (2 ^ (d * j) * 2 ^ (2 * d * k)) :=
      Nat.mul_le_mul (BadConvolution.card_lower_rank_le A' d i hA)
        (Nat.mul_le_mul_right _ (BadConvolution.card_upper_codim_le B' d j hB))
    _ = 2 ^ (d * (i + j) + 2 * d * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem card_ancestor_le_source (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) (ht : i + j + k ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (3 * (d * (i + j + k))) := by
  apply (card_ancestor_le A' B' Y d i j k hY hA hB).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Induction.antecedent_exponent_budget d i j k (i + j + k) rfl ht
  calc
    d * (i + j) + 2 * d * k ≤ d * (i + j) + 2 * d * k + k * k :=
      Nat.le_add_right _ _
    _ ≤ 3 * (d * (i + j + k)) := by simpa only [Nat.mul_assoc] using h

end

end MaxCutGames.Appendix.A5ReverseIndex

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

noncomputable section

namespace MaxCutGames.Appendix.A5ForwardIndex

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank {d : ℕ} (a : Index (E := E) (F := F) d) :
    targetRank (descendant a) = Module.finrank F2 a.1.val.2.2.range :=
  A5Passage.descendant_rank a.1.val.1 a.1.val.2.1 a.1.val.2.2 a.2

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_size {d : ℕ} (a : Index (E := E) (F := F) d) :
    sourceI a + sourceJ a + targetRank (descendant a) = A13Index.size a.1.val := by
  rw [descendant_rank]
  rfl

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierTriple_encode (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) (a : Fiber d r i j) :
    earlierTriple (encode d r i j a) = a.val.1.val := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Fixing the result and retained earlier data fixes both the complementary
pair and its outer hybrid index. No additional outer-index factor occurs. -/
theorem encode_injective (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Function.Injective (encode d r i j) := by
  intro a b hab
  have hraw : a.val.1.val = b.val.1.val := by
    simpa only [earlierTriple_encode] using congrArg earlierTriple hab
  have hbase : a.val.1 = b.val.1 := Subtype.ext hraw
  have hresult : descendant a.val = descendant b.val := a.property.1.trans b.property.1.symm
  rcases a with ⟨⟨r₁, p⟩, ha⟩
  rcases b with ⟨⟨r₂, q⟩, hb⟩
  change r₁ = r₂ at hbase
  cases hbase
  have hA := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.1) hresult
  have hB := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.2.1) hresult
  change p.2.val.1.comap r₁.val.1.mkQ = q.2.val.1.comap r₁.val.1.mkQ at hA
  change p.2.val.2.map r₁.val.2.1.subtype = q.2.val.2.map r₁.val.2.1.subtype at hB
  have hpq : p = q := A5Passage.forget_injective r₁.val.2.2 _
    (Prod.ext (A5Passage.comap_mkQ_injective r₁.val.1 hA)
      (A5Passage.map_subtype_injective r₁.val.2.1 hB))
  cases hpq
  rfl

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

attribute [local instance] OAI.MaxCutGames.Appendix.A5ForwardIndex.indexFintype
omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Actual cardinality bound for every fiber used by the weighted reversal. -/
theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r))) := by
  by_cases hn : Nonempty (Fiber d r i j)
  · obtain ⟨a⟩ := hn
    have hsize : A13Index.size r ≤ d := by
      rw [← a.property.1]
      exact descendant_size_le a.val
    have hA : Module.finrank F2 r.1 ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have hB : Module.finrank F2 (F ⧸ r.2.1) ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have ht : i + j + targetRank r ≤ d := by
      have h := (original_order_bounds a.val).2
      rwa [a.property.1, a.property.2.1, a.property.2.2] at h
    have hcount := A5ReverseIndex.card_ancestor_le_source r.1 r.2.1 r.2.2
      d i j (targetRank r) (le_refl _) hA hB ht
    exact (Nat.card_le_card_of_injective (encode d r i j)
      (encode_injective d r i j)).trans hcount
  · have : IsEmpty (Fiber d r i j) := ⟨fun a => hn ⟨a⟩⟩
    simp

end MaxCutGames.Appendix.A5ForwardIndex

open scoped BigOperators

namespace MaxCutGames.Appendix.A5WeightedReindex

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

end MaxCutGames.Appendix.A5WeightedReindex
end

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

noncomputable section
namespace MaxCutGames.Appendix.A5ReverseSum

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
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
  · simp only [h, ite_false, Finset.sum_const_zero]

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

end MaxCutGames.Appendix.A5ReverseSum
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5Induction
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

noncomputable section
namespace MaxCutGames.Appendix.A5Induction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.DerivativeDegree
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

theorem damping_le (d k : ℕ) :
    (1 / 2 : ℝ) ^ (31 * d * (k + 1) + 4 * d * k) ≤
      (1 / 2 : ℝ) ^ (31 * d) * (1 / 2 : ℝ) ^ (8 * d * k) := by
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
      nlinarith
  have he : 31 * d * (k + 1) + 4 * d * k =
      (31 * d + 8 * d * k) + 27 * d * k := by ring
  rw [he, pow_add, pow_add]
  have hh := mul_le_mul_of_nonneg_left (hpow (27 * d * k))
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (31 * d))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (8 * d * k)))
  simpa only [mul_one] using hh

theorem coefficient_absorption (d : ℕ) (hd : 1 ≤ d) :
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
      (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) ≤
      (2 : ℝ) ^ (100 * d * d) := by
  have hfirst : (2 : ℝ) ^ (100 * d * d) *
      ((2 : ℝ) ^ (94 * d * d))⁻¹ = (2 : ℝ) ^ (6 * d * d) := by
    have he : 100 * d * d = 6 * d * d + 94 * d * d := by ring
    rw [he, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      mul_one]
  have he : 31 * d = (31 * d - 1) + 1 := by omega
  have hsecond : ((2 : ℝ) ^ (31 * d - 1))⁻¹ =
      2 * (1 / 2 : ℝ) ^ (31 * d) := by
    calc
      ((2 : ℝ) ^ (31 * d - 1))⁻¹ = (1 / 2 : ℝ) ^ (31 * d - 1) := by
        rw [one_div, inv_pow]
      _ = 2 * ((1 / 2 : ℝ) ^ (31 * d - 1) * (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← pow_succ, ← he]
  have hscaled := mul_le_mul_of_nonneg_right (A5Scalar.absorption hd)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  calc
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) =
        162 * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
          ((2 : ℝ) ^ (31 * d - 1))⁻¹) * (2 : ℝ) ^ (100 * d * d) := by
      symm
      calc
        _ = 162 * ((2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (94 * d * d))⁻¹ +
            (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (31 * d - 1))⁻¹) := by ring
        _ = _ := by rw [hfirst, hsecond]
    _ ≤ _ := by simpa only [one_mul] using hscaled

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem dampedMapMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedMapMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * (𝔼 M, f M ^ 2) ^ 2 := by
  have hterms : dampedMapMoment d f ≤ (1 / 2 : ℝ) ^ (31 * d) *
      ∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2) ^ 2 := by
    unfold dampedMapMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro X _
    have hh := mul_le_mul_of_nonneg_right (damping_le d (frequencyRank X))
      (sq_nonneg (𝔼 N, mapDerivative X f N ^ 2))
    simpa only [mul_assoc] using hh
  have hbase := weighted_fourth_derivative_energy f d (fun Y hY => hf Y hY)
  have hbase' :
      (∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2)^2) ≤ 2 * (𝔼 M, f M ^ 2)^2 := by
    simpa only [one_div, frequencyRank] using hbase
  calc
    dampedMapMoment d f ≤ _ := hterms
    _ ≤ (1 / 2 : ℝ) ^ (31 * d) * (2 * (𝔼 M, f M ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase'
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    _ = _ := by ring

theorem dampedHybridMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedHybridMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f := by
  unfold dampedHybridMoment hybridMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)) ≤
        𝔼 T, (2 * (1 / 2 : ℝ) ^ (31 * d)) *
          (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2 := by
      apply Finset.expect_le_expect
      intro T _
      exact dampedMapMoment_le d _
        ((degree_hybridDerivative s.val.1 s.val.2 T f hf).mono (Nat.sub_le _ _))
    _ = _ := by rw [← Finset.mul_expect]

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

/-- Close the actual recurrence once its finite index expansion is supplied.
This lemma states that recurrence explicitly; it is not the public A.5 theorem. -/
theorem recurrence_closure (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (hrec : (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d * d) * (𝔼 M, f M ^ 2)^2 +
        (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f := by
  have hS : 0 ≤ hybridMomentSum d f :=
    Finset.sum_nonneg (fun s _ => Finset.expect_nonneg (fun T _ => sq_nonneg _))
  have herror := mul_le_mul_of_nonneg_left (energy_sq_le_hybridMomentSum d f)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d * d))
  have hdamp := mul_le_mul_of_nonneg_left (dampedHybridMoment_le d f hf)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  have hrec' : (𝔼 M, f M ^ 4) / 162 ≤
      ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f := by
    calc
      _ ≤ _ := hrec
      _ ≤ (2 : ℝ) ^ (6 * d * d) * hybridMomentSum d f +
          (2 : ℝ) ^ (100 * d * d) *
            ((2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f) :=
        add_le_add herror hdamp
      _ = _ := by ring
  calc
    (𝔼 M, f M ^ 4) = 162 * ((𝔼 M, f M ^ 4) / 162) := by ring
    _ ≤ 162 * (((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f) := mul_le_mul_of_nonneg_left hrec' (by norm_num)
    _ = (162 * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d)))) *
          hybridMomentSum d f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_absorption d hd) hS

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

/-- Recombination uses the natural domain and codomain isomorphisms. The
intermediate shifts need only be the actual embedded derivative parameters. -/
theorem postA5Sum_hybrid_average (A : Submodule F2 E) (B : Submodule F2 F)
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
theorem boundedTripleSum_le_descendants (d : ℕ)
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

theorem derivative_inequality (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d f := by
  simpa only [pow_two, Nat.mul_assoc] using boundAtDegree.{u, v} d f hf

end MaxCutGames.Appendix.A5Induction
end

/-! Frequency-conditioned counts of actual Hybrid pairs and derivative indices. -/
namespace MaxCutGames.Appendix.HybridCounting

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

private theorem comap_subtype_injective_inline_HybridCounting {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (I A B : Submodule K V) (hA : A ≤ I) (hB : B ≤ I)
    (h : A.comap I.subtype = B.comap I.subtype) : A = B := by
  apply le_antisymm
  · intro x hx
    have hv : (⟨x, hA hx⟩ : I) ∈ A.comap I.subtype := hx
    rw [h] at hv
    exact hv
  · intro x hx
    have hv : (⟨x, hB hx⟩ : I) ∈ B.comap I.subtype := hx
    rw [← h] at hv
    exact hv

private theorem map_quotient_injective_inline_HybridCounting {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (N A B : Submodule K V) (hA : N ≤ A) (hB : N ≤ B)
    (h : A.map N.mkQ = B.map N.mkQ) : A = B := by
  have aux (P Q : Submodule K V) (hQ : N ≤ Q)
      (he : P.map N.mkQ = Q.map N.mkQ) : P ≤ Q := by
    intro x hx
    have hm : N.mkQ x ∈ P.map N.mkQ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [he] at hm
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hm
    have hk : x - y ∈ N := by
      have hzero : x - y ∈ LinearMap.ker N.mkQ := by
        change N.mkQ (x - y) = 0
        rw [map_sub, heq, sub_self]
      simpa only [Submodule.ker_mkQ] using hzero
    have hz := Q.add_mem (hQ hk) hy
    simpa only [sub_add_cancel] using hz
  exact le_antisymm (aux A B hB h) (aux B A hA h.symm)

private theorem finite_submodules_inline_HybridCounting (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Finite (Submodule F2 V) := by
  let : Finite V := Finite.of_injective (Module.finBasis F2 V).equivFun
    (Module.finBasis F2 V).equivFun.injective
  exact Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]
  [Module F2 E] [Module F2 F] [FiniteDimensional F2 F]

/-- All actual Hybrid pairs for this frequency, with no ambient-dimension factor. -/
theorem card_hybrid_pairs_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {p : Submodule F2 E × Submodule F2 F //
      LinearIdentities.Hybrid Y p.1 p.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let P := {p : Submodule F2 E × Submodule F2 F //
    LinearIdentities.Hybrid Y p.1 p.2}
  let : Finite (Submodule F2 Y.range) := finite_submodules_inline_HybridCounting _
  let : Finite (Submodule F2 (F ⧸ Y.ker)) := finite_submodules_inline_HybridCounting _
  have hk (p : P) : Y.ker ≤ p.1.2 := by
    intro x hx
    apply p.2.2
    change Y x ∈ p.1.1
    rw [show Y x = 0 from hx]
    exact Submodule.zero_mem _
  let code (p : P) : Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker) :=
    ((p.1.1).comap Y.range.subtype, (p.1.2).map Y.ker.mkQ)
  have hi : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact comap_subtype_injective_inline_HybridCounting Y.range p.1.1 q.1.1 p.2.1 q.2.1
        (congrArg Prod.fst h)
    · exact map_quotient_injective_inline_HybridCounting Y.ker p.1.2 q.1.2 (hk p) (hk q)
        (congrArg Prod.snd h)
  have hq : finrank F2 (F ⧸ Y.ker) = finrank F2 Y.range := by
    have hquot := Y.ker.finrank_quotient_add_finrank
    have hrank := Y.finrank_range_add_finrank_ker
    omega
  have hleft := MaxCutGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := Y.range) d hY
  have hright := MaxCutGames.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := F ⧸ Y.ker) d (hq.trans_le hY)
  calc
    _ ≤ Nat.card (Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_le_card_of_injective code hi
    _ = Nat.card (Submodule F2 Y.range) * Nat.card (Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_prod _ _
    _ ≤ 2 ^ (d * d) * 2 ^ (d * d) := Nat.mul_le_mul hleft hright
    _ = _ := by rw [← pow_add]; congr 1; ring

variable [FiniteDimensional F2 E]

/-- The actual order-bounded index subtype injects into the conditioned pairs. -/
theorem card_hybridIndex_le_two (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let : Finite (Submodule F2 E) := finite_submodules_inline_HybridCounting _
  let : Finite (Submodule F2 F) := finite_submodules_inline_HybridCounting _
  let code (s : {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2}) :
      {p : Submodule F2 E × Submodule F2 F // LinearIdentities.Hybrid Y p.1 p.2} :=
    ⟨s.1.1, s.2⟩
  have hi : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    change (code s).1 = (code t).1
    exact congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective code hi).trans (card_hybrid_pairs_le Y d hY)

theorem card_hybridIndex_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (3 * d * d) := by
  apply (card_hybridIndex_le_two Y d hY).trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (d * d) (by decide : 2 ≤ 3)

end MaxCutGames.Appendix.HybridCounting

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.DerivativeDegree

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual selector multiplicity on frequencies of rank at most `d`.
This uses only the proved finite subspace count and Parseval. -/
theorem selector_energy_le (d : ℕ) (g : (E →ₗ[F2] F) → ℝ)
    (hg : DegreeAtMost d g) :
    hybridSelectorEnergy d g ≤ (2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2) := by
  unfold hybridSelectorEnergy hybridProjector
  apply selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hg Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : selectorMultiplicity
      (fun s : HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [selectorMultiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

/-- Generic closure of the fourth-moment estimate from a uniform bound on
the actual hybrid derivatives. Its eventual KMS application must prove `hH`
from the basis-invariant function and its local densities. -/
theorem fourth_moment_le_of_uniform_hybrid_energy
    (d : ℕ) (g : (E →ₗ[F2] F) → ℝ) (hg : DegreeAtMost d g)
    (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ d → (𝔼 N, hybridDerivative A B T g N ^ 2) ≤ H) :
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (103 * d * d) * H * (𝔼 X, g X ^ 2) := by
  have hp : (2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (103 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d g :=
      A5Induction.derivative_inequality d g hg
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) * (H * hybridSelectorEnergy d g) :=
      mul_le_mul_of_nonneg_left (hybridMomentSum_le_of_uniform_energy d g H hH)
        (by positivity)
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) *
        (H * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (selector_energy_le d g hg) hH0) (by positivity)
    _ = ((2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d)) *
        H * (𝔼 X, g X ^ 2) := by ring
    _ = _ := by rw [hp]

end
end MaxCutGames.Inverse.KMSFourthMoment

/-! The analytic synthesis and the direct basis-invariant projection are the
same actual function. This identity fixes the interface for both moment and
spectral estimates. -/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Inverse.KMSBasisInvariant

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The degree bound follows from the literal coefficient filter. -/
theorem rankComponent_coeff_eq_zero_of_ne (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E)
    (hS : Module.finrank F2 S.range ≠ i) :
    linearCoeff (rankComponent i f) S = 0 := by
  simp only [rankComponent, coeff_component, ite_eq_right hS]

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
The exact rank component meets the generic derivative inequality's degree
contract by its literal Fourier coefficient filter. This specializes the
checked aggregation to the same actual component used by the KMS spectral
argument; the separate basis-specific proof supplies its hybrid energy.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Appendix
open MaxCutGames.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual finite Fourier support of the component, with no rank-level
inequality invoked. -/
theorem rankComponent_degree (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DerivativeDegree.DegreeAtMost i (rankComponent i f) := by
  intro S hS
  apply rankComponent_coeff_eq_zero_of_ne i f S
  exact ne_of_gt hS

variable [Finite E] [Finite F]

/-- Generic fourth-moment closure for the literal KMS rank component. -/
theorem rankComponent_fourth_moment_le_of_hybrid_oai (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ i →
      (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
    (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2) :=
  fourth_moment_le_of_uniform_hybrid_energy i (rankComponent i f)
    (rankComponent_degree i f) H hH0 hH

end
end MaxCutGames.Inverse.KMSFourthMoment

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid_oai.{u_1, u_2} := @OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid_oai.{u_1, u_2}
