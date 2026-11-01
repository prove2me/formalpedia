-- Prove2me | solution 1 for OAI.KadisonSimilarity.ae_common_fiber_scalar_center
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:50:52.998582+00:00
-- url     : https://prove2.me/submissions/68050065-9342-4e9a-8de4-af1aeb08898c

import Mathlib
import Definitions.Def_OAIQ075A033

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

/-- Compressing an operator supported on the isometric range and extending
it back recovers the original operator. -/
theorem isometricExtension_compression
    (Q : K →L[ℂ] K)
    (hleft : isometricExtension J 1 * Q = Q)
    (hright : Q * isometricExtension J 1 = Q) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap) = Q := by
  have hl (x : K) : J (J.toContinuousLinearMap.adjoint (Q x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hleft
  have hr (x : K) : Q (J (J.toContinuousLinearMap.adjoint x)) = Q x :=
    congrArg (fun L : K →L[ℂ] K => L x) hright
  apply ContinuousLinearMap.ext
  intro x
  change J (J.toContinuousLinearMap.adjoint
    (Q (J (J.toContinuousLinearMap.adjoint x)))) = Q x
  rw [hr, hl]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonSpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The represented abelian commutant embeds isometrically in the actual
commutant of measurable scalar localizations on a single L² space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace A] in
/-- Compression of a scalar-commuting operator lies in the original
represented commutant. -/
theorem commonCompression_commutes_representation
    (Q : CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D)
    (hQ : ∀ a, Q * commonScalarRepresentation π D a =
      commonScalarRepresentation π D a * Q) (a : A) :
    (((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp Q).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap) * π a =
    π a * (((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp Q).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  change (cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
      (Q (cyclicCommonEmbedding π D (π a x))) =
    π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
      (Q (cyclicCommonEmbedding π D x)))
  have hq := congrArg (fun L : CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D =>
    L (cyclicCommonEmbedding π D x)) (hQ a)
  change Q (commonScalarRepresentation π D a (cyclicCommonEmbedding π D x)) =
    commonScalarRepresentation π D a (Q (cyclicCommonEmbedding π D x)) at hq
  rw [commonScalarRepresentation_intertwines, hq,
    ← commonScalarRepresentation_adjoint_intertwines]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_BoundedMeasurableField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable operator fields on L²

Strong measurability of each constant column suffices to apply a field to
an arbitrary L² vector. An almost-everywhere uniform bound then constructs
the actual bounded L² operator, with its pointwise action and localization
commutation proved directly. No norm measurability of the operator field
is required.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem boundedFieldOperator_action
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, boundedFieldOperator μ R hR C hbound f a = R a (f a) :=
  boundedFieldVector_ae μ R hR C hbound f

/-- A measurable field supported on a projection gives a genuinely
left-supported L² operator. -/
theorem boundedFieldOperator_left_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, p a * R a = R a) :
    P * boundedFieldOperator μ R hR C hbound = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP (boundedFieldOperator μ R hR C hbound f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrf ha
  change P (boundedFieldOperator μ R hR C hbound f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

/-- Right support is also recovered from the corresponding pointwise
identity, with no simultaneous null-set assumption. -/
theorem boundedFieldOperator_right_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, R a * p a = R a) :
    boundedFieldOperator μ R hR C hbound * P = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f, boundedFieldOperator_action μ R hR C hbound (P f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrpf hrf ha
  change boundedFieldOperator μ R hR C hbound (P f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hrpf, hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ContinuousFieldCommutation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every bounded measurable operator field commutes with continuous scalar
multiplication, directly from its action on L² sections. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω H : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem boundedFieldOperator_commutes_continuous
    (R : Ω → H →L[ℂ] H)
    (hmeas : ∀ v : H, AEStronglyMeasurable (fun a => R a v) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : C(Ω, ℂ)) :
    boundedFieldOperator μ R hmeas C hbound * VectorL2.continuousL2Mul μ f =
      VectorL2.continuousL2Mul μ f * boundedFieldOperator μ R hmeas C hbound := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [boundedFieldOperator_action μ R hmeas C hbound
      (VectorL2.continuousL2Mul μ f ξ),
    boundedFieldOperator_action μ R hmeas C hbound ξ,
    VectorL2.continuousL2Mul_ae μ f ξ,
    VectorL2.continuousL2Mul_ae μ f (boundedFieldOperator μ R hmeas C hbound ξ)]
    with a hRm hR hm hmr
  change boundedFieldOperator μ R hmeas C hbound (VectorL2.continuousL2Mul μ f ξ) a =
    VectorL2.continuousL2Mul μ f (boundedFieldOperator μ R hmeas C hbound ξ) a
  rw [hRm, hmr, hm, hR, map_smul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RankOneFactorCriterion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rank-one tests for scalarity. A countable dense family suffices, including
on a variable projection range. These are the tests used to prove that the
central-decomposition fibers are factors. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Commuting with all rank-one operators forces an operator to be scalar. -/
theorem scalar_of_commutes_rankOne (T : H →L[ℂ] H)
    (hT : ∀ v w : H, T * InnerProductSpace.rankOne ℂ v w =
      InnerProductSpace.rankOne ℂ v w * T) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · let := hs
    exact ⟨0, Subsingleton.elim _ _⟩
  · let := hn
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have hvv : inner ℂ v v ≠ 0 := (inner_self_ne_zero (𝕜 := ℂ)).2 hv
    have h (x : H) : inner ℂ v v • T x = inner ℂ v (T v) • x := by
      have hx := congrArg (fun S : H →L[ℂ] H => S v) (hT x v)
      simpa only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul] using hx
    refine ⟨(inner ℂ v v)⁻¹ * inner ℂ v (T v), ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    change T x = ((inner ℂ v v)⁻¹ * inner ℂ v (T v)) • x
    calc
      T x = (inner ℂ v v)⁻¹ • (inner ℂ v v • T x) := by
        rw [smul_smul, inv_mul_cancel₀ hvv, one_smul]
      _ = (inner ℂ v v)⁻¹ • (inner ℂ v (T v) • x) := congrArg (fun z : H => (inner ℂ v v)⁻¹ • z) (h x)
      _ = _ := by rw [smul_smul]

/-- It suffices to test rank-one operators on a dense family of vectors. -/
theorem scalar_of_commutes_dense_rankOne {ι : Type*} (d : ι → H)
    (hd : DenseRange d) (T : H →L[ℂ] H)
    (hT : ∀ i j, T * InnerProductSpace.rankOne ℂ (d i) (d j) =
      InnerProductSpace.rankOne ℂ (d i) (d j) * T) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  apply scalar_of_commutes_rankOne T
  have hr : Continuous (fun q : H × H => InnerProductSpace.rankOne ℂ q.1 q.2) := by
    change Continuous (fun q : H × H =>
      (ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ q.2)) q.1)
    exact ((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
      ((innerSL ℂ).continuous.comp continuous_snd)).clm_apply continuous_fst
  have hc : IsClosed {q : H × H |
      T * InnerProductSpace.rankOne ℂ q.1 q.2 =
        InnerProductSpace.rankOne ℂ q.1 q.2 * T} := by
    exact isClosed_eq (continuous_const.mul hr) (hr.mul continuous_const)
  exact hd.induction_on₂ hc hT

/-- Projecting a dense family gives a dense family in the actual range. -/
theorem projectionFiber_denseRange {ι : Type*} (d : ι → H) (hd : DenseRange d)
    (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    DenseRange (fun i => projectionFiberRetraction p hp (d i)) := by
  have hr : Function.Surjective (projectionFiberRetraction p hp) := by
    intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact projectionFiber_fixed p hp x
  exact hr.denseRange.comp hd (projectionFiberRetraction p hp).continuous

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionRankOne
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported rank-one fields supply countably many tests for the full
operator algebra on each projection range. Their bounds and measurability
follow from the projection columns themselves. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A rank-one operator with both vectors in a projection range is supported
on that range on both sides. -/
theorem projection_rankOne_support (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    p * InnerProductSpace.rankOne ℂ (p v) (p w) =
        InnerProductSpace.rankOne ℂ (p v) (p w) ∧
      InnerProductSpace.rankOne ℂ (p v) (p w) * p =
        InnerProductSpace.rankOne ℂ (p v) (p w) := by
  have hpp (x : H) : p (p x) = p x :=
    congrArg (fun L : H →L[ℂ] H => L x) hp.isIdempotentElem.eq
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change p (inner ℂ (p w) x • p v) = inner ℂ (p w) x • p v
    rw [map_smul, hpp]
  · apply ContinuousLinearMap.ext
    intro x
    change inner ℂ (p w) (p x) • p v = inner ℂ (p w) x • p v
    have ha : p.adjoint (p w) = p w := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq, hpp]
    rw [← ContinuousLinearMap.adjoint_inner_left, ha]

/-- Compression gives the ordinary rank-one operator on the range. -/
theorem projectionFiberCompression_rankOne (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    projectionFiberCompression p hp (InnerProductSpace.rankOne ℂ (p v) (p w)) =
      InnerProductSpace.rankOne ℂ (projectionFiberRetraction p hp v)
        (projectionFiberRetraction p hp w) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (inner ℂ (p w) (x : H) • p v) = inner ℂ (p w) (x : H) • p v
  rw [map_smul]
  exact congrArg (_ • ·) (congrArg (fun L : H →L[ℂ] H => L v) hp.isIdempotentElem.eq)

theorem norm_projection_apply_le (p : H →L[ℂ] H) (hp : IsStarProjection p) (v : H) :
    ‖p v‖ ≤ ‖v‖ := by
  calc
    ‖p v‖ ≤ ‖p‖ * ‖v‖ := p.le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_projection_le_one p hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem norm_projection_rankOne_le (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) : ‖InnerProductSpace.rankOne ℂ (p v) (p w)‖ ≤ ‖v‖ * ‖w‖ := by
  rw [InnerProductSpace.norm_rankOne]
  exact mul_le_mul (norm_projection_apply_le p hp v) (norm_projection_apply_le p hp w)
    (norm_nonneg _) (norm_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

omit [CompleteSpace H] in
/-- Strongly measurable projection columns give strongly measurable
columns for every supported rank-one field. -/
theorem aestronglyMeasurable_projection_rankOne
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ v : H, AEStronglyMeasurable (fun a => p a v) μ) (v w x : H) :
    AEStronglyMeasurable
      (fun a => InnerProductSpace.rankOne ℂ (p a v) (p a w) x) μ := by
  exact ((hmeas w).inner aestronglyMeasurable_const).smul (hmeas v)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SupportedFieldRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported measurable fields are recovered exactly by compression to the
original Hilbert space. In particular, the supported rank-one tests used for
factor fibers come from actual original operators. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω H F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure Ω) (J : H →ₗᵢ[ℂ] Lp F 2 μ)

/-- An operator field supported on the original range is exactly the
zero extension of its compression. -/
theorem isometricExtension_boundedField_compression
    (p R : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (hmeas : ∀ v : F, AEStronglyMeasurable (fun x => R x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ C)
    (hleft : ∀ᵐ x ∂μ, p x * R x = R x)
    (hright : ∀ᵐ x ∂μ, R x * p x = R x) :
    isometricExtension J
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hmeas C hbound)).comp
        J.toContinuousLinearMap) = boundedFieldOperator μ R hmeas C hbound :=
  isometricExtension_compression J _
    (boundedFieldOperator_left_support μ R hmeas C hbound _ p hP hleft)
    (boundedFieldOperator_right_support μ R hmeas C hbound _ p hP hright)

variable [IsFiniteMeasure μ]

/-- The projection columns of the original range are strongly measurable. -/
theorem aestronglyMeasurable_isometric_projection_column
    (p : Ω → F →L[ℂ] F)
    (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))
    (v : F) : AEStronglyMeasurable (fun x => p x v) μ :=
  (Lp.aestronglyMeasurable (isometricExtension J 1 (Lp.const 2 μ v))).congr
    (pointwise_action_column μ _ p hP v)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CommonFieldCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compressing an actual measurable field in the common spectral model
returns an operator in the original abelian commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Expose the compression formula without unfolding its field operator. -/
theorem commonFieldCompression_eq
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    commonFieldCompression π D R hmeas C hbound =
      ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
        (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
          (cyclicCommonEmbedding π D).toContinuousLinearMap := rfl

theorem commonFieldCompression_mem
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    commonFieldCompression π D R hmeas C hbound ∈ starSubalgebraCommutant π.range := by
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
  rintro _ ⟨a, rfl⟩
  apply Eq.symm
  apply commonCompression_commutes_representation π D
  intro b
  rw [commonScalarRepresentation_apply]
  exact boundedFieldOperator_commutes_continuous (cyclicCommonBaseMeasure π D)
    R hmeas C hbound (gelfandStarTransform A b)

/-- The same compression belongs to any representation generating this
commutant. -/
theorem commonFieldCompression_mem_of_range_eq {B : Type*} [CStarAlgebra B]
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra σ = starSubalgebraCommutant π.range)
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp
      (boundedFieldOperator (cyclicCommonBaseMeasure π D) R hmeas C hbound)).comp
        (cyclicCommonEmbedding π D).toContinuousLinearMap ∈
      representationVonNeumannAlgebra σ := by
  have h := hgen.ge (commonFieldCompression_mem π D R hmeas C hbound)
  rw [commonFieldCompression_eq] at h
  exact h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SupportedRankOneMembership
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abstract isometric compression supplies supported rank-one members of
the actual fiber bicommutants. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {Ω F H B : Type u} [MeasurableSpace Ω] [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem ae_supported_projection_rankOne_mem (μ : Measure Ω) [IsFiniteMeasure μ]
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : Set Ω) (hs : MeasurableSet s) (hnull : μ sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hρ : ∀ b : B, ∀ f : Lp F 2 μ,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → Ω) μ,
        isometricExtension J (σ b) f x = ρ x (Unitization.inr b) (f x))
    (hcompression : ∀ (R : Ω → F →L[ℂ] F)
      (hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ)
      (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ C),
      ((J.toContinuousLinearMap.adjoint.comp (boundedFieldOperator μ R hm C hb)).comp
        J.toContinuousLinearMap) ∈ representationVonNeumannAlgebra σ)
    (v w : F) :
    ∀ᵐ x ∂μ, InnerProductSpace.rankOne ℂ
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) v)
      (projectionFiberRetraction
        (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
        (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) w) ∈
      representationVonNeumannAlgebra
        (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  let p := fun x => nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hp (x) : IsStarProjection (p x) :=
    nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)
  have hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J 1 f x = p x (f x) := by
    intro f
    have h := zeroExtendOperatorField_action μ s hs hnull
      (isometricExtension J (σ 1)) (fun x => ρ x (Unitization.inr 1)) (hρ 1) f
    simpa only [map_one, zeroExtendNonunitalRepresentation_apply, nonunitalUnitProjection,
      p] using h
  let R := fun x => InnerProductSpace.rankOne ℂ (p x v) (p x w)
  have hm : ∀ z, AEStronglyMeasurable (fun x => R x z) μ :=
    aestronglyMeasurable_projection_rankOne μ p
      (aestronglyMeasurable_isometric_projection_column μ J p hP) v w
  have hb : ∀ᵐ x ∂μ, ‖R x‖ ≤ ‖v‖ * ‖w‖ :=
    Eventually.of_forall fun x => norm_projection_rankOne_le (p x) (hp x) v w
  let Q := boundedFieldOperator μ R hm (‖v‖ * ‖w‖) hb
  let T := (J.toContinuousLinearMap.adjoint.comp Q).comp J.toContinuousLinearMap
  have hT : T ∈ representationVonNeumannAlgebra σ := hcompression R hm _ hb
  have he : isometricExtension J T = Q :=
    isometricExtension_boundedField_compression μ J p R hP hm _ hb
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).1)
      (Eventually.of_forall fun x => (projection_rankOne_support (p x) (hp x) v w).2)
  have haction : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ,
      isometricExtension J T f x = R x (f x) := by
    intro f
    rw [he]
    exact boundedFieldOperator_action μ R hm _ hb f
  have hmem := ae_global_projection_mem_of_isometric_closure μ s hs hnull J σ ρ hρ
    T hT R haction
  filter_upwards [hmem] with x hx
  change projectionFiberCompression (p x) (hp x)
    (InnerProductSpace.rankOne ℂ (p x v) (p x w)) ∈ _ at hx
  rw [projectionFiberCompression_rankOne] at hx
  exact hx

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonRankOneClosure
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported rank-one fields belong to the joint fiber bicommutant when
the source generates the original central commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A B H : Type u} [CommCStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Every compressed constant rank-one field lies almost everywhere in the
fiber bicommutant. Its original operator is constructed by compression. -/
theorem ae_common_projection_rankOne_mem
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra σ = starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : B, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (σ b) f x =
          ρ x (Unitization.inr b) (f x))
    (v w : ScalarHilbertCoordinates D.generators) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) v)
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) w) ∈
        representationVonNeumannAlgebra
          (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  exact ae_supported_projection_rankOne_mem (cyclicCommonBaseMeasure π D)
    (cyclicCommonEmbedding π D) σ s hs hnull ρ hρ
    (commonFieldCompression_mem_of_range_eq π D σ hgen) v w

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_JointCStarSource
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

theorem jointCStarSource_minimal (B C S : StarSubalgebra ℂ A)
    (hB : B ≤ S) (hC : C ≤ S) (hS : IsClosed (S : Set A)) :
    jointCStarSource B C ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (sup_le hB hC) hS

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointFiberCommutants
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Central elements of a joint fiber representation

For commuting sources `B,C`, a central element of the represented
bicommutant of `B` commutes with the full joint bicommutant. The proof uses
norm generation of the joint source, with no normality assertion for a
pointwise fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A representation of the joint norm closure lands in any closed star
algebra containing the represented copies of both sources. -/
theorem joint_source_representation_mem
    (B C : StarSubalgebra ℂ A)
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (N : StarSubalgebra ℂ (K →L[ℂ] K)) (hN : IsClosed (N : Set (K →L[ℂ] K)))
    (hB : ∀ b : B, σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) ∈ N)
    (hC : ∀ c : C, σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈ N)
    (s : jointCStarSource B C) : σ s ∈ N := by
  let D := N.comap σ
  have hD : IsClosed (D : Set (jointCStarSource B C)) :=
    hN.preimage (map_continuous σ)
  have hImage : IsClosed ((D.map (jointCStarSource B C).subtype) : Set A) := by
    rw [StarSubalgebra.coe_map]
    exact (jointCStarSource_isClosed B C).isClosedMap_subtype_val _ hD
  have hb : B ≤ D.map (jointCStarSource B C).subtype := by
    intro b hb
    exact ⟨StarSubalgebra.inclusion (le_jointCStarSource_left B C) ⟨b, hb⟩,
      hB ⟨b, hb⟩, rfl⟩
  have hc : C ≤ D.map (jointCStarSource B C).subtype := by
    intro c hc
    exact ⟨StarSubalgebra.inclusion (le_jointCStarSource_right B C) ⟨c, hc⟩,
      hC ⟨c, hc⟩, rfl⟩
  obtain ⟨t, ht, hts⟩ := jointCStarSource_minimal B C _ hb hc hImage s.property
  have heq : t = s := Subtype.ext hts
  change σ t ∈ N at ht
  simpa only [heq] using ht

/-- The represented second source commutes with the bicommutant of the
first source, since the two original sources commute. -/
theorem joint_second_mem_first_commutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (c : C) :
    σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈
      (representationVonNeumannAlgebra
        (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))).commutant := by
  apply (mem_representation_commutant_iff _ _).mpr
  rintro _ ⟨b, rfl⟩
  change σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) *
      σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) =
    σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) *
      σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b)
  rw [← map_mul, ← map_mul]
  apply congrArg σ
  apply Subtype.ext
  exact hBC b c

/-- Centrality in the first represented bicommutant gives commutation with
the entire joint representation. -/
theorem joint_center_mem_joint_commutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C))))) :
    T ∈ (representationVonNeumannAlgebra σ).commutant := by
  let σB := σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C))
  let P := representationVonNeumannAlgebra σB
  have ht : T ∈ P := hT.1
  have htc : T ∈ P.commutant := hT.2
  have hst : star T ∈ P := star_mem ht
  have hstc : star T ∈ P.commutant := star_mem htc
  let N := StarSubalgebra.centralizer ℂ ({T} : Set (K →L[ℂ] K))
  have hN : IsClosed (N : Set (K →L[ℂ] K)) := by
    rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hb : ∀ b : B, σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) ∈ N := by
    intro b
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = T := Set.mem_singleton_iff.mp hg
    subst g
    have hmem : σB b ∈ P := mem_representationVonNeumannAlgebra σB b
    exact ⟨((VonNeumannAlgebra.mem_commutant_iff.mp htc) _ hmem).symm,
      ((VonNeumannAlgebra.mem_commutant_iff.mp hstc) _ hmem).symm⟩
  have hc : ∀ c : C, σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈ N := by
    intro c
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = T := Set.mem_singleton_iff.mp hg
    subst g
    have hmem := joint_second_mem_first_commutant B C hBC σ c
    exact ⟨(VonNeumannAlgebra.mem_commutant_iff.mp hmem) _ ht,
      (VonNeumannAlgebra.mem_commutant_iff.mp hmem) _ hst⟩
  apply (mem_representation_commutant_iff σ T).mpr
  rintro _ ⟨s, rfl⟩
  have hmem := joint_source_representation_mem B C σ N hN hb hc s
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hmem) T (Set.mem_singleton T)).1.symm

/-- In particular a central first-source operator commutes with every
operator in the represented joint bicommutant, including rank-one tests. -/
theorem joint_center_commutes_joint_bicommutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (T Q : K →L[ℂ] K)
    (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))))
    (hQ : Q ∈ representationVonNeumannAlgebra σ) : T * Q = Q * T :=
  ((VonNeumannAlgebra.mem_commutant_iff.mp
    (joint_center_mem_joint_commutant B C hBC σ T hT)) Q hQ).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_GlobalFiberRestriction
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and zero extension of range representations

The old-unit projection is unchanged by restriction along a unital map,
even when the represented map is nonunital. Restriction commutes with
zero extension from a conull base, so the canonical range identifications
are available at every base point, including the zero fibers.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {Ω : Type*} (s : Set Ω)
    (φ : B →⋆ₐ[ℂ] S) (ρ : ∀ _x : s, Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F))

theorem globalRestrictionFiberEquiv_intertwines (x : Ω) (b : B)
    (v : projectionFiber
      (nonunitalUnitProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))
      (nonunitalUnitProjection_isStarProjection
        (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x))) :
    globalRestrictionFiberEquiv s φ ρ x
        (nonunitalRangeRepresentation
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) b v) =
      nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x) (φ b)
        (globalRestrictionFiberEquiv s φ ρ x v) := by
  apply Subtype.ext
  simp only [globalRestrictionFiberEquiv_coe, nonunitalRangeRepresentation_coe]
  exact congrArg (fun τ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F) => τ b (v : F))
    (zeroExtend_unitizationRestrict s φ ρ x)

/-- Exact equality of the global zero-extended range representations. -/
theorem globalRestriction_range_conjugacy (x : Ω) :
    (globalRestrictionFiberEquiv s φ ρ x).conjStarAlgEquiv.toStarAlgHom.comp
        (nonunitalRangeRepresentation
          (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x)) =
      (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)).comp φ := by
  apply StarAlgHom.ext
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change globalRestrictionFiberEquiv s φ ρ x
    (nonunitalRangeRepresentation
      (zeroExtendNonunitalRepresentation s (fun y => unitizationRestrict φ (ρ y)) x) b
      ((globalRestrictionFiberEquiv s φ ρ x).symm v)) =
    nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x) (φ b) v
  rw [globalRestrictionFiberEquiv_intertwines, LinearIsometryEquiv.apply_symm_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointRankOneFactors
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable rank-one tests in the joint representation force the first
source's represented von Neumann algebra to be a factor. -/

noncomputable section
namespace KadisonSimilarity

variable {A K ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- No measurable selection is needed: centrality and dense rank-one tests
in the joint bicommutant force each central operator to be scalar. -/
theorem joint_first_scalar_center_of_rankOne
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (d : ι → K) (hd : DenseRange d)
    (hRank : ∀ i j, InnerProductSpace.rankOne ℂ (d i) (d j) ∈
      representationVonNeumannAlgebra σ) :
    ∀ a : (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  intro a ha
  have hcenter : (a : K →L[ℂ] K) ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))) := by
    refine ⟨a.property, VonNeumannAlgebra.mem_commutant_iff.mpr ?_⟩
    intro b hb
    exact (congrArg Subtype.val (ha ⟨b, hb⟩)).symm
  obtain ⟨c, hc⟩ := scalar_of_commutes_dense_rankOne d hd (a : K →L[ℂ] K)
    (fun i j => joint_center_commutes_joint_bicommutant B C hBC σ a _ hcenter (hRank i j))
  refine ⟨c, Subtype.ext ?_⟩
  change (a : K →L[ℂ] K) = c • (1 : K →L[ℂ] K)
  exact hc

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RepresentationCenterTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar centers and exact representation conjugacy

An algebra equivalence between the ambient operator algebras transports
the represented bicommutants and their centers. In particular, identifying
two equal projection ranges does not change the factor-fiber criterion.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem representation_bicommutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    θ T ∈ representationVonNeumannAlgebra ρ := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT ⊢
  intro Q hQ
  have hpre : θ.symm Q ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
    rintro _ ⟨a, rfl⟩
    apply θ.injective
    change θ (σ a * θ.symm Q) = θ (θ.symm Q * σ a)
    simp only [map_mul]
    change θ (σ a) * θ (θ.symm Q) = θ (θ.symm Q) * θ (σ a)
    rw [θ.apply_symm_apply, hθ]
    exact hQ (ρ a) ⟨a, rfl⟩
  have h := congrArg θ (hT (θ.symm Q) hpre)
  simpa only [map_mul, θ.apply_symm_apply] using h

theorem representation_commutant_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ (representationVonNeumannAlgebra σ).commutant) :
    θ T ∈ (representationVonNeumannAlgebra ρ).commutant := by
  apply (mem_representation_commutant_iff ρ (θ T)).mpr
  have ht := (mem_representation_commutant_iff σ T).mp hT
  rintro _ ⟨a, rfl⟩
  change ρ a * θ T = θ T * ρ a
  simpa only [map_mul, hθ] using congrArg θ (ht (σ a) ⟨a, rfl⟩)

theorem representation_center_map_mem
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (T : H →L[ℂ] H) (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra σ)) :
    θ T ∈ vonNeumannCenter (representationVonNeumannAlgebra ρ) :=
  ⟨representation_bicommutant_map_mem θ σ ρ hθ T hT.1,
    representation_commutant_map_mem θ σ ρ hθ T hT.2⟩

/-- The scalar-center condition used for factor fibers is unchanged by an
exact star-algebra conjugacy of the representations. -/
theorem scalar_center_of_representation_equiv
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hθ : ∀ a, θ (σ a) = ρ a)
    (hρ : ∀ a : (representationVonNeumannAlgebra ρ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c) :
    ∀ a : (representationVonNeumannAlgebra σ).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  intro a ha
  have haCenter : (a : H →L[ℂ] H) ∈
      vonNeumannCenter (representationVonNeumannAlgebra σ) := by
    refine ⟨a.property, VonNeumannAlgebra.mem_commutant_iff.mpr ?_⟩
    intro b hb
    exact (congrArg Subtype.val (ha ⟨b, hb⟩)).symm
  have hθCenter := representation_center_map_mem θ σ ρ hθ a haCenter
  let aρ : (representationVonNeumannAlgebra ρ).toStarSubalgebra := ⟨θ a, hθCenter.1⟩
  have hcomm : ∀ b, aρ * b = b * aρ := by
    intro b
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hθCenter.2) b b.property).symm
  obtain ⟨c, hc⟩ := hρ aρ hcomm
  refine ⟨c, Subtype.ext ?_⟩
  apply θ.injective
  have hval := congrArg Subtype.val hc
  change θ (a : H →L[ℂ] H) = algebraMap ℂ (K →L[ℂ] K) c at hval
  change θ (a : H →L[ℂ] H) = θ (algebraMap ℂ (H →L[ℂ] H) c)
  simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] using hval

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointFiberFactorCriterion
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many rank-one members of joint fibers imply scalar centers
for the restricted source, on any measurable base. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

variable {A F Ω : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace Ω]

theorem ae_joint_fiber_scalar_center
    (B C : StarSubalgebra ℂ A) [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (μ : Measure Ω) (s : Set Ω)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ] (F →L[ℂ] F))
    (d : ℕ → F) (hd : DenseRange d)
    (hRank : ∀ i j : ℕ, ∀ᵐ x ∂μ,
      InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) (d i))
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) (d j)) ∈
        representationVonNeumannAlgebra
          (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x))) :
    ∀ᵐ x ∂μ,
      ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation
        (zeroExtendNonunitalRepresentation s
          (fun y => unitizationRestrict
            (StarSubalgebra.inclusion (le_jointCStarSource_left B C)) (ρ y)) x))).toStarSubalgebra,
        (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  let φ := StarSubalgebra.inclusion (le_jointCStarSource_left B C)
  let τ := zeroExtendNonunitalRepresentation s ρ
  let p := fun x => nonunitalUnitProjection (τ x)
  let hp := fun x => nonunitalUnitProjection_isStarProjection (τ x)
  have hall := eventually_countable_forall.mpr fun i =>
    eventually_countable_forall.mpr fun j => hRank i j
  filter_upwards [hall] with x hx
  have hscalar := joint_first_scalar_center_of_rankOne B C hBC
    (nonunitalRangeRepresentation (τ x))
    (fun i => projectionFiberRetraction (p x) (hp x) (d i))
    (projectionFiber_denseRange d hd (p x) (hp x)) hx
  apply scalar_center_of_representation_equiv
    (globalRestrictionFiberEquiv s φ ρ x).conjStarAlgEquiv
    _ ((nonunitalRangeRepresentation (τ x)).comp φ) _ hscalar
  intro b
  exact congrArg (fun f => f b) (globalRestriction_range_conjugacy s φ ρ x)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonFiberFactors
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common joint source gives factor fibers for the first algebra,
using countably many compressed constant rank-one tests. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A H : Type u} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- The first source's genuine range fibers have scalar center almost
everywhere when the joint source generates the central commutant. -/
theorem ae_common_fiber_scalar_center_oai
    (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hBC : ∀ b : B, ∀ c : C, (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
      (c : H →L[ℂ] H) * (b : H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
      starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : jointCStarSource B C, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρ x (Unitization.inr b) (f x)) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      commonFirstFiberScalarCenter π D B C s ρ x := by
  apply ae_joint_fiber_scalar_center B C hBC (cyclicCommonBaseMeasure π D) s ρ
    (TopologicalSpace.denseSeq (ScalarHilbertCoordinates D.generators))
    (TopologicalSpace.denseRange_denseSeq (ScalarHilbertCoordinates D.generators))
  intro i j
  exact ae_common_projection_rankOne_mem π D (jointCStarSource B C).subtype
    hgen s hs hnull ρ hρ _ _

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.ae_common_fiber_scalar_center_oai.{u} := @OAI.KadisonSimilarity.ae_common_fiber_scalar_center_oai.{u}
