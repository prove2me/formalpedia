-- Prove2me | solution 1 for OAI.KadisonKastler.exists_signed_cyclic_functional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:40:58.846758+00:00
-- url     : https://prove2.me/submissions/4bd129fc-65f5-4bc2-b130-7a83a000a6b2

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Zorn
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K006

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic column factorization from equality of vector functionals

Equality of quadratic forms yields an intertwining column contraction.
Existence of a realizing vector is a consequence of standard form.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The algebraic orbit is dense in its closed cyclic subspace. -/
theorem orbitIntoClosure_dense (N : StarSubalgebra ℂ (K →L[ℂ] K)) (ζ : K) :
    DenseRange (orbitIntoClosure N ζ) := by
  change Dense (Set.range (orbitIntoClosure N ζ))
  rw [Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (orbitLinearMap N ζ)) ⊆
    closure (Set.range (orbitLinearMap N ζ))
  exact Set.Subset.rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every unital star representation is the orthogonal sum of cyclic reducing
representations. The family is constructed by Zorn's lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

/-- The original vector has dense orbit for the restricted action. -/
theorem orbitGenerator_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    DenseRange (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) := by
  change Dense (Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)))
  have hset : Set.range (fun a : A => orbitRepresentation σ ξ a (orbitGenerator σ ξ)) =
      Set.range (orbitIntoClosure σ.range ξ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ.rangeRestrict a, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      refine ⟨b, ?_⟩
      apply Subtype.ext
      change σ b ξ = (a : H →L[ℂ] H) ξ
      change σ b = (a : H →L[ℂ] H) at hb
      rw [hb]
  rw [hset]
  exact orbitIntoClosure_dense σ.range ξ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicCoefficientNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.HochschildNormalPart.scalarNormalPart_coefficient _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm-attaining coefficient models have cyclic sign vectors

Equality in the coefficient norm estimate places the left vector in the
closed orbit of the right vector. For a commuting sign operator, this
makes that cyclic space invariant under the sign.
-/

namespace KadisonKastler

noncomputable section

open KadisonSimilarity HochschildNormalPart
open scoped InnerProductSpace

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficient_norm_eq_mem_orbitClosure
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ η : H)
    (hn : ‖η‖ = ‖ξ‖) (hf : ‖coefficient π η ξ‖ = ‖ξ‖ ^ 2) :
    η ∈ orbitClosure π.range ξ := by
  let K := orbitClosure π.range ξ
  have hcoeff : coefficient π (K.toSubmodule.starProjection η) ξ = coefficient π η ξ := by
    ext a
    change inner ℂ (K.toSubmodule.starProjection η) (π a ξ) = inner ℂ η (π a ξ)
    rw [K.toSubmodule.inner_starProjection_left_eq_right]
    congr 1
    apply K.toSubmodule.starProjection_eq_self_iff.mpr
    exact (LinearMap.range (orbitLinearMap π.range ξ)).le_topologicalClosure
      ⟨π.rangeRestrict a, rfl⟩
  apply (K.toSubmodule.mem_iff_norm_starProjection η).mpr
  by_cases hz : ‖ξ‖ = 0
  · have hη : η = 0 := norm_eq_zero.mp (hn.trans hz)
    simp [hη]
  · have hp := coefficient_norm π (K.toSubmodule.starProjection η) ξ
    rw [hcoeff, hf, sq] at hp
    have hle : ‖ξ‖ ≤ ‖K.toSubmodule.starProjection η‖ :=
      (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hz))).mp hp
    apply le_antisymm (K.toSubmodule.norm_starProjection_apply_le η)
    rw [hn]
    exact hle

theorem commuting_operator_preserves_orbitClosure
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H)
    (hS : ∀ a, Commute S (π a)) (hξ : S ξ ∈ orbitClosure π.range ξ) :
    ∀ x ∈ orbitClosure π.range ξ, S x ∈ orbitClosure π.range ξ := by
  let K := orbitClosure π.range ξ
  have hle : K.toSubmodule ≤ K.toSubmodule.comap S.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro x ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      change π b = a.val at hb
      change S (a.val ξ) ∈ K
      rw [← hb]
      have he := congrArg (fun T : H →L[ℂ] H => T ξ) (hS b).eq
      change S (π b ξ) = π b (S ξ) at he
      rw [he]
      exact orbitClosure_invariant π.range ξ (π.rangeRestrict b) _ hξ
    · exact K.isClosed.preimage S.continuous
  exact fun x hx => hle hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianPositiveDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm-additive positive decomposition of a Hermitian functional

The real Hahn–Banach pair construction already in the library gives the
positive and negative parts with the exact total norm needed by Sakai's
extreme-functional argument.
-/

namespace KadisonKastler

noncomputable section

open HochschildPositiveDecomposition NaimarkZFC
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]

theorem exists_norm_additive_positive_decomposition (f : A →L[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a)) :
    ∃ p q : A →ₚ[ℂ] ℂ, (∀ a, f a = p a - q a) ∧
      (p 1).re + (q 1).re = ‖f‖ := by
  let l := realRestriction f
  obtain ⟨g, hgn, hg1, hgl⟩ := exists_pair_extension l
  let p₀ := g.comp (ContinuousLinearMap.inl ℝ (selfAdjoint A) (selfAdjoint A))
  let q₀ := g.comp (ContinuousLinearMap.inr ℝ (selfAdjoint A) (selfAdjoint A))
  have hp₀ (a : selfAdjoint A) (ha : 0 ≤ (a : A)) : 0 ≤ p₀ a :=
    pair_nonneg g (norm_nonneg l) hgn hg1 a 0 ha (by simp)
  have hq₀ (a : selfAdjoint A) (ha : 0 ≤ (a : A)) : 0 ≤ q₀ a :=
    pair_nonneg g (norm_nonneg l) hgn hg1 0 a (by simp) ha
  let p := complexifyPositive p₀.toLinearMap hp₀
  let q := complexifyPositive q₀.toLinearMap hq₀
  have hdiff (a : selfAdjoint A) : l a = p₀ a - q₀ a := by
    rw [← hgl]
    change g (a, -a) = g (a, 0) - g (0, a)
    rw [← map_sub]
    congr 1
    simp
  have heq : f.toLinearMap = p.toLinearMap - q.toLinearMap := by
    apply complexLinear_eq_of_selfAdjoint
    intro a
    change f (a : A) = p (a : A) - q (a : A)
    rw [complexifyPositive_apply, complexifyPositive_apply,
      complexify_selfAdjoint, complexify_selfAdjoint]
    have hi := congrArg Complex.im (hf (a : A))
    rw [a.property.star_eq, Complex.star_def, Complex.conj_im] at hi
    apply Complex.ext
    · exact hdiff a
    · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      linarith
  have hsum : (p 1).re + (q 1).re = ‖l‖ := by
    change (complexify p₀.toLinearMap ((1 : selfAdjoint A) : A)).re +
      (complexify q₀.toLinearMap ((1 : selfAdjoint A) : A)).re = ‖l‖
    rw [complexify_selfAdjoint, complexify_selfAdjoint]
    change g (1, 0) + g (0, 1) = ‖l‖
    rw [← map_add]
    simpa using hg1
  have hfbound : ‖f‖ ≤ ‖l‖ := by
    apply f.opNorm_le_bound (norm_nonneg l)
    intro a
    have ha : f a = p a - q a := congrArg (fun F : A →ₗ[ℂ] ℂ => F a) heq
    rw [ha]
    calc
      ‖p a - q a‖ ≤ ‖p a‖ + ‖q a‖ := norm_sub_le _ _
      _ ≤ (p 1).re * ‖a‖ + (q 1).re * ‖a‖ :=
        add_le_add (positive_norm_apply_le p a) (positive_norm_apply_le q a)
      _ = ‖l‖ * ‖a‖ := by rw [← add_mul, hsum]
  have hn : ‖l‖ = ‖f‖ := le_antisymm (realRestriction_norm f) hfbound
  refine ⟨p, q, ?_, hsum.trans hn⟩
  intro a
  exact congrArg (fun F : A →ₗ[ℂ] ℂ => F a) heq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SignedCyclicFunctional
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A cyclic signed-vector model for a Hermitian functional

The norm-additive positive parts give a two-summand GNS representation.
Equality in the coefficient norm bound makes its sign preserve the cyclic
subspace. Restricting there gives the precise model used in the separation
argument, with no polar-decomposition hypothesis.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC HochschildNormalPart KadisonSimilarity
open scoped InnerProductSpace

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_signed_cyclic_functional_oai (f : A →L[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a)) (hfn : ‖f‖ = 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H),
      ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) ∧
      IsSelfAdjoint S ∧ S * S = 1 ∧
      (∀ a, Commute S (π a)) ∧ ∀ a, f a = inner ℂ (S ξ) (π a ξ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨p, q, hpq, hn⟩ := exists_norm_additive_positive_decomposition f hf
  let H₀ := WithLp 2 (p.GNS × q.GNS)
  let π : A →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀) := sumRepresentation p.gnsStarAlgHom q.gnsStarAlgHom
  let ξ : H₀ := WithLp.toLp 2 (gnsVector p, gnsVector q)
  let S : H₀ →L[ℂ] H₀ := sumOperator 1 (-1)
  have hSnorm (x : H₀) : ‖S x‖ = ‖x‖ := by
    have hs := WithLp.prod_norm_sq_eq_of_L2 (S x)
    have hx := WithLp.prod_norm_sq_eq_of_L2 x
    change ‖S x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖-x.snd‖ ^ 2 at hs
    rw [norm_neg] at hs
    nlinarith [norm_nonneg (S x), norm_nonneg x]
  have hSsq : S * S = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change WithLp.toLp 2 (x.fst, - - x.snd) = x
    rw [neg_neg]
    rfl
  have hSstar : IsSelfAdjoint S := by
    have he : S = S.adjoint := by
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ x.fst y.fst + inner ℂ (-x.snd) y.snd =
        inner ℂ x.fst y.fst + inner ℂ x.snd (-y.snd)
      simp only [inner_neg_left, inner_neg_right]
    exact he.symm
  have hScomm (a : A) : Commute S (π a) := by
    apply ContinuousLinearMap.ext
    intro x
    change WithLp.toLp 2 (p.gnsStarAlgHom a x.fst, -(q.gnsStarAlgHom a x.snd)) =
      WithLp.toLp 2 (p.gnsStarAlgHom a x.fst, q.gnsStarAlgHom a (-x.snd))
    simp only [map_neg]
  have hξsq : ‖ξ‖ ^ 2 = ‖f‖ := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (congrArg₂ (· + ·) (gnsVector_norm_sq p) (gnsVector_norm_sq q)).trans hn
  have hξn : ‖ξ‖ = 1 := by
    rw [hfn] at hξsq
    nlinarith [norm_nonneg ξ]
  have hcoeff : coefficient π (S ξ) ξ = f := by
    ext a
    change inner ℂ (gnsVector p) (p.gnsStarAlgHom a (gnsVector p)) +
      inner ℂ (-gnsVector q) (q.gnsStarAlgHom a (gnsVector q)) = f a
    rw [inner_neg_left, gnsVector_coefficient, gnsVector_coefficient]
    exact (hpq a).symm
  have hSξ : S ξ ∈ orbitClosure π.range ξ :=
    coefficient_norm_eq_mem_orbitClosure π ξ (S ξ) (hSnorm ξ)
      (by rw [hcoeff, hξsq])
  have hinv := commuting_operator_preserves_orbitClosure π ξ S hScomm hSξ
  let K := orbitClosure π.range ξ
  let T : K →L[ℂ] K := S.restrict hinv
  let ρ := orbitRepresentation π ξ
  let ζ := orbitGenerator π ξ
  refine ⟨K, inferInstance, inferInstance, inferInstance, ρ, ζ, T,
    hξn, orbitGenerator_dense π ξ, ?_, ?_, ?_, ?_⟩
  · have he : T = T.adjoint := by
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ (S x.val) y.val = inner ℂ x.val (S y.val)
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hSstar.star_eq]
    exact he.symm
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun R : H₀ →L[ℂ] H₀ => R x.val) hSsq
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun R : H₀ →L[ℂ] H₀ => R x.val) (hScomm a).eq
  · intro a
    exact (congrArg (fun F : A →L[ℂ] ℂ => F a) hcoeff).symm

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_signed_cyclic_functional_oai.{u} := @OAI.KadisonKastler.exists_signed_cyclic_functional_oai.{u}
