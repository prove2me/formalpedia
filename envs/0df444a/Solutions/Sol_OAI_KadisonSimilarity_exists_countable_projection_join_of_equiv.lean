-- Prove2me | solution 1 for OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:42:12.946134+00:00
-- url     : https://prove2.me/submissions/42e775ac-e5a5-4344-993a-3f2466521a14

import Mathlib
import Definitions.Def_OAIQ075A014
import Definitions.Def_OAIQ075A017
import Definitions.Def_OAIQ075A018

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_rangeSupport (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    B * rangeSupport B = B := by
  have h := congrArg star (rangeSupport_mul B)
  simpa only [star_mul, hB.star_eq, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq]
    using h

/-- Annihilating the range also annihilates its orthogonal support. -/
theorem mul_rangeSupport_eq_zero (B C : H →L[ℂ] H) (h : C * B = 0) :
    C * rangeSupport B = 0 := by
  have hh : operatorRangeClosure B ≤ C.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun S : H →L[ℂ] H => S x) h
    · exact C.isClosed_ker
  ext x
  exact hh ((operatorRangeClosure B).starProjection_apply_mem x)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalSupportTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Range supports are preserved by star isomorphisms between concrete von
Neumann algebras. The proof uses their algebraic least-support property, so
no continuity in the weak operator topology is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any left identity on an operator is a left identity on its range support. -/
theorem rangeSupport_least_left (B p : H →L[ℂ] H) (h : p * B = B) :
    p * rangeSupport B = rangeSupport B := by
  have hz : (1 - p) * B = 0 := by rw [sub_mul, one_mul, h, sub_self]
  have hs := mul_rangeSupport_eq_zero B (1 - p) hz
  rw [sub_mul, one_mul, sub_eq_zero] at hs
  exact hs.symm

theorem normalRangeSupport_isStarProjection (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) : IsStarProjection (normalRangeSupport M a) := by
  constructor
  · apply Subtype.ext
    exact (rangeSupport_isStarProjection (a : H →L[ℂ] H)).isIdempotentElem.eq
  · apply Subtype.ext
    exact (rangeSupport_isStarProjection (a : H →L[ℂ] H)).isSelfAdjoint.star_eq

theorem normalRangeSupport_mul (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    normalRangeSupport M a * a = a := by
  apply Subtype.ext
  exact rangeSupport_mul (a : H →L[ℂ] H)

theorem normalRangeSupport_least (M : VonNeumannAlgebra H)
    (a p : M.toStarSubalgebra) (h : p * a = a) :
    p * normalRangeSupport M a = normalRangeSupport M a := by
  apply Subtype.ext
  exact rangeSupport_least_left (a : H →L[ℂ] H) p (congrArg Subtype.val h)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_PolarPartialIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete right supports in a finite tracial von Neumann algebra

The partial isometry is constructed by extending the isometry
`sqrt(x* x) ξ ↦ x ξ` from its dense range and setting it to zero on the
orthogonal complement. Bicommutant closure keeps that operator in the algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem polarPartialIsometry_mul_modulus (x : H →L[ℂ] H) :
    polarPartialIsometry x * polarModulus x = x := by
  ext ξ
  have he : (operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
      (polarModulus x ξ) = rangeIntoClosure (polarModulus x) ξ := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩)
  change polarRangeIsometry x
    ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto (polarModulus x ξ)) = x ξ
  rw [he, polarRangeIsometry_apply]

theorem polarPartialIsometry_initial (x : H →L[ℂ] H) :
    star (polarPartialIsometry x) * polarPartialIsometry x = rangeSupport (polarModulus x) := by
  let M := operatorRangeClosure (polarModulus x)
  let J := (polarRangeIsometry x).toContinuousLinearMap
  let Q := M.orthogonalProjectionOnto
  change (J.comp Q).adjoint.comp (J.comp Q) = M.starProjection
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    (Q.adjoint.comp J.adjoint).comp (J.comp Q) =
        Q.adjoint.comp ((J.adjoint.comp J).comp Q) := by simp only [ContinuousLinearMap.comp_assoc]
    _ = M.subtypeL.comp Q := by
      rw [(polarRangeIsometry x).adjoint_comp_self, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp, Submodule.adjoint_orthogonalProjectionOnto]
    _ = M.starProjection := rfl

theorem polarPartialIsometry_mul_initial (x : H →L[ℂ] H) :
    polarPartialIsometry x * rangeSupport (polarModulus x) = polarPartialIsometry x := by
  ext ξ
  change polarRangeIsometry x
      ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
        ((operatorRangeClosure (polarModulus x)).starProjection ξ)) =
    polarRangeIsometry x ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto ξ)
  congr 1
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T ξ)
    (rangeSupport_isStarProjection (polarModulus x)).isIdempotentElem.eq

theorem polarPartialIsometry_final (x : H →L[ℂ] H) :
    IsStarProjection (polarPartialIsometry x * star (polarPartialIsometry x)) := by
  constructor
  · change (polarPartialIsometry x * star (polarPartialIsometry x)) *
      (polarPartialIsometry x * star (polarPartialIsometry x)) = _
    calc
      _ = (polarPartialIsometry x *
          (star (polarPartialIsometry x) * polarPartialIsometry x)) *
          star (polarPartialIsometry x) := by simp only [mul_assoc]
      _ = polarPartialIsometry x * star (polarPartialIsometry x) := by
        rw [polarPartialIsometry_initial, polarPartialIsometry_mul_initial]
  · exact IsSelfAdjoint.mul_star_self _

/-- A left support of x is also a left support of its polar partial isometry. -/
theorem leftSupport_polarPartialIsometry (x q : H →L[ℂ] H) (hqx : q * x = x) :
    q * polarPartialIsometry x = polarPartialIsometry x := by
  have he : ∀ ξ : operatorRangeClosure (polarModulus x),
      q (polarRangeIsometry x ξ) = polarRangeIsometry x ξ := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      rw [polarRangeIsometry_apply]
      exact congrArg (fun T : H →L[ℂ] H => T η) hqx
    · exact isClosed_eq (q.continuous.comp (polarRangeIsometry x).continuous)
        (polarRangeIsometry x).continuous
  ext ξ
  exact he _

/-- Commutation on the two dense range maps extends to the polar isometry. -/
theorem polarPartialIsometry_commutes (x T : H →L[ℂ] H)
    (hx : Commute x T) (hS : Commute (polarModulus x) T)
    (hSstar : Commute (polarModulus x) (star T)) :
    Commute (polarPartialIsometry x) T := by
  let M := operatorRangeClosure (polarModulus x)
  let J := polarRangeIsometry x
  let Q := M.orthogonalProjectionOnto
  let R : M →L[ℂ] M := T.restrict (fun ξ hξ => operatorRangeClosure_invariant _ T hS hξ)
  have hJ : ∀ ξ : M, J (R ξ) = T (J ξ) := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      have hR : R (rangeIntoClosure (polarModulus x) η) =
          rangeIntoClosure (polarModulus x) (T η) := by
        apply Subtype.ext
        exact (congrArg (fun S : H →L[ℂ] H => S η) hS.eq).symm
      rw [hR, polarRangeIsometry_apply, polarRangeIsometry_apply]
      exact congrArg (fun S : H →L[ℂ] H => S η) hx.eq
    · exact isClosed_eq (J.continuous.comp R.continuous) (T.continuous.comp J.continuous)
  have hQ (ξ : H) : Q (T ξ) = R (Q ξ) := by
    apply Subtype.ext
    exact congrArg (fun S : H →L[ℂ] H => S ξ) (rangeSupport_commutes _ T hS hSstar).eq
  change polarPartialIsometry x * T = T * polarPartialIsometry x
  ext ξ
  change J (Q (T ξ)) = T (J (Q ξ))
  rw [hQ, hJ]

theorem polarModulus_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarModulus x ∈ P := by
  let : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  rw [polarModulus, CFC.sqrt_eq_real_sqrt (star x * x) (star_mul_self_nonneg x)]
  have hxstar : star x ∈ P.toStarSubalgebra := star_mem hx
  have hxx : star x * x ∈ P.toStarSubalgebra := P.toStarSubalgebra.mul_mem hxstar hx
  exact cfcₙ_mem (𝕜' := ℂ) (s := P.toStarSubalgebra) Real.sqrt hxx

theorem polarPartialIsometry_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarPartialIsometry x ∈ P := by
  suffices polarPartialIsometry x ∈ P.commutant.commutant by simpa using this
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hS := polarModulus_mem P x hx
  exact (polarPartialIsometry_commutes x T
    (VonNeumannAlgebra.mem_commutant_iff.mp hT x hx)
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _ hS)
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hT) _ hS)).eq.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-half spectral rounding inequality

The cutoff is the support of the positive part of `2a-1`.  Its polynomial
order inequality implies the required L² inequality for every positive
functional on a concrete von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isStarProjection_subtype_of_coe {R S : Type*} [Mul R] [Star R]
    [SetLike S R] [MulMemClass S R] [StarMemClass S R] {s : S}
    (x : s) (hp : IsStarProjection (x : R)) : IsStarProjection x := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialRightSupportDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right support trace bounds from the constructed polar partial isometry -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace comparison needs only traciality and positivity once the polar
partial isometry has been constructed. -/
theorem trace_initial_le_leftSupport {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (v q : A) (hq : IsStarProjection q) (hv : IsStarProjection (v * star v))
    (hqv : q * v = v) : (τ (star v * v)).re ≤ (τ q).re := by
  have hqs : q * (v * star v) = v * star v := by rw [← mul_assoc, hqv]
  have hpos := τ.map_nonneg (hv.sub_of_mul_eq_right hq hqs).nonneg
  change 0 ≤ τ (q - v * star v) at hpos
  have ht : τ (v * star v) = τ (star v * v) := htr _ _
  rw [map_sub, ht] at hpos
  exact sub_nonneg.mp (show 0 ≤ (τ q).re - (τ (star v * v)).re from hpos.1)

section Tracial
variable (P : VonNeumannAlgebra H)
attribute [local instance] OAI.KadisonSimilarity.supportClosed
attribute [local instance] OAI.KadisonSimilarity.supportCStar
attribute [local instance] OAI.KadisonSimilarity.supportOrder
local instance supportStarOrder : StarOrderedRing P.toStarSubalgebra := inferInstance

/-- The constructed right support has trace no larger than any containing
left support. No normality of the tracial positive functional is used. -/
theorem exists_rightSupport_trace_le
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (q x : P.toStarSubalgebra) (hq : IsStarProjection q) (hqx : q * x = x) :
    ∃ r : P.toStarSubalgebra, IsStarProjection r ∧ (τ r).re ≤ (τ q).re ∧ x * r = x := by
  let v : P.toStarSubalgebra :=
    ⟨polarPartialIsometry (x : H →L[ℂ] H), polarPartialIsometry_mem P x x.property⟩
  let r : P.toStarSubalgebra := ⟨rangeSupport (polarModulus (x : H →L[ℂ] H)),
    rangeSupport_mem P _ (polarModulus_mem P x x.property)⟩
  have hr : IsStarProjection r := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (rangeSupport (polarModulus (x : H →L[ℂ] H)))
    exact rangeSupport_isStarProjection (H := H) (polarModulus (x : H →L[ℂ] H))
  have hv : IsStarProjection (v * star v) := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (polarPartialIsometry (x : H →L[ℂ] H) *
      star (polarPartialIsometry (x : H →L[ℂ] H)))
    exact polarPartialIsometry_final (H := H) (x : H →L[ℂ] H)
  have hvr : star v * v = r := by
    apply Subtype.ext
    change star (polarPartialIsometry (x : H →L[ℂ] H)) * polarPartialIsometry (x : H →L[ℂ] H) =
      rangeSupport (polarModulus (x : H →L[ℂ] H))
    exact polarPartialIsometry_initial (H := H) (x : H →L[ℂ] H)
  have hqv : q * v = v := by
    apply Subtype.ext
    change (q : H →L[ℂ] H) * polarPartialIsometry (x : H →L[ℂ] H) =
      polarPartialIsometry (x : H →L[ℂ] H)
    exact leftSupport_polarPartialIsometry (H := H) (x : H →L[ℂ] H)
      (q : H →L[ℂ] H) (congrArg Subtype.val hqx)
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hvr]
    exact trace_initial_le_leftSupport τ htr v q hq hv hqv
  · apply Subtype.ext
    let X : H →L[ℂ] H := x
    change X * rangeSupport (polarModulus X) = X
    calc
      _ = (polarPartialIsometry X * polarModulus X) * rangeSupport (polarModulus X) := by
        rw [polarPartialIsometry_mul_modulus]
      _ = polarPartialIsometry X * (polarModulus X * rangeSupport (polarModulus X)) :=
        mul_assoc _ _ _
      _ = X := by rw [mul_rangeSupport _ (polarModulus_selfAdjoint X),
        polarPartialIsometry_mul_modulus]

end Tracial

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionJoinTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joins of projections and their trace bound. These elementary
support identities are used to control countable unions of small spectral
projections in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive trace is monotone in the algebraic projection order. -/
theorem trace_projection_le {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ)
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : q * p = p) : (τ p).re ≤ (τ q).re := by
  have ht := τ.map_nonneg (hp.sub_of_mul_eq_right hq h).nonneg
  rw [map_sub] at ht
  exact sub_nonneg.mp ht.1

attribute [local instance] OAI.KadisonSimilarity.joinTrace_closed
/-- The range support has trace at most that of a prescribed right support. -/
theorem trace_normalRangeSupport_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x p : M.toStarSubalgebra) (hp : IsStarProjection p) (hxp : x * p = x) :
    (τ (normalRangeSupport M x)).re ≤ (τ p).re := by
  have hpx : p * star x = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hxp
  obtain ⟨r, hr, hrt, hxr⟩ := exists_rightSupport_trace_le M τ htr p (star x) hp hpx
  have hrx : r * x = x := by
    simpa only [star_mul, star_star, hr.isSelfAdjoint.star_eq] using congrArg star hxr
  exact (trace_projection_le τ _ _ (normalRangeSupport_isStarProjection M x) hr
    (normalRangeSupport_least M x r hrx)).trans hrt

theorem projectionJoin_properties (M : VonNeumannAlgebra H)
    (p q : M.toStarSubalgebra) (hp : IsStarProjection p) (_hq : IsStarProjection q) :
    IsStarProjection (projectionJoin M p q) ∧
      projectionJoin M p q * p = p ∧ projectionJoin M p q * q = q ∧
      ∀ r : M.toStarSubalgebra, r * p = p → r * q = q →
        r * projectionJoin M p q = projectionJoin M p q := by
  let x := (1 - p) * q
  let s := normalRangeSupport M x
  have hs : IsStarProjection s := normalRangeSupport_isStarProjection M x
  have hpx : p * x = 0 := by
    dsimp [x]
    rw [← mul_assoc, mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self, zero_mul]
  have hps : p * s = 0 := by
    apply Subtype.ext
    exact mul_rangeSupport_eq_zero (x : H →L[ℂ] H) p (congrArg Subtype.val hpx)
  have hsp : s * p = 0 := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hs.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hps
  have hsx : s * x = x := normalRangeSupport_mul M x
  have hsq : s * q = x := by
    calc
      s * q = (s * (1 - p)) * q := by rw [mul_sub, mul_one, hsp, sub_zero]
      _ = s * x := mul_assoc _ _ _
      _ = x := hsx
  refine ⟨hp.add hs hps, ?_, ?_, ?_⟩
  · change (p + s) * p = p
    rw [add_mul, hp.isIdempotentElem.eq, hsp, add_zero]
  · change (p + s) * q = q
    rw [add_mul, hsq]
    dsimp [x]
    rw [sub_mul, one_mul]
    abel
  · intro r hrp hrq
    have hrx : r * x = x := by
      dsimp [x]
      rw [sub_mul, one_mul, mul_sub, ← mul_assoc, hrp, hrq]
    have hrs : r * s = s := normalRangeSupport_least M x r hrx
    change r * (p + s) = p + s
    rw [mul_add, hrp, hrs]

/-- Subadditivity of the trace for a finite projection join. -/
theorem trace_projectionJoin_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (p q : M.toStarSubalgebra) (hq : IsStarProjection q) :
    (τ (projectionJoin M p q)).re ≤ (τ p).re + (τ q).re := by
  have hright : ((1 - p) * q) * q = (1 - p) * q := by
    rw [mul_assoc, hq.isIdempotentElem.eq]
  have ht := trace_normalRangeSupport_le M τ htr ((1 - p) * q) q hq hright
  change (τ (p + normalRangeSupport M ((1 - p) * q))).re ≤ _
  rw [map_add, Complex.add_re]
  linarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableProjectionJoin
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable projection joins with the trace bound inherited from finite
unions. Only the concrete faithful vector trace is used for the limit. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finiteProjectionJoin_isStarProjection (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    IsStarProjection (finiteProjectionJoin M p n) := by
  induction n with
  | zero => exact IsStarProjection.zero _
  | succ n ih => exact (projectionJoin_properties M _ _ ih (hp n)).1

theorem finiteProjectionJoin_step (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    finiteProjectionJoin M p (n + 1) * finiteProjectionJoin M p n =
      finiteProjectionJoin M p n :=
  (projectionJoin_properties M _ _ (finiteProjectionJoin_isStarProjection M p hp n) (hp n)).2.1

theorem finiteProjectionJoin_contains (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (n i : ℕ) (hi : i < n) : finiteProjectionJoin M p n * p i = p i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · calc
        finiteProjectionJoin M p (n + 1) * p i =
            finiteProjectionJoin M p (n + 1) * (finiteProjectionJoin M p n * p i) := by rw [ih hin]
        _ = (finiteProjectionJoin M p (n + 1) * finiteProjectionJoin M p n) * p i :=
          (mul_assoc _ _ _).symm
        _ = p i := by rw [finiteProjectionJoin_step M p hp n, ih hin]
    · have he : i = n := by omega
      subst i
      exact (projectionJoin_properties M _ _ (finiteProjectionJoin_isStarProjection M p hp n)
        (hp n)).2.2.1

theorem finiteProjectionJoin_mono (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (i j : ℕ) (hij : i ≤ j) :
    finiteProjectionJoin M p j * finiteProjectionJoin M p i = finiteProjectionJoin M p i := by
  induction j, hij using Nat.le_induction with
  | base => exact (finiteProjectionJoin_isStarProjection M p hp i).isIdempotentElem.eq
  | succ j _ ih =>
    calc
      _ = finiteProjectionJoin M p (j + 1) *
          (finiteProjectionJoin M p j * finiteProjectionJoin M p i) := by rw [ih]
      _ = (finiteProjectionJoin M p (j + 1) * finiteProjectionJoin M p j) *
          finiteProjectionJoin M p i := (mul_assoc _ _ _).symm
      _ = finiteProjectionJoin M p i := by rw [finiteProjectionJoin_step M p hp j, ih]

theorem finiteProjectionJoin_least (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (r : M.toStarSubalgebra) (hr : ∀ n, r * p n = p n) (n : ℕ) :
    r * finiteProjectionJoin M p n = finiteProjectionJoin M p n := by
  induction n with
  | zero => exact mul_zero _
  | succ n ih => exact (projectionJoin_properties M _ _
      (finiteProjectionJoin_isStarProjection M p hp n) (hp n)).2.2.2 r ih (hr n)

attribute [local instance] OAI.KadisonSimilarity.countableJoin_closed
theorem trace_finiteProjectionJoin_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    (τ (finiteProjectionJoin M p n)).re ≤ ∑ i ∈ Finset.range n, (τ (p i)).re := by
  induction n with
  | zero => simp [finiteProjectionJoin]
  | succ n ih =>
    change (τ (projectionJoin M (finiteProjectionJoin M p n) (p n))).re ≤ _
    rw [Finset.sum_range_succ]
    have hj := trace_projectionJoin_le M τ htr (finiteProjectionJoin M p n) (p n) (hp n)
    linarith

/-- The join has trace bounded by every common bound on finite trace sums. -/
theorem exists_countable_projection_join (M : VonNeumannAlgebra H)
    (υ : TracialRepresentation M) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hτ : ∀ a, τ a = υ.trace a)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  have htr (a b : M.toStarSubalgebra) : τ (a * b) = τ (b * a) := by
    rw [hτ, hτ, υ.trace_mul_comm]
  let b : ℕ → AlgebraProjection M := fun n =>
    ⟨finiteProjectionJoin M p n, finiteProjectionJoin_isStarProjection M p hp n⟩
  have hb : Monotone b := fun i j hij => finiteProjectionJoin_mono M p hp i j hij
  have hbt (n : ℕ) : (υ.trace (b n).val).re ≤ C := by
    rw [← hτ]
    exact (trace_finiteProjectionJoin_le M τ htr p hp n).trans (hC n)
  obtain ⟨q, hq, hqt, hleast⟩ := monotone_projection_upper_bound υ b hb C hbt
  refine ⟨q.val, q.property, ?_, ?_, ?_⟩
  · rwa [hτ]
  · intro n
    have hbn := finiteProjectionJoin_contains M p hp (n + 1) n (Nat.lt_succ_self n)
    calc
      q.val * p n = q.val * ((b (n + 1)).val * p n) := by rw [hbn]
      _ = (q.val * (b (n + 1)).val) * p n := (mul_assoc _ _ _).symm
      _ = p n := by rw [hq (n + 1), hbn]
  · intro r hr hrp
    exact hleast ⟨r, hr⟩ (fun n => finiteProjectionJoin_least M p hp r hrp n)

/-- The countable trace bound transports through a star isomorphism. Only
the target trace needs to be presented by a concrete vector. -/
theorem exists_countable_projection_join_of_equiv_oai
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  obtain ⟨q, hq, hqt, hqp, hleast⟩ := exists_countable_projection_join N υ σ hσ
    (fun n => e (p n)) (fun n => (hp n).map e.toStarAlgHom) C (by simpa only [he] using hC)
  have heq : e (e.symm q) = q := e.apply_symm_apply q
  refine ⟨e.symm q, hq.map e.symm.toStarAlgHom, ?_, ?_, ?_⟩
  · have h := he (e.symm q)
    rw [heq] at h
    rwa [← h]
  · intro n
    apply e.injective
    calc
      e (e.symm q * p n) = e (e.symm q) * e (p n) := e.map_mul' _ _
      _ = q * e (p n) := congrArg (fun b => b * e (p n)) heq
      _ = e (p n) := hqp n
  · intro r hr hrp
    have hu (n : ℕ) : e r * e (p n) = e (p n) :=
      (e.map_mul' r (p n)).symm.trans (congrArg e (hrp n))
    have h := hleast (e r) (hr.map e.toStarAlgHom) hu
    apply e.injective
    calc
      e (r * e.symm q) = e r * e (e.symm q) := e.map_mul' _ _
      _ = e r * q := congrArg (fun b => e r * b) heq
      _ = q := h
      _ = e (e.symm q) := heq.symm

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv_oai.{u_1, u_2} := @OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv_oai.{u_1, u_2}
