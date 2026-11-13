-- Prove2me | solution 1 for OAI.KadisonKastler.exists_simple_spatial_derivation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:47:35.105437+00:00
-- url     : https://prove2.me/submissions/c54065e2-39a2-4104-8627-a7d3998b2df6

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A018
import Definitions.Def_Q260K003
import Definitions.Def_Q260K007
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_factorization_of_complete_bound
import Theorems.Thm_OAI_KadisonSimilarity_cyclic_derivation_implementation_of_column_tests

section
-- module Solutions.OAIQ075_KS.TracialSplitting_FullProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section SmallFullSupport

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma simple_starAlgHom_injective [Nontrivial D] (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) : Function.Injective ι := by
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))).continuous
  have hc : IsClosed (TwoSidedIdeal.ker ι : Set A) := by
    have he : (TwoSidedIdeal.ker ι : Set A) = {a : A | ι a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker ι
    rw [he]
    exact isClosed_eq hι continuous_const
  rcases hsimple (TwoSidedIdeal.ker ι) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot ι).mp hb
  · have : (1 : A) ∈ TwoSidedIdeal.ker ι := by rw [ht]; exact Set.mem_univ _
    have hz := (TwoSidedIdeal.mem_ker ι).mp this
    simp at hz

end SmallFullSupport

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.peakingExpectation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f)) := by
  simp only [gns_apply_vector]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

theorem gnsVector_norm_eq_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖gnsVector f‖ = 1 := by
  have hs := gnsVector_norm_sq f
  rw [hf, Complex.one_re] at hs
  nlinarith [norm_nonneg (gnsVector f)]

theorem state_map_star (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) :
    f (star a) = star (f a) := map_star (positiveOfSquares f hf.2) a

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem invariant_orthogonal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H)
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) :
    ∀ a : A, ∀ x ∈ Mᗮ, π a x ∈ Mᗮ := by
  intro a x hx y hy
  have hz := hx (π (star a) y) (hM (star a) y hy)
  rw [map_star] at hz
  exact (ContinuousLinearMap.adjoint_inner_left (π a) x y).symm.trans hz

theorem invariant_starProjection_commute (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M) (a : A) (x : H) :
    M.starProjection (π a x) = π a (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hM a _ (M.starProjection_apply_mem x)
  · rw [← map_sub]
    exact invariant_orthogonal π M hM a _ (M.sub_starProjection_mem_orthogonal x)

theorem vectorFunctional_add_reducing (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (x y : H) (hx : x ∈ M) (hy : y ∈ Mᗮ) :
    vectorFunctional π (x + y) = vectorFunctional π x + vectorFunctional π y := by
  ext a
  simp only [vectorFunctional_apply, map_add, inner_add_left, inner_add_right, add_apply]
  have hxy : ⟪x, π a y⟫_ℂ = 0 := invariant_orthogonal π M hM a y hy x hx
  have hyx : ⟪y, π a x⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    simp only [hy _ (hM a x hx), map_zero]
  rw [hxy, hyx]
  simp only [add_zero, zero_add]

variable [PartialOrder A] [StarOrderedRing A]

theorem normalized_vector_isState (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : x ≠ 0) :
    IsState ((‖x‖ ^ 2)⁻¹ • vectorFunctional π x) := by
  apply (isState_iff _).mpr
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  constructor
  · rw [smul_apply, vectorFunctional_one π hone, ← Complex.ofReal_pow]
    change (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 hn), Complex.ofReal_one]
  · intro a
    rw [smul_apply, vectorFunctional_square]
    simp only [Complex.smul_im, Complex.smul_re, ← Complex.ofReal_pow,
      Complex.ofReal_im, Complex.ofReal_re, smul_eq_mul, mul_zero, true_and]
    positivity

omit [PartialOrder A] [StarOrderedRing A] in

theorem cyclic_closed_invariant_top (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a : A => π a ξ)) (M : Submodule ℂ H)
    (hclosed : IsClosed (M : Set H)) (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (hξ : ξ ∈ M) : M = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  apply closure_minimal (s := Set.range (fun a : A => π a ξ)) _ hclosed (hcyc x)
  rintro y ⟨a, rfl⟩
  exact hinv a ξ hξ

theorem pure_cyclic_irreducible (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (hcyc : DenseRange (fun a : A => π a ξ))
    (hpure : IsPureState (vectorFunctional π ξ)) : IsIrreducible π := by
  refine ⟨?_, ?_⟩
  · intro hz
    have h : ξ = 0 := by
      calc
        ξ = π 1 ξ := by rw [hone]; rfl
        _ = 0 := by rw [hz]; rfl
    simp [h] at hξ
  · intro M hclosed hinv
    let : IsClosed (M : Set H) := hclosed
    let u := M.starProjection ξ
    let v := ξ - u
    have huM : u ∈ M := M.starProjection_apply_mem ξ
    have hvM : v ∈ Mᗮ := M.sub_starProjection_mem_orthogonal ξ
    by_cases hu : u = 0
    · left
      apply M.orthogonal_eq_top_iff.mp
      apply cyclic_closed_invariant_top π ξ hcyc Mᗮ M.isClosed_orthogonal
        (invariant_orthogonal π M hinv)
      simpa only [v, hu, sub_zero] using hvM
    by_cases hv : v = 0
    · right
      apply cyclic_closed_invariant_top π ξ hcyc M hclosed hinv
      have h : ξ = u := sub_eq_zero.mp hv
      rwa [h]
    have ha : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hb : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hab : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := by
      have h := Submodule.norm_sq_eq_add_norm_sq_starProjection ξ M
      rw [hξ, one_pow, Submodule.starProjection_orthogonal_val] at h
      exact h.symm
    have huv : u + v = ξ := by dsimp [v]; abel
    have hseg : vectorFunctional π ξ ∈ openSegment ℝ
        ((‖u‖ ^ 2)⁻¹ • vectorFunctional π u)
        ((‖v‖ ^ 2)⁻¹ • vectorFunctional π v) := by
      refine ⟨‖u‖ ^ 2, ‖v‖ ^ 2, ha, hb, hab, ?_⟩
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt ha),
        mul_inv_cancel₀ (ne_of_gt hb), one_smul, one_smul]
      rw [← vectorFunctional_add_reducing π M hinv u v huM hvM, huv]
    have huf : (‖u‖ ^ 2)⁻¹ • vectorFunctional π u = vectorFunctional π ξ :=
      (((mem_extremePoints.mp hpure).2 _ (normalized_vector_isState π hone u hu)
        _ (normalized_vector_isState π hone v hv) hseg).1)
    have hgu : vectorFunctional π u = ‖u‖ ^ 2 • vectorFunctional π ξ := by
      rw [← huf, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    have hPu : M.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr huM
    have coeff (a : A) : ⟪u, π a ξ⟫_ℂ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := by
      calc
        ⟪u, π a ξ⟫_ℂ = ⟪u, M.starProjection (π a ξ)⟫_ℂ := by
          rw [← M.inner_starProjection_left_eq_right, hPu]
        _ = vectorFunctional π u a := by
          rw [invariant_starProjection_commute π M hinv]
          rfl
        _ = (‖u‖ ^ 2) • ⟪ξ, π a ξ⟫_ℂ := by rw [hgu]; rfl
        _ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := (inner_smul_left_eq_smul _ _ _).symm
    have hscalar : u = (‖u‖ ^ 2) • ξ := by
      apply ext_inner_right ℂ
      have h := hcyc.equalizer
        (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
        (funext coeff)
      exact congrFun h
    have hscale : (‖u‖ ^ 2 : ℝ) • u = u := by
      calc
        (‖u‖ ^ 2 : ℝ) • u = M.starProjection ((‖u‖ ^ 2 : ℝ) • ξ) := by
          exact ((M.starProjection.restrictScalars ℝ).map_smul (‖u‖ ^ 2) ξ).symm
        _ = M.starProjection u := by rw [← hscalar]
        _ = u := hPu
    have hnorm := congrArg norm hscale
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
    have hn := norm_pos_iff.mpr hu
    exfalso
    have h1 : ‖u‖ ^ 2 = 1 := by nlinarith
    linarith

theorem pure_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f) (hfp : IsPureState f) :
    IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom := by
  let g := positiveOfSquares f hf.2
  have hone : g 1 = 1 := ((isState_iff f).mp hf).1
  have hcoeff : vectorFunctional g.gnsNonUnitalStarAlgHom (gnsVector g) = f := by
    ext a
    exact gnsVector_coefficient g a
  apply pure_cyclic_irreducible g.gnsNonUnitalStarAlgHom
    (show g.gnsStarAlgHom 1 = 1 from map_one _) (gnsVector g)
    (gnsVector_norm_eq_one g hone) (gnsVector_cyclic g)
  rwa [hcoeff]

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_States
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_state_extension_subalgebra
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (f : S →L[ℂ] ℂ) (hf : IsState f) :
    ∃ F : A →L[ℂ] ℂ, IsState F ∧ ∀ a : S, F (a : A) = f a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let g : selfAdjointSubspace S →L[ℝ] ℝ :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp (selfAdjointSubspaceInclusion S))
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (selfAdjointSubspaceInclusion S a)).re‖ ≤ 1 * ‖a‖
    calc
      _ ≤ ‖f (selfAdjointSubspaceInclusion S a)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ ‖selfAdjointSubspaceInclusion S a‖ := state_norm_apply_le f hf _
      _ = 1 * ‖a‖ := by simp [selfAdjointSubspaceInclusion]; rfl
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (selfAdjointSubspace S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖G₀‖ * ‖sa a‖ := G₀.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg _)
  have hG1 : G 1 = 1 := by
    let e : selfAdjointSubspace S := ⟨1, S.one_mem, IsSelfAdjoint.one A⟩
    have he := hG₀ e
    change G 1 = (f 1).re at he
    simpa only [(isState_iff f).mp hf |>.1, Complex.one_re] using he
  let F := positiveCLM (selfAdjointPositive G hGn hG1)
  have hF : IsState F := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1, fun a => ?_⟩
    exact ⟨((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).2.symm,
      ((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).1⟩
  refine ⟨F, hF, ?_⟩
  have hs (a : S) (ha : IsSelfAdjoint a) : F (a : A) = f a := by
    let b : selfAdjointSubspace S := ⟨(a : A), a.property, by
      change star (a : A) = (a : A)
      exact congrArg Subtype.val ha.star_eq⟩
    let bsa : selfAdjoint A := ⟨(a : A), b.property.2⟩
    have hfb : (f a).im = 0 := by
      have hh := state_map_star f hf a
      rw [ha.star_eq] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    change selfAdjointPositive G hGn hG1 (bsa : A) = f a
    rw [selfAdjointPositive_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    exact Complex.ext (by simp) (by simpa using hfb.symm)
  intro a
  have hdecomp := realPart_add_I_smul_imaginaryPart a
  rw [← hdecomp]
  change F (((realPart a : S) : A) + Complex.I • ((imaginaryPart a : S) : A)) = _
  simp only [map_add, map_smul]
  rw [hs _ (realPart a).property, hs _ (imaginaryPart a).property]

omit [PartialOrder A] [StarOrderedRing A] in

theorem character_isState (φ : WeakDual.characterSpace ℂ A) :
    IsState (WeakDual.toStrongDual (φ : WeakDual ℂ A)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  apply (isState_iff _).mpr
  refine ⟨map_one φ, fun a => ?_⟩
  change (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re
  rw [map_mul, map_star]
  have h := star_mul_self_nonneg (φ a)
  exact ⟨h.2.symm, h.1⟩

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_norming_state [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ‖f a‖ = ‖a‖ := by
  let S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ a
  let b : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨z, hz, hnz⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) b).1
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨f, hf, hrest⟩ := exists_state_extension_subalgebra S
    (WeakDual.toStrongDual (φ : WeakDual ℂ S)) (character_isState φ)
  refine ⟨f, hf, ?_⟩
  change ‖f (b : A)‖ = ‖b‖
  rw [hrest b]
  change ‖φ b‖ = ‖b‖
  rw [hφ]
  exact hnz

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimpleIrreducibleRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful irreducible representation for Sakai's construction

Compactness of the state space gives a pure state. Its GNS representation
is irreducible, and simplicity makes the representation faithful. These
steps use the existing state-space and GNS proofs, with no representation
existence hypothesis.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_pure_state :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ IsPureState f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (A →L[ℂ] ℂ))
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    (WeakDual.withSeminorms ℂ A).toLocallyConvexSpace
  obtain ⟨f, hf, _⟩ := exists_norming_state (1 : A)
  have hne : (weakStates A).Nonempty := ⟨StrongDual.toWeakDual f, hf⟩
  obtain ⟨g, hg⟩ := isCompact_weakStates.extremePoints_nonempty hne
  exact ⟨g.toStrongDual, hg.1, hg⟩

theorem exists_simple_irreducible_representation (hA : CStarSimple A) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ ξ : H, ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨f, hf, hpure⟩ := exists_pure_state (A := A)
  let g := positiveOfSquares f hf.2
  have h1 : g 1 = 1 := ((isState_iff f).mp hf).1
  have hn : ‖gnsVector g‖ = 1 := gnsVector_norm_eq_one g h1
  let : Nontrivial g.GNS := ⟨⟨gnsVector g, 0, by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn⟩⟩
  refine ⟨g.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    g.gnsStarAlgHom, ?_, pure_gns_irreducible f hf hpure,
    gnsVector g, hn, gnsVector_cyclic g⟩
  exact CurrentMain.simple_starAlgHom_injective hA g.gnsStarAlgHom

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.KadisonSimilarity.sumColumns_adjoint_apply _root_.OAI.KadisonSimilarity.sumColumns_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete matrix norms and complete boundedness

The matrix norm used here is `CStarMatrix`'s C-star norm. The representation
on finite Hilbert sums is shown to preserve that norm, connecting the concrete
commutator estimate with the usual notion of complete boundedness.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every entry can be recovered by evaluating on a vector in one coordinate. -/
theorem operatorMatrixRepresentation_injective (n : ℕ) :
    Function.Injective (operatorMatrixRepresentation (H := H) n) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  ext ξ
  have he := congrArg
    (fun T : HilbertCopies H n →L[ℂ] HilbertCopies H n => T (PiLp.single 2 j ξ) i) h
  simpa [operatorMatrixRepresentation, matrixOperator, PiLp.single_apply, apply_ite] using he

/-- The normed matrix action remains injective after the type synonym is changed. -/
theorem matrixRepresentation_injective (n : ℕ) :
    Function.Injective (matrixRepresentation (H := H) n) :=
  (operatorMatrixRepresentation_injective n).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.injective

/-- The abstract C-star matrix norm equals the concrete Hilbert-space operator norm. -/
theorem norm_matrixOperator_eq (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖matrixOperator (CStarMatrix.ofMatrix.symm X)‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixRepresentation n)
    (matrixRepresentation_injective n) X

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section NativeMatrixNorm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_cstarMatrix_conjTranspose_le {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  have hi := CStarMatrix.inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v)
  have hn := congrArg norm hi
  calc
    _ = ‖inner A (CStarMatrix.toCLM M w) v‖ := hn
    _ ≤ ‖CStarMatrix.toCLM M w‖ * ‖v‖ := CStarModule.norm_inner_le _
    _ ≤ (‖M‖ * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      ((CStarMatrix.toCLM M).le_opNorm w) (norm_nonneg v)
    _ = (‖M‖₊ : ℝ) * ‖v‖ * ‖w‖ := by simp only [coe_nnnorm] <;> ring

/-- Rectangular conjugate transpose preserves the native C-star matrix norm. -/
theorem norm_cstarMatrix_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (norm_cstarMatrix_conjTranspose_le M)
  have hMM : M.conjTranspose.conjTranspose = M := by
    ext i j
    simp [CStarMatrix.conjTranspose_apply]
  simpa only [hMM] using norm_cstarMatrix_conjTranspose_le M.conjTranspose

end NativeMatrixNorm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RegularizedPolarFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem positiveShiftReciprocal_continuous (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ h) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε)

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_selfAdjoint (h : A) (ε : ℝ) :
    IsSelfAdjoint (positiveShiftReciprocal h ε) := cfc_predicate _ h

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_commute (h : A) (ε : ℝ) :
    Commute (positiveShiftReciprocal h ε) h := (Commute.refl h).cfc_real _

theorem positiveShiftReciprocal_inverse (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (h + ε • (1 : A)) * positiveShiftReciprocal h ε = 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  have hid : cfc (fun t : ℝ => t + ε) h = h + ε • (1 : A) := by
    rw [cfc_add h (fun t : ℝ => t) (fun _ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh.isSelfAdjoint, cfc_const ε h hh.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [positiveShiftReciprocal, ← hid, ← cfc_mul _ _ h (by fun_prop) hc]
  calc
    cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) h = cfc (fun _ : ℝ => 1) h := by
      apply cfc_congr
      intro t ht
      exact mul_inv_cancel₀ (ne_of_gt
        (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε))
    _ = 1 := cfc_const_one ℝ h hh.isSelfAdjoint

theorem positiveShiftReciprocal_mul_norm_le (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ‖h * positiveShiftReciprocal h ε‖ ≤ 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  change ‖h * cfc (fun t : ℝ => (t + ε)⁻¹) h‖ ≤ 1
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ h hh.isSelfAdjoint]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) h continuousOn_id hc]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hh ht
  have hp : 0 < t + ε := add_pos_of_nonneg_of_pos ht0 hε
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
  change t / (t + ε) ≤ 1
  exact (div_le_one hp).mpr (by linarith)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnPolar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive regularized polar columns inside the source algebra. These
columns will supply dense cyclic vector tests with a varying unit vector. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder WithCStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A column is contractive when its positive column square is contractive. -/
theorem norm_column_le_of_starSquare {n : ℕ} (a : Fin n → A)
    (ha : ‖∑ i, star (a i) * a i‖ ≤ 1) :
    ‖CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)‖ ≤ 1 := by
  let M := CStarMatrix.ofMatrix (fun i (_ : Fin 1) => a i)
  rw [← norm_cstarMatrix_conjTranspose M]
  change ‖CStarMatrix.toCLM M.conjTranspose‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hv : ‖v (0 : Fin 1)‖ ≤ ‖v‖ := WithCStarModule.norm_apply_le_norm _ _
  have hi : inner A (CStarMatrix.toCLM M.conjTranspose v)
      (CStarMatrix.toCLM M.conjTranspose v) =
      v 0 * (∑ i, star (a i) * a i) * star (v 0) := by
    rw [CStarMatrix.toCLM_apply_eq_sum]
    change (∑ i : Fin n, (∑ j : Fin 1, v j * star (a i)) *
      star (∑ j : Fin 1, v j * star (a i))) = _
    simp only [Fin.sum_univ_one, star_mul, star_star, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
  have hn : ‖CStarMatrix.toCLM M.conjTranspose v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    calc
      _ = ‖v 0 * (∑ i, star (a i) * a i) * star (v 0)‖ := by
        rw [CStarModule.norm_sq_eq A, hi]
      _ ≤ (‖v 0‖ * ‖∑ i, star (a i) * a i‖) * ‖v 0‖ :=
        (norm_mul_le _ _).trans (by
          rw [norm_star]
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖v‖ * 1) * ‖v‖ := by gcongr
      _ = ‖v‖ ^ 2 := by ring
  simpa only [one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg v)).mp hn

theorem cyclicColumnRoot_nonneg {n : ℕ} (a : Fin n → A) : 0 ≤ cyclicColumnRoot a :=
  CFC.sqrt_nonneg _

theorem cyclicColumnRoot_sq {n : ℕ} (a : Fin n → A) :
    cyclicColumnRoot a * cyclicColumnRoot a = ∑ i, star (a i) * a i :=
  CFC.sqrt_mul_sqrt_self _ (Finset.sum_nonneg fun _ _ => star_mul_self_nonneg _)

theorem cyclicPolarColumn_contract {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    ‖CStarMatrix.ofMatrix (cyclicPolarColumn a ε)‖ ≤ 1 := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hstar : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (∑ i, star (a i * r) * (a i * r)) = (h * r) * (h * r) := by
    calc
      _ = r * (∑ i, star (a i) * a i) * r := by
        simp only [star_mul, hstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = r * (h * h) * r := by rw [← cyclicColumnRoot_sq a]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  apply norm_column_le_of_starSquare
  change ‖∑ i, star (a i * r) * (a i * r)‖ ≤ 1
  rw [he]
  have hn := positiveShiftReciprocal_mul_norm_le h (cyclicColumnRoot_nonneg a) hε
  exact (norm_mul_le _ _).trans <| (mul_le_mul hn hn (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- Multiplication by the shifted root recovers every original column entry. -/
theorem cyclicPolarColumn_recover {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε)
    (i : Fin n) : cyclicPolarColumn a ε i 0 * (cyclicColumnRoot a + ε • (1 : A)) = a i := by
  let h := cyclicColumnRoot a
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hi := congrArg star (positiveShiftReciprocal_inverse h (cyclicColumnRoot_nonneg a) hε)
  have hrev : r * (h + ε • (1 : A)) = 1 := by
    simp only [star_mul, star_add, star_smul, star_trivial, star_one] at hi
    change star r * (star h + ε • (1 : A)) = 1 at hi
    have hh : star h = h := (cyclicColumnRoot_nonneg a).star_eq
    rwa [hr, hh] at hi
  change (a i * r) * (h + ε • (1 : A)) = a i
  rw [mul_assoc, hrev, mul_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyEmbedding_toContinuousLinearMap _root_.OAI.KadisonSimilarity.copyRestriction_apply _root_.OAI.KadisonSimilarity.copyRestriction_copyEmbedding _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_id_eq _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.norm_copyEmbeddingMap _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense cyclic orbits give the bounded column tests needed for the
matrix derivation estimate. The unit vector may vary with the test. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A finite orbit column and its positive square root have the same vector norm. -/
theorem norm_cyclicColumnRoot_action (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) :
    ‖σ (cyclicColumnRoot a) Ω‖ = ‖cyclicOrbitColumn σ Ω a‖ := by
  have hsa : (σ (cyclicColumnRoot a)).adjoint = σ (cyclicColumnRoot a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      (cyclicColumnRoot_nonneg a).star_eq]
  have hsq : (σ (cyclicColumnRoot a)).adjoint.comp (σ (cyclicColumnRoot a)) =
      ∑ i, (σ (a i)).adjoint.comp (σ (a i)) := by
    rw [hsa]
    change σ (cyclicColumnRoot a) * σ (cyclicColumnRoot a) = _
    rw [← map_mul, cyclicColumnRoot_sq, map_sum]
    simp only [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  have hi := congrArg (fun T : K →L[ℂ] K => (inner ℂ Ω (T Ω)).re) hsq
  simp only [ContinuousLinearMap.comp_apply, sum_apply, inner_sum,
    ContinuousLinearMap.adjoint_inner_right] at hi
  have hre (f : Fin n → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reLm f Finset.univ
  have hself (x : K) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hre, hself] at hi
  simp_rw [hself] at hi
  have hv := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => K) (cyclicOrbitColumn σ Ω a)
  simp only [cyclicOrbitColumn_apply] at hv
  nlinarith [norm_nonneg (σ (cyclicColumnRoot a) Ω), norm_nonneg (cyclicOrbitColumn σ Ω a)]

theorem cyclicShiftVector_norm_le (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖cyclicShiftVector σ Ω a ε‖ ≤ ‖cyclicOrbitColumn σ Ω a‖ + ε * ‖Ω‖ := by
  have he : cyclicShiftVector σ Ω a ε = σ (cyclicColumnRoot a) Ω + ε • Ω := by
    change σ (cyclicColumnRoot a + ε • (1 : A)) Ω = _
    have hs : σ (ε • (1 : A)) = ε • σ 1 :=
      σ.toLinearMap.map_smul_of_tower ε (1 : A)
    rw [map_add, hs, map_one]
    rfl
  rw [he, ← norm_cyclicColumnRoot_action σ Ω a]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_of_nonneg hε])

theorem cyclicPolarColumn_action_recover (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    columnAction σ (cyclicPolarColumn a ε) (cyclicShiftVector σ Ω a ε) =
      cyclicOrbitColumn σ Ω a := by
  apply PiLp.ext
  intro i
  rw [columnAction_apply, cyclicShiftVector, cyclicOrbitColumn_apply]
  change ((σ (cyclicPolarColumn a ε i 0) * σ (cyclicColumnRoot a + ε • (1 : A))) Ω) = _
  rw [← map_mul, cyclicPolarColumn_recover a hε i]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Cyclicity supplies simultaneous approximation in every finite Hilbert sum. -/
theorem cyclicOrbitColumn_dense (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) (n : ℕ) :
    DenseRange (cyclicOrbitColumn (n := n) σ Ω) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm
  have hpi : DenseRange (Pi.map (fun _ : Fin n => fun a : A => σ a Ω)) :=
    DenseRange.piMap (fun _ => hΩ)
  exact e.surjective.denseRange.comp hpi e.continuous

/-- A dense cyclic orbit gives all the required bounded column tests. -/
theorem cyclicColumnTests_of_dense_orbit (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) : CyclicColumnTests σ := by
  intro n ξ hξ η hη
  let δ := min η (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  obtain ⟨a, ha⟩ := (cyclicOrbitColumn_dense σ Ω hΩ n).exists_dist_lt ξ hδ
  rw [dist_eq_norm, norm_sub_rev] at ha
  let c := cyclicOrbitColumn σ Ω a
  have hc : ‖c - ξ‖ < δ := ha
  have hcn : ‖c‖ < 1 + δ := by
    have h := norm_le_norm_sub_add c ξ
    rw [hξ] at h
    linarith
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_sub, norm_neg, hξ] at hc
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    linarith
  let ε := (1 / 4 : ℝ) / (‖Ω‖ + 1)
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  have he : ε * (‖Ω‖ + 1) = 1 / 4 := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hεΩ : ε * ‖Ω‖ ≤ 1 / 4 := by nlinarith [norm_nonneg Ω]
  let z := cyclicShiftVector σ Ω a ε
  let P : Matrix (Fin n) (Fin 1) A := cyclicPolarColumn a ε
  have hrec : columnAction σ P z = c := cyclicPolarColumn_action_recover σ Ω a hε
  have hzn : ‖z‖ ≤ 2 := by
    have h := cyclicShiftVector_norm_le σ Ω a hε.le
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    change ‖z‖ ≤ ‖c‖ + ε * ‖Ω‖ at h
    linarith
  have hz0 : z ≠ 0 := by
    intro hz
    apply hc0
    rw [← hrec, hz]
    apply PiLp.ext
    intro i
    simp only [columnAction_apply, map_zero, PiLp.zero_apply]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let ζ := (‖z‖ : ℂ)⁻¹ • z
  let W : Matrix (Fin n) (Fin 1) A := (‖z‖ : ℂ) • P
  refine ⟨ζ, W, ?_, ?_, ?_⟩
  · change ‖(‖z‖ : ℂ)⁻¹ • z‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hnz]
  · change ‖(‖z‖ : ℂ) • CStarMatrix.ofMatrix P‖ ≤ 2
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_of_le_one_right (norm_nonneg z) (cyclicPolarColumn_contract a hε)).trans hzn
  · have hv : columnAction σ W ζ = c := by
      apply PiLp.ext
      intro i
      rw [columnAction_apply]
      change σ ((‖z‖ : ℂ) • P i 0) ((‖z‖ : ℂ)⁻¹ • z) = c i
      have hscalar : σ ((‖z‖ : ℂ) • P i 0) = (‖z‖ : ℂ) • σ (P i 0) :=
        map_smul σ _ _
      rw [hscalar, smul_apply, map_smul, smul_smul,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnz), one_smul]
      simpa only [columnAction_apply] using
        congrArg (fun x : HilbertCopies K n => x i) hrec
    rw [hv]
    exact hc.trans_le (min_le_left _ _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative positive metric from an invertible star intertwiner

This is the final geometric step of Paulsen's theorem. The intertwiner may
map to a different Hilbert space. Its positive metric on the original space
and its positive square root yield the actual similarity unit, with exactly
the product of the forward and inverse operator norms.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The square of any bounded star intertwiner is a metric for the original
homomorphism, without an invertibility assumption. -/
theorem intertwiner_metric_identity (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) (a : A) :
    (W.adjoint.comp W).comp (π.1 (star a)) =
      (π.1 a).adjoint.comp (W.adjoint.comp W) := by
  have hadj : (π.1 a).adjoint.comp W.adjoint = W.adjoint.comp (σ (star a)) := by
    simpa only [adjoint_comp, map_star, star_eq_adjoint] using
      congrArg ContinuousLinearMap.adjoint (hW a)
  calc
    (W.adjoint.comp W).comp (π.1 (star a)) =
        W.adjoint.comp (W.comp (π.1 (star a))) := comp_assoc _ _ _
    _ = W.adjoint.comp ((σ (star a)).comp W) := by rw [hW]
    _ = (W.adjoint.comp (σ (star a))).comp W := (comp_assoc _ _ _).symm
    _ = ((π.1 a).adjoint.comp W.adjoint).comp W := by rw [← hadj]
    _ = (π.1 a).adjoint.comp (W.adjoint.comp W) := comp_assoc _ _ _

/-- The metric is positive because it is an adjoint square. -/
theorem intertwinerMetric_nonneg (W : H →L[ℂ] K) : 0 ≤ W.adjoint.comp W := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self W)

/-- A square root of the positive metric preserves both operator norms
needed for the sharp similarity estimate. -/
theorem exists_positive_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      0 ≤ (S : H →L[ℂ] H) ∧
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  let Q := intertwinerMetricUnit W L hLW hWL
  have hQ : 0 ≤ (Q : H →L[ℂ] H) := intertwinerMetric_nonneg W
  have hu : IsUnit (CFC.sqrt (Q : H →L[ℂ] H)) :=
    (CFC.isUnit_sqrt_iff _ hQ).mpr Q.isUnit
  obtain ⟨S, hS⟩ := hu
  have hSstar : star (S : H →L[ℂ] H) = (S : H →L[ℂ] H) := by
    rw [hS]
    exact (CFC.sqrt_nonneg _).star_eq
  have hSq : (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = (Q : H →L[ℂ] H) := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self _ hQ
  have hmetric : star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) =
      W.adjoint.comp W := by rw [hSstar, hSq]; rfl
  have hnorm : ‖(S : H →L[ℂ] H)‖ = ‖W‖ := by
    have h := CStarRing.norm_star_mul_self (x := (S : H →L[ℂ] H))
    rw [hmetric, norm_adjoint_comp_self] at h
    nlinarith [norm_nonneg (S : H →L[ℂ] H), norm_nonneg W]
  have hunit : S * S = Q := Units.ext hSq
  have hinvSq : (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) =
      L.comp L.adjoint := by
    have h := congrArg (fun U : (H →L[ℂ] H)ˣ => (↑U⁻¹ : H →L[ℂ] H)) hunit
    calc
      (↑S⁻¹ : H →L[ℂ] H) * (↑S⁻¹ : H →L[ℂ] H) = ↑((S * S)⁻¹) := by
        simp only [mul_inv_rev, Units.val_mul]
      _ = (↑Q⁻¹ : H →L[ℂ] H) := h
      _ = L.comp L.adjoint := rfl
  have hSstarU : star S = S := Units.ext hSstar
  have hinvstar : star (↑S⁻¹ : H →L[ℂ] H) = (↑S⁻¹ : H →L[ℂ] H) := by
    rw [← Units.coe_star, star_inv, hSstarU]
  have hinvnorm : ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
    have h := CStarRing.norm_star_mul_self (x := (↑S⁻¹ : H →L[ℂ] H))
    rw [hinvstar, hinvSq] at h
    have hLL := norm_adjoint_comp_self L.adjoint
    rw [adjoint_adjoint, adjoint.norm_map] at hLL
    rw [hLL] at h
    nlinarith [norm_nonneg (↑S⁻¹ : H →L[ℂ] H), norm_nonneg L]
  exact ⟨S, by rw [hS]; exact CFC.sqrt_nonneg _, hmetric, hnorm, hinvnorm⟩

/-- The positive metric construction gives an invertible star intertwiner. -/
theorem exists_sqrt_metric_unit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) :
    ∃ S : (H →L[ℂ] H)ˣ,
      star (S : H →L[ℂ] H) * (S : H →L[ℂ] H) = W.adjoint.comp W ∧
      ‖(S : H →L[ℂ] H)‖ = ‖W‖ ∧ ‖(↑S⁻¹ : H →L[ℂ] H)‖ = ‖L‖ := by
  obtain ⟨S, _, hS⟩ := exists_positive_sqrt_metric_unit W L hLW hWL
  exact ⟨S, hS⟩

/-- An invertible bounded intertwiner into a star representation supplies
similarity on the original space with its exact condition-number bound. -/
theorem quantitative_similarity_of_intertwiner (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1)
    (hW : ∀ a, W.comp (π.1 a) = (σ a).comp W) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  obtain ⟨S, hmetric, hnorm, hinvnorm⟩ := exists_sqrt_metric_unit W L hLW hWL
  refine ⟨S, by rw [hnorm, hinvnorm], ?_⟩
  intro a
  have h := intertwiner_metric_identity π σ W hW a
  change (W.adjoint.comp W) * π.1 (star a) = star (π.1 a) * (W.adjoint.comp W) at h
  rw [← hmetric] at h
  have he := congrArg (fun X : H →L[ℂ] H =>
    star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) h
  simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
    Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
    Units.mul_inv_cancel_left, mul_one, one_mul] using he

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reducing space generated by a homomorphism factorization

Only the vectors generated by the right factor are needed. Multiplicativity
makes the left factor an intertwiner on this closed span. Its kernel is then
a reducing subspace, which is the geometric input to invertible similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem right_mem_factorizationSpace (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (x : H) : W x ∈ factorizationSpace σ W := by
  apply (Submodule.span ℂ _).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨(1, x), by simp⟩

/-- The generating space is invariant under the whole star representation. -/
theorem factorizationSpace_invariant (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (a : A) (x : K) (hx : x ∈ factorizationSpace σ W) :
    σ a x ∈ factorizationSpace σ W := by
  let N := Submodule.span ℂ (Set.range fun p : A × H => σ p.1 (W p.2))
  have hi : N ≤ N.comap (σ a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, y⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨(a * b, y), by simp only [map_mul, mul_apply_eq_comp]; rfl⟩
  have hm : Set.MapsTo (σ a) (N : Set K) (N : Set K) := fun _ hy => hi hy
  exact hm.closure (σ a).continuous hx

/-- The left factor intertwines on the closed cyclic span, by continuity
from the algebraic generators and multiplicativity of the homomorphism. -/
theorem left_intertwines_factorizationSpace (π : BoundedUnitalHom A H)
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hf : ∀ a, L.comp ((σ a).comp W) = π.1 a)
    (a : A) (x : K) (hx : x ∈ factorizationSpace σ W) :
    L (σ a x) = π.1 a (L x) := by
  let D := L.comp (σ a) - (π.1 a).comp L
  have hs : Submodule.span ℂ (Set.range fun p : A × H => σ p.1 (W p.2)) ≤
      D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, y⟩, rfl⟩
    change L (σ a (σ b (W y))) - π.1 a (L (σ b (W y))) = 0
    have hab := congrArg (fun T : H →L[ℂ] H => T y) (hf (a * b))
    have hb := congrArg (fun T : H →L[ℂ] H => T y) (hf b)
    simp only [map_mul, comp_apply, mul_apply_eq_comp] at hab hb
    rw [hab, hb]
    exact sub_self _
  have hc : closure (Submodule.span ℂ
      (Set.range fun p : A × H => σ p.1 (W p.2)) : Set K) ⊆ (D.ker : Set K) :=
    closure_minimal hs D.isClosed_ker
  exact sub_eq_zero.mp (hc hx)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the kernel of a star intertwiner

A surjective intertwiner with a bounded right inverse restricts to an
isomorphism on the orthogonal complement of its kernel. Orthogonal
projection does not increase the right-inverse norm, which retains the
sharp bound needed for quantitative similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded right inverse of a surjective star intertwiner gives
similarity with no increase in the product of its two norms. -/
theorem quantitative_similarity_of_surjective_intertwiner
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H) (hLW : L.comp W = 1)
    (hL : ∀ a, L.comp (σ a) = (π.1 a).comp L) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let N : ClosedSubmodule ℂ K := ⟨L.ker, L.isClosed_ker⟩
  let : CompleteSpace N.toSubmodule := N.isClosed.completeSpace_coe
  let E : ClosedSubmodule ℂ K := ⟨N.toSubmoduleᗮ, N.toSubmodule.isClosed_orthogonal⟩
  let : CompleteSpace E.toSubmodule := E.isClosed.completeSpace_coe
  have hN (a : A) (x : K) (hx : x ∈ N) : σ a x ∈ N := by
    change L (σ a x) = 0
    have h := congrArg (fun T : K →L[ℂ] H => T x) (hL a)
    change L x = 0 at hx
    simpa only [comp_apply, hx, map_zero] using h
  have hE (a : A) (x : K) (hx : x ∈ E) : σ a x ∈ E := by
    apply (N.toSubmodule.mem_orthogonal _).mpr
    intro y hy
    rw [← adjoint_inner_left, ← star_eq_adjoint, ← map_star]
    exact (N.toSubmodule.mem_orthogonal x).mp hx _ (hN (star a) y hy)
  let σ₀ := restrictStarRepresentation σ E hE
  let L₀ : E →L[ℂ] H := L.domRestrict E.toSubmodule
  let W₀ : H →L[ℂ] E := E.toSubmodule.orthogonalProjectionOnto.comp W
  have hL₀W₀ : L₀.comp W₀ = 1 := by
    ext x
    change L ((N.toSubmoduleᗮ).orthogonalProjectionOnto (W x) : K) = x
    rw [N.toSubmodule.orthogonalProjectionOnto_orthogonal]
    change L (W x - N.toSubmodule.starProjection (W x)) = x
    have hz : L (N.toSubmodule.starProjection (W x)) = 0 :=
      Submodule.starProjection_apply_mem N.toSubmodule (W x)
    have hw := congrArg (fun T : H →L[ℂ] H => T x) hLW
    simpa only [map_sub, hz, sub_zero, comp_apply, one_def, id_apply] using hw
  have hL₀inj : Function.Injective L₀ := by
    intro x y hxy
    apply Subtype.ext
    have hk : (x : K) - (y : K) ∈ N := by
      change L ((x : K) - (y : K)) = 0
      change L (x : K) = L (y : K) at hxy
      rw [map_sub, hxy, sub_self]
    have he : (x : K) - (y : K) ∈ N.toSubmoduleᗮ := E.sub_mem x.property y.property
    have hz := (N.toSubmodule.mem_orthogonal _).mp he _ hk
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)
  have hW₀L₀ : W₀.comp L₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    exact congrArg (fun T : H →L[ℂ] H => T (L₀ x)) hL₀W₀
  have hL₀ (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact congrArg (fun T : K →L[ℂ] H => T x) (hL a)
  have hW₀ (a : A) : W₀.comp (π.1 a) = (σ₀ a).comp W₀ := by
    apply ContinuousLinearMap.ext
    intro x
    apply hL₀inj
    have hlx := congrArg (fun T : H →L[ℂ] H => T x) hL₀W₀
    have hla := congrArg (fun T : H →L[ℂ] H => T (π.1 a x)) hL₀W₀
    have hi := congrArg (fun T : E →L[ℂ] H => T (W₀ x)) (hL₀ a)
    change L₀ (W₀ (π.1 a x)) = L₀ (σ₀ a (W₀ x))
    simpa only [comp_apply, one_def, id_apply] using hla.trans (hi.trans
      (congrArg (π.1 a) hlx)).symm
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (E.toSubmodule.norm_orthogonalProjectionOnto_apply_le (W x)).trans
      (W.le_opNorm x)
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hstar⟩ := quantitative_similarity_of_intertwiner
    π σ₀ W₀ L₀ hL₀W₀ hW₀L₀ hW₀
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hstar⟩

/-- Multiplicativity upgrades a bounded star-representation factorization
to a similarity, with the original product bound. -/
theorem quantitative_similarity_of_factorization
    (π : BoundedUnitalHom A H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hf : ∀ a, L.comp ((σ a).comp W) = π.1 a) :
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ ‖W‖ * ‖L‖ ∧
      ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)) := by
  let M := factorizationSpace σ W
  let : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
  let σ₀ := restrictStarRepresentation σ M (factorizationSpace_invariant σ W)
  let W₀ : H →L[ℂ] M := W.codRestrict M.toSubmodule (right_mem_factorizationSpace σ W)
  let L₀ : M →L[ℂ] H := L.domRestrict M.toSubmodule
  have hLW : L₀.comp W₀ = 1 := by
    ext x
    change L (W x) = x
    have h := congrArg (fun T : H →L[ℂ] H => T x) (hf 1)
    simpa only [comp_apply, map_one, one_def, id_apply] using h
  have hL (a : A) : L₀.comp (σ₀ a) = (π.1 a).comp L₀ := by
    ext x
    exact left_intertwines_factorizationSpace π σ W L hf a x x.property
  have hnW : ‖W₀‖ ≤ ‖W‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact W.le_opNorm x
  have hnL : ‖L₀‖ ≤ ‖L‖ := by
    apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact L.le_opNorm (x : K)
  obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_surjective_intertwiner
    π σ₀ W₀ L₀ hLW hL
  exact ⟨S, hS.trans (mul_le_mul hnW hnL (norm_nonneg _) (norm_nonneg _)), hs⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_PaulsenDischarge
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative similarity from the proved completely bounded factorization

The entrywise C-star matrix norm agrees with the concrete matrix operator
norm. Applying the proved factorization and then removing its kernel gives
Paulsen's quantitative similarity conclusion on the original Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem completeBound_entrywise (π : BoundedUnitalHom A H) {C : ℝ}
    (hπ : CompleteBound π.1 C) (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖X.map π.1.toLinearMap‖ ≤ C * ‖X‖ := by
  have h := hπ n (CStarMatrix.ofMatrix.symm X)
  change ‖matrixOperator (CStarMatrix.ofMatrix.symm (X.map π.1.toLinearMap))‖ ≤ C * ‖X‖ at h
  rwa [norm_matrixOperator_eq] at h

/-- Paulsen's quantitative similarity bound, including the zero Hilbert space. -/
theorem paulsenSimilarityInput (π : BoundedUnitalHom A H) : PaulsenSimilarityInput π := by
  intro C hC hπ
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨1, ?_, fun _ => Subsingleton.elim _ _⟩
    have hnorm : ‖(1 : H →L[ℂ] H)‖ = 0 := by
      rw [Subsingleton.elim (1 : H →L[ℂ] H) 0, norm_zero]
    simpa only [inv_one, Units.val_one, hnorm, zero_mul] using hC
  · let := hH
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have he := congrArg π.1 h
      have hz : (0 : H →L[ℂ] H) = 1 := by
        simpa only [map_zero, map_one] using he
      exact zero_ne_one hz
    let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
    have hm : (1 : CStarMatrix (Fin 1) (Fin 1) A).map π.1.toLinearMap = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    have hc := completeBound_entrywise π hπ 1 1
    rw [hm, CStarRing.norm_one, CStarRing.norm_one, mul_one] at hc
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hc
    obtain ⟨F⟩ := BoundedHochschild.KadisonRingrose.factorization_of_complete_bound
      π.1.toLinearMap hCpos (completeBound_entrywise π hπ)
    obtain ⟨S, hS, hs⟩ := quantitative_similarity_of_factorization
      π F.representation F.rightMap F.leftMap.adjoint (fun a => (F.factorization a).symm)
    refine ⟨S, hS.trans ?_, hs⟩
    simpa only [ContinuousLinearMap.adjoint.norm_map, mul_comm] using F.bound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicSpatialDerivation
attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial implementation in the initial irreducible representation

The proved cyclic column estimate and completely bounded factorization
implement a bounded derivation in a cyclic representation. Taking the real
part gives the self-adjoint implementer used in Sakai's quotient argument.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cyclic_spatial_derivation
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hcyclic : ∃ ξ : H, DenseRange (fun a : A => π a ξ))
    (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ T : H →L[ℂ] H, ∀ a, π (D a) = T * π a - π a * T := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let δ : A →L[ℂ] (H →L[ℂ] H) :=
    { toLinearMap := π.toLinearMap.comp D.toLinearMap
      cont := by
        change Continuous (fun a => π (D a))
        exact (show Continuous π by fun_prop).comp D.continuous }
  have hδ : ∀ a b, δ (a * b) = (π a).comp (δ b) + (δ a).comp (π b) := by
    intro a b
    change π (D (a * b)) = π a * π (D b) + π (D a) * π b
    rw [hD, map_add, map_mul, map_mul, add_comm]
  obtain ⟨ξ, hξ⟩ := hcyclic
  obtain ⟨T, hT, _⟩ := KadisonSimilarity.cyclic_derivation_implementation_of_column_tests
    π π δ hδ (KadisonSimilarity.cyclicColumnTests_of_dense_orbit π ξ hξ)
    (KadisonSimilarity.paulsenSimilarityInput
      (KadisonSimilarity.normalizedRectangularRepresentation π π δ hδ))
  exact ⟨T, hT⟩

theorem selfAdjoint_spatial_implementer
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : A →L[ℂ] A)
    (hstar : ∀ a, D (star a) = -star (D a))
    (T : H →L[ℂ] H) (hT : ∀ a, π (D a) = T * π a - π a * T) :
    ∃ S : H →L[ℂ] H, IsSelfAdjoint S ∧
      ∀ a, π (D a) = S * π a - π a * S := by
  have hTs : ∀ a, π (D a) = star T * π a - π a * star T := by
    intro a
    have h := congrArg star (hT (star a))
    rw [hstar, map_neg, map_star, star_neg, star_star,
      star_sub, star_mul, star_mul, map_star, star_star] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨(1 / 2 : ℂ) • (T + star T),
    (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self T), ?_⟩
  intro a
  calc
    π (D a) = (1 / 2 : ℂ) • (π (D a) + π (D a)) := by
      rw [← two_smul ℂ (π (D a)), smul_smul]
      norm_num
    _ = (1 / 2 : ℂ) • ((T * π a - π a * T) +
        (star T * π a - π a * star T)) := by
      conv_lhs => arg 2; arg 1; rw [hT]
      conv_lhs => arg 2; arg 2; rw [hTs]
    _ = ((1 / 2 : ℂ) • (T + star T)) * π a -
        π a * ((1 / 2 : ℂ) • (T + star T)) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_sub, smul_add]
      abel

theorem exists_simple_spatial_derivation_oai [Nontrivial A]
    (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ NaimarkZFC.IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
        ∀ a, π (D a) = T * π a - π a * T := by
  obtain ⟨H, _, _, _, _, π, hπ, hirr, ξ, _, hξ⟩ :=
    exists_simple_irreducible_representation hA
  obtain ⟨T, hT⟩ := cyclic_spatial_derivation π ⟨ξ, hξ⟩ D hD
  obtain ⟨S, hS, hSD⟩ := selfAdjoint_spatial_implementer π D hstar T hT
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, π,
    hπ, hirr, S, hS, hSD⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_simple_spatial_derivation_oai.{u} := @OAI.KadisonKastler.exists_simple_spatial_derivation_oai.{u}
