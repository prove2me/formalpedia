-- Prove2me | solution 1 for OAI.KadisonKastler.pure_restriction_commuting_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:50:15.916618+00:00
-- url     : https://prove2.me/submissions/cb23bd7e-9715-435c-b5a2-b1728ec54713

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Definitions.Def_Q260K007

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFunctional_norm_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    ‖vectorFunctional π x‖ ≤ ‖x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro a
  calc
    ‖vectorFunctional π x a‖ = ‖⟪x, π a x⟫_ℂ‖ := rfl
    _ ≤ ‖x‖ * ‖π a x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖π a‖ * ‖x‖) := by gcongr; exact (π a).le_opNorm x
    _ ≤ ‖x‖ * (‖a‖ * ‖x‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = ‖x‖ ^ 2 * ‖a‖ := by ring

theorem isState_vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : ‖x‖ = 1) : IsState (vectorFunctional π x) := by
  constructor
  · apply le_antisymm
    · simpa [hx] using vectorFunctional_norm_le π x
    · calc
        1 = ‖vectorFunctional π x 1‖ := by simp [vectorFunctional_one π hone, hx]
        _ ≤ ‖vectorFunctional π x‖ * ‖(1 : A)‖ := (vectorFunctional π x).le_opNorm 1
        _ ≤ ‖vectorFunctional π x‖ * 1 := by
          gcongr
          exact (IsStarProjection.one A).norm_le _
        _ = ‖vectorFunctional π x‖ := mul_one _
  · intro a
    rw [vectorFunctional_square]
    simp only [← Complex.ofReal_pow, Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact sq_nonneg _

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

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_denseRange (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hcomm : ∀ a : A, Commute T (π a)) : DenseRange T := by
  let M := T.range
  have hinv (a : A) : M.map (π a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨π a x, ?_⟩
    exact congrArg (fun S : H →L[ℂ] H => S x) (hcomm a).eq
  have hcl (a : A) (x : H) (hx : x ∈ M.topologicalClosure) :
      π a x ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hinv a)
    apply Submodule.topologicalClosure_map (π a) M
    exact ⟨x, hx, rfl⟩
  rcases hπ.2 M.topologicalClosure M.isClosed_topologicalClosure hcl with hz | ht
  · exfalso
    apply hT
    ext x
    have hx : T x ∈ M.topologicalClosure := M.le_topologicalClosure ⟨x, rfl⟩
    rw [hz] at hx
    exact hx
  · intro x
    have hx : x ∈ M.topologicalClosure := by rw [ht]; trivial
    exact hx

theorem commutant_mul_eq_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (S T : H →L[ℂ] H)
    (hcomm : ∀ a : A, Commute T (π a)) (hz : S * T = 0) : S = 0 ∨ T = 0 := by
  by_cases hT : T = 0
  · exact Or.inr hT
  · left
    apply DFunLike.coe_injective
    change (fun x => S x) = (fun _ => 0)
    apply (irreducible_commutant_denseRange π hπ T hT hcomm).equalizer
      S.continuous continuous_const
    funext x
    exact congrArg (fun R : H →L[ℂ] H => R x) hz

theorem irreducible_commutant_selfAdjoint_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ r : ℝ, T = r • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, Subsingleton.elim _ _⟩
  let : Nontrivial H := hH
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) T hT
  refine ⟨r, ?_⟩
  have unique (x y : ℝ) (hx : x ∈ spectrum ℝ T) (hy : y ∈ spectrum ℝ T) : ¬ x < y := by
    intro hxy
    let c := (x + y) / 2
    let f : ℝ → ℝ := fun t => max (t - c) 0
    let g : ℝ → ℝ := fun t => max (c - t) 0
    have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
    have hg : Continuous g := (continuous_const.sub continuous_id).max continuous_const
    have hfg (t : ℝ) : f t * g t = 0 := by
      dsimp [f, g]
      by_cases h : t ≤ c
      · rw [max_eq_right (sub_nonpos.mpr h), zero_mul]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), mul_zero]
    have hzero : cfc f T * cfc g T = 0 := by
      rw [← cfc_mul f g T hf.continuousOn hg.continuousOn]
      rw [cfc_congr (g := fun _ : ℝ => 0) (fun t _ => hfg t), cfc_const_zero]
    rcases commutant_mul_eq_zero π hπ (cfc f T) (cfc g T)
      (fun a => hT.commute_cfc (hcomm a) g) hzero with hz | hz
    · have heq : cfc f T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hT hy
      dsimp [f, c] at hval
      have hpos : 0 < y - (x + y) / 2 := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
    · have heq : cfc g T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hg.continuousOn continuousOn_const hT hx
      dsimp [g, c] at hval
      have hpos : 0 < (x + y) / 2 - x := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
  have hspec : spectrum ℝ T ⊆ {r} := by
    intro t ht
    exact le_antisymm (not_lt.mp (unique r t hr ht)) (not_lt.mp (unique t r ht hr))
  simpa [Algebra.algebraMap_eq_smul_one] using
    CFC.eq_algebraMap_of_spectrum_subset_singleton T r hspec hT

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PureCommutingCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression to a pure cyclic representation

A pure vector-state restriction makes every commuting operator scalar
after compression to the cyclic subspace. This is the factorization step
for the initial product state on the two commuting factor algebras.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexStarModule ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_complex_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) :
    ∃ z : ℂ, T=z • (1 : H →L[ℂ] H) := by
  have hstar (a : A) : Commute (star T) (π a) := by
    have h := (hT (star a)).star_star
    simpa only [map_star,star_star] using h
  have hre (a : A) : Commute (realPart T).val (π a) := by
    rw [realPart_apply_coe]
    exact ((hT a).add_left (hstar a)).smul_left _
  have him (a : A) : Commute (imaginaryPart T).val (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hT a).sub_left (hstar a)).smul_left _).smul_left _
  obtain ⟨r,hr⟩ := irreducible_commutant_selfAdjoint_scalar π hπ _
    (realPart T).property hre
  obtain ⟨s,hs⟩ := irreducible_commutant_selfAdjoint_scalar π hπ _
    (imaginaryPart T).property him
  refine ⟨(r : ℂ)+Complex.I*(s : ℂ),?_⟩
  calc
    T = (realPart T).val+Complex.I • (imaginaryPart T).val :=
      (realPart_add_I_smul_imaginaryPart T).symm
    _ = r • (1 : H →L[ℂ] H)+Complex.I • (s • (1 : H →L[ℂ] H)) := by rw [hr,hs]
    _ = _ := by rw [← Complex.coe_smul,← Complex.coe_smul,smul_smul,← add_smul]

variable [PartialOrder A] [StarOrderedRing A]

theorem cyclicGNSMap_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a, f a=inner ℂ ξ (π a ξ)) (a : A) :
    (cyclicGNSMap f π ξ hcoeff).comp (f.gnsStarAlgHom a)=
      (π a).comp (cyclicGNSMap f π ξ hcoeff) := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
  funext b
  simp only [ContinuousLinearMap.comp_apply,Function.comp_apply,gns_apply_vector,
    gns_apply_coe,cyclicGNSMap_apply,map_mul,mul_apply_eq_comp]

theorem pureVector_commuting_factorization
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖=1)
    (hpure : IsPureState (NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ))
    (T : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) (a : A) :
    inner ℂ ξ (π a (T ξ))=inner ℂ ξ (π a ξ)*inner ℂ ξ (T ξ) := by
  let f := NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ
  have hf : IsState f := isState_vectorFunctional π.toNonUnitalStarAlgHom π.map_one ξ hξ
  let P := positiveOfSquares f hf.2
  have hcoeff (b : A) : P b=inner ℂ ξ (π.toNonUnitalStarAlgHom b ξ) := rfl
  let W := cyclicGNSMap P π.toNonUnitalStarAlgHom ξ hcoeff
  let g := gnsVector P
  have hWg : W g=ξ := by
    change cyclicGNSMap P π.toNonUnitalStarAlgHom ξ hcoeff (P.toPreGNS 1)=ξ
    rw [cyclicGNSMap_apply]
    change π 1 ξ=ξ
    have hone : π 1=1 := map_one π
    rw [hone]
    rfl
  have hg : ‖g‖=1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf).1
  have hW (b : A) : W.comp (P.gnsStarAlgHom b)=(π b).comp W :=
    cyclicGNSMap_intertwines P π.toNonUnitalStarAlgHom ξ hcoeff b
  have hWs (b : A) : W.adjoint.comp (π b)=(P.gnsStarAlgHom b).comp W.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint (hW (star b))
    simpa only [ContinuousLinearMap.adjoint_comp,map_star,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h.symm
  let C := W.adjoint.comp (T.comp W)
  have hC (b : A) : Commute C (P.gnsStarAlgHom b) := by
    change C.comp (P.gnsStarAlgHom b)=(P.gnsStarAlgHom b).comp C
    ext x
    have hWx := congrArg (fun L : P.GNS →L[ℂ] H => L x) (hW b)
    have hTx := congrArg (fun L : H →L[ℂ] H => L (W x)) (hT b).eq
    have hWsx := congrArg (fun L : H →L[ℂ] P.GNS => L (T (W x))) (hWs b)
    change W.adjoint (T (W (P.gnsStarAlgHom b x)))=
      P.gnsStarAlgHom b (W.adjoint (T (W x)))
    change W (P.gnsStarAlgHom b x)=π b (W x) at hWx
    change T (π b (W x))=π b (T (W x)) at hTx
    change W.adjoint (π b (T (W x)))=P.gnsStarAlgHom b (W.adjoint (T (W x))) at hWsx
    rw [hWx,hTx,hWsx]
  obtain ⟨z,hz⟩ := irreducible_commutant_complex_scalar P.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible f hf hpure) C hC
  have hzvalue : inner ℂ ξ (T ξ)=z := by
    calc
      inner ℂ ξ (T ξ) = inner ℂ g (C g) := by
        change inner ℂ ξ (T ξ)=inner ℂ g (W.adjoint (T (W g)))
        rw [ContinuousLinearMap.adjoint_inner_right,hWg]
      _ = inner ℂ g (z • g) := by rw [hz]; rfl
      _ = z := by rw [inner_smul_right,inner_self_eq_norm_sq_to_K,hg]; simp
  calc
    inner ℂ ξ (π a (T ξ)) = inner ℂ ξ (T (π a ξ)) :=
      congrArg (fun x => inner ℂ ξ x) (congrArg (fun L : H →L[ℂ] H => L ξ) (hT a).eq.symm)
    _ = inner ℂ g (C (P.gnsStarAlgHom a g)) := by
      change _=inner ℂ g (W.adjoint (T (W (P.gnsStarAlgHom a g))))
      rw [ContinuousLinearMap.adjoint_inner_right,hWg]
      have hWa := congrArg (fun L : P.GNS →L[ℂ] H => L g) (hW a)
      change W (P.gnsStarAlgHom a g)=π a (W g) at hWa
      rw [hWg] at hWa
      exact congrArg (fun x => inner ℂ ξ (T x)) hWa.symm
    _ = z*inner ℂ g (P.gnsStarAlgHom a g) := by rw [hz]; simp only [smul_apply,one_apply_eq_self,inner_smul_right]
    _ = inner ℂ ξ (π a ξ)*inner ℂ ξ (T ξ) := by
      rw [gnsVector_coefficient,hcoeff,hzvalue,mul_comm]
      rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PureRestrictionFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product values from a pure restriction

An ambient state whose restriction to one algebra is pure factors
against every element commuting with that algebra.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem pure_restriction_commuting_factorization_oai
    (ι : A →⋆ₐ[ℂ] B) (φ : B →L[ℂ] ℂ) (hφ : IsState φ)
    (hpure : IsPureState (restrictState ι φ))
    (b : B) (hb : ∀ a : A, Commute b (ι a)) (a : A) :
    φ (ι a*b)=φ (ι a)*φ b := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let P := positiveOfSquares φ hφ.2
  let π := P.gnsStarAlgHom.comp ι
  let ξ := gnsVector P
  have hξ : ‖ξ‖=1 := gnsVector_norm_eq_one P ((isState_iff φ).mp hφ).1
  have hstate : NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ=restrictState ι φ := by
    ext c
    exact gnsVector_coefficient P (ι c)
  have hp : IsPureState (NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ) := by
    rwa [hstate]
  have hc (c : A) : Commute (P.gnsStarAlgHom b) (π c) :=
    (hb c).map P.gnsStarAlgHom
  have h := pureVector_commuting_factorization π ξ hξ hp (P.gnsStarAlgHom b) hc a
  calc
    φ (ι a*b) = inner ℂ ξ (P.gnsStarAlgHom (ι a*b) ξ) :=
      (gnsVector_coefficient P (ι a*b)).symm
    _ = inner ℂ ξ (π a (P.gnsStarAlgHom b ξ)) := by
      rw [map_mul]
      rfl
    _ = inner ℂ ξ (π a ξ)*inner ℂ ξ (P.gnsStarAlgHom b ξ) := h
    _ = φ (ι a)*φ b := by
      change inner ℂ ξ (P.gnsStarAlgHom (ι a) ξ)*
        inner ℂ ξ (P.gnsStarAlgHom b ξ)=_
      rw [gnsVector_coefficient,gnsVector_coefficient]
      rfl

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.pure_restriction_commuting_factorization_oai.{u_1, u_2} := @OAI.KadisonKastler.pure_restriction_commuting_factorization_oai.{u_1, u_2}
