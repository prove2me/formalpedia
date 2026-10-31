-- Prove2me | solution 1 for OAI.Release061.original_small_slope_good_supported_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:06:16.525673+00:00
-- url     : https://prove2.me/submissions/d27db383-5a40-4606-b25b-57d3ddcaaa9a

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002
import Theorems.Thm_OAI_Release061_NashPatch_null_nonsmallgood_generic
import Theorems.Thm_OAI_Release061_cocompact_bounded_affine_smooth
import Theorems.Thm_OAI_Release061_prime_boundary_generic_fiber

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalarEquicontinuousHolomorphy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem zeroLocus_closed {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
      {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
    ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscRelationCompactLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem peakLinear_re {n : ℕ} (p q : Affine n) :
    (peakLinear p q).re = coordinateEnergy q - coordinateEnergy p - coordinateEnergy (q-p) := by
  simp only [peakLinear, coordinateEnergy, Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

theorem coordinateEnergy_nonneg {n : ℕ} (z : Affine n) : 0 ≤ coordinateEnergy z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sq_norm_le_coordinateEnergy {n : ℕ} (z : Affine n) : ‖z‖^2 ≤ coordinateEnergy z := by
  have h : ‖z‖ ≤ Real.sqrt (coordinateEnergy z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i)
  exact (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mp h

 theorem peakLinear_analytic {n : ℕ} (p : Affine n) : AnalyticOnNhd ℂ (peakLinear p) univ := by
  intro q _
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_const.mul (((ContinuousLinearMap.proj i : (Affine n) →L[ℂ] ℂ).analyticAt q).sub analyticAt_const))

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem HolomorphicOnSubset.restrict {d n : ℕ} {S W : Set (Affine d)}
    {f : S → Affine n} (hf : HolomorphicOnSubset S f) (hWS : W ⊆ S) :
    HolomorphicOnSubset W (fun p => f ⟨p.val,hWS p.property⟩) := by
  intro p
  obtain ⟨O,hO,hpO,F,hF,he⟩ := hf ⟨p.val,hWS p.property⟩
  exact ⟨O,hO,hpO,F,hF,fun q hqO => he ⟨q.val,hWS q.property⟩ hqO⟩

open Filter
open scoped Topology

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ClosedMaximizerRelation
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set MeasureTheory _root_.Module Filter
open scoped Topology ENNReal

theorem affine_image_spans_of_positive_measure
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [AddCommGroup G] [Module ℝ G]
    (ν : Measure F) [ν.IsAddHaarMeasure] {s : Set F} (hs : ν s ≠ 0)
    (A : F →ᵃ[ℝ] G) (hA : Function.Surjective A) :
    Submodule.span ℝ (A '' s) = ⊤ := by
  by_contra hspan
  let W := (Submodule.span ℝ (A '' s)).toAffineSubspace.comap A
  have hW : W ≠ ⊤ := by
    intro h
    apply hspan
    apply top_unique
    intro v _
    obtain ⟨x,rfl⟩ := hA v
    have hx : x ∈ W := by rw [h]; trivial
    exact hx
  apply hs
  apply measure_mono_null (t := (W : Set F))
  · intro x hx
    exact Submodule.subset_span (mem_image_of_mem A hx)
  · exact Measure.addHaar_affineSubspace ν W hW

theorem exists_independent_affine_images_of_positive_measure
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
    (ν : Measure F) [ν.IsAddHaarMeasure] {s : Set F} (hs : ν s ≠ 0)
    (A : F →ᵃ[ℝ] G) (hA : Function.Surjective A) :
    ∃ v : Fin (finrank ℝ G) → F, (∀ i, v i ∈ s) ∧
      LinearIndependent ℝ (fun i => A (v i)) := by
  classical
  have hspan := affine_image_spans_of_positive_measure ν hs A hA
  let b := Basis.ofSpan (s := A '' s) (show ⊤ ≤ Submodule.span ℝ (A '' s) by rw [hspan])
  let b' := b.reindex (b.indexEquiv (finBasis ℝ G))
  have hb : ∀ i, ∃ v ∈ s, A v = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℝ (A '' s) by rw [hspan])
    refine ⟨(b.indexEquiv (finBasis ℝ G)).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose v hv hvb using hb
  refine ⟨v,hv,?_⟩
  have he : (fun i => A (v i)) = b' := funext hvb
  rw [he]
  exact b'.linearIndependent

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimitsFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem isSemialgebraic_iff_polynomialSignSet {n : ℕ} {S : Set (Affine n)} :
    IsSemialgebraic S ↔ PolynomialSignSet realCoordinates S := by
  constructor
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CenteredChartGerms
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem Biholomorph.centered_chart_germs {n m : ℕ} {V W : Set (Affine n)}
    {B : Set (Affine m)} (e : Biholomorph W B) (hWV : W ⊆ V)
    (hW : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W)) (hB : IsOpen B)
    {q : Affine n} (hq : q ∈ W) :
    ∃ (F : Affine m → Affine n) (G : Affine n → Affine m),
      F 0 = q ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ G q ∧
      (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
      (∀ᶠ y in 𝓝[V] q, F (G y) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) := by
  let b : Affine m := (e.toHomeomorph ⟨q,hq⟩).val
  have hb : b ∈ B := (e.toHomeomorph ⟨q,hq⟩).property
  let f := ambientExtend (fun y : B => (e.toHomeomorph.symm y).val)
  have hf : AnalyticOnNhd ℂ f B := e.holomorphic_invFun.analyticOnNhd_extend hB
  have hfb : f b = q := by
    rw [show f b = (e.toHomeomorph.symm (e.toHomeomorph ⟨q,hq⟩)).val from ambientExtend_apply _ _]
    simp
  obtain ⟨O,hO,hqO,g,hg,hge⟩ := e.holomorphic_toFun ⟨q,hq⟩
  let F : Affine m → Affine n := fun z => f (z+b)
  let G : Affine n → Affine m := fun y => g y-b
  have hF0 : F 0 = q := by simpa only [F,zero_add] using hfb
  have hF : AnalyticAt ℂ F 0 := by
    have htr : AnalyticAt ℂ (fun z : Affine m => z+b) 0 := analyticAt_id.add analyticAt_const
    have hf' : AnalyticAt ℂ f (0+b) := by simpa only [zero_add] using hf b hb
    exact hf'.comp (f := fun z : Affine m => z+b) (x := 0) htr
  have hG : AnalyticAt ℂ G q := (hg q hqO).sub analyticAt_const
  refine ⟨F,G,hF0,hF,hG,?_,?_,?_⟩
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    have hzO : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ O :=
      hF.continuousAt.preimage_mem_nhds (by simpa only [hF0] using hO.mem_nhds hqO)
    filter_upwards [hzB,hzO] with z hz hz'
    have hfy : f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val := ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩
    have hfw : F z ∈ W := by rw [show F z = f (z+b) from rfl,hfy]; exact (e.toHomeomorph.symm ⟨z+b,hz⟩).property
    have he : g (F z) = z+b := by
      rw [hge ⟨F z,hfw⟩ hz']
      have heq : (⟨F z,hfw⟩ : W) = e.toHomeomorph.symm ⟨z+b,hz⟩ := Subtype.ext hfy
      rw [heq]
      exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨z+b,hz⟩)
    change g (F z)-b = z
    rw [he,add_sub_cancel_right]
  · obtain ⟨O',hO',hWO'⟩ := isOpen_induced_iff.mp hW
    have hqO' : q ∈ O' := by
      have hh : (⟨q,hWV hq⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' W := hq
      rwa [← hWO'] at hh
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds hqO'),
      mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hqO)] with y hyV hyO' hyO
    have hyW : y ∈ W := by
      have hh : (⟨y,hyV⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' O' := hyO'
      rwa [hWO'] at hh
    have hgy := hge ⟨y,hyW⟩ hyO
    change f (g y-b+b) = y
    rw [sub_add_cancel,hgy]
    rw [show f (e.toHomeomorph ⟨y,hyW⟩).val =
      (e.toHomeomorph.symm (e.toHomeomorph ⟨y,hyW⟩)).val from ambientExtend_apply _ _]
    simp
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    filter_upwards [hzB] with z hz
    change f (z+b) ∈ V
    rw [show f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val from ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩]
    exact hWV (e.toHomeomorph.symm ⟨z+b,hz⟩).property

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

lemma IsSemialgebraic.inter {n : ℕ} {S T : Set (Affine n)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  exact isSemialgebraic_iff_polynomialSignSet.mpr
    ((isSemialgebraic_iff_polynomialSignSet.mp hS).inter
      (isSemialgebraic_iff_polynomialSignSet.mp hT))

namespace NashPatch
variable {n : ℕ}

lemma analytic_complexMap (p : NashPatch (n+n)) : AnalyticOnNhd ℝ p.complexMap p.domain := by
  intro x hx
  exact ((complexRealEquiv n).symm.analyticAt _).comp (p.analytic_toFun x hx)

lemma injective_fderiv_complexMap (p : NashPatch (n+n)) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    Function.Injective (fderiv ℝ p.complexMap x) := by
  have he := ((complexRealEquiv n).symm.hasFDerivAt.comp x
    (p.analytic_toFun x hx).differentiableAt.hasFDerivAt).fderiv
  change Function.Injective (fderiv ℝ ((complexRealEquiv n).symm ∘ p.toFun) x)
  rw [he]
  exact (complexRealEquiv n).symm.injective.comp (p.injective_fderiv x hx)

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicPolynomialNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set
open scoped Classical

theorem complex_polynomial_real_syntax {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    ∃ A B : MvPolynomial (Fin n ⊕ Fin n) ℝ, ∀ z : Affine n,
      MvPolynomial.eval (realCoordinates z) A = (MvPolynomial.eval z P).re ∧
      MvPolynomial.eval (realCoordinates z) B = (MvPolynomial.eval z P).im := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a.re,MvPolynomial.C a.im,by simp⟩
  | add P Q hp hq =>
    obtain ⟨A,B,h⟩ := hp
    obtain ⟨C,D,k⟩ := hq
    exact ⟨A+C,B+D,by intro z; simp only [map_add,Complex.add_re,Complex.add_im,(h z).1,(h z).2,(k z).1,(k z).2]; trivial⟩
  | mul_X P j hp =>
    obtain ⟨A,B,h⟩ := hp
    refine ⟨A*MvPolynomial.X (.inl j)-B*MvPolynomial.X (.inr j),
      A*MvPolynomial.X (.inr j)+B*MvPolynomial.X (.inl j),?_⟩
    intro z
    simp only [map_sub,map_mul,map_add,MvPolynomial.eval_X,Complex.mul_re,Complex.mul_im]
    rw [(h z).1,(h z).2]
    exact ⟨rfl,by dsimp [realCoordinates]⟩

lemma isSemialgebraic_polynomial_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsSemialgebraic {z : Affine n | MvPolynomial.eval z P = 0} := by
  obtain ⟨A,B,h⟩ := complex_polynomial_real_syntax P
  convert (IsSemialgebraic.zero A).inter (IsSemialgebraic.zero B) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,(h z).1,(h z).2,Complex.ext_iff,Complex.zero_re,Complex.zero_im]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineInverseGermSemialgebraic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical

theorem isSemialgebraic_zeroLocus {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsSemialgebraic (MvPolynomial.zeroLocus ℂ I) := by
  obtain ⟨S,hS⟩ := I.fg_of_isNoetherianRing
  rw [← hS,MvPolynomial.zeroLocus_span]
  apply isSemialgebraic_iff_polynomialSignSet.mpr
  have h : PolynomialSignSet realCoordinates {z : Affine n | ∀ p : S, MvPolynomial.eval z p.val = 0} :=
    PolynomialSignSet.forall_finite _ (fun p =>
      isSemialgebraic_iff_polynomialSignSet.mp (isSemialgebraic_polynomial_zero p.val))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  change (∀ p ∈ (S : Set (MvPolynomial (Fin n) ℂ)), MvPolynomial.eval z p = 0) ↔ _
  constructor
  · intro hz p; exact hz p.val p.property
  · intro hz p hp; exact hz ⟨p,hp⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryParametricDimensionLt
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem boundary_parametric_dimension_lt {d m N : ℕ}
    {U V : Set (Affine N)} (hUV : U ⊆ V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hp : q x ∈ closure U) (hF0 : F 0 = q x)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : AnalyticAt ℝ q x) (hqinj : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFGV : ∀ᶠ y in 𝓝[V] (q x), F (G y) = y)
    (hqV : ∀ᶠ y in 𝓝 x, q y ∈ V)
    (hqnU : ∀ᶠ y in 𝓝 x, q y ∉ U) : d < 2*m := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have ht : Tendsto q (𝓝 x) (𝓝[V] (q x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hFGq : (F ∘ G ∘ q) =ᶠ[𝓝 x] q := ht hFGV
  let r := G ∘ q
  have hr : AnalyticAt ℝ r x := hG.restrictScalars.comp hq
  have hd : ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ r x) = fderiv ℝ q x := by
    have hf' : AnalyticAt ℂ F (r x) := by simpa only [r,Function.comp_apply,hG0] using hF
    have hh := (hf'.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.differentiableAt.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFGq.symm
    simpa only [r,Function.comp_apply,hG0] using he.fderiv.symm
  have hi : Function.Injective (fderiv ℝ r x) := by
    intro a b hab
    apply hqinj
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  have hdim : Module.finrank ℝ (Affine m) = 2*m := by simp [Affine,Module.finrank_pi_fintype,Nat.mul_comm]
  have hle : d ≤ 2*m := by
    have hh := (fderiv ℝ r x).toLinearMap.finrank_le_finrank_of_injective hi
    simpa only [Module.finrank_pi,Fintype.card_fin,hdim] using hh
  apply lt_of_le_of_ne hle
  intro heq
  have hedim : Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (Affine m) := by
    simpa using heq.trans hdim.symm
  let e := ((fderiv ℝ r x).toLinearMap.linearEquivOfInjective hi hedim).toContinuousLinearEquiv
  have he : (e : (Fin d → ℝ) →L[ℝ] Affine m) = fderiv ℝ r x := by ext v; rfl
  have hs : HasStrictFDerivAt r (e : (Fin d → ℝ) →L[ℝ] Affine m) x := by
    rw [he]; exact hr.hasStrictFDerivAt
  let B : Set (Fin d → ℝ) := {y | F (G (q y)) = q y ∧ q y ∉ U}
  have hB : B ∈ 𝓝 x := hFGq.and hqnU
  have hBr : r '' B ∈ 𝓝 (r x) := by
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map hB
  have hGBr : ∀ᶠ y in 𝓝 (q x), G y ∈ r '' B := hG.continuousAt hBr
  have hFGU : ∀ᶠ y in 𝓝[U] (q x), F (G y) = y :=
    hFGV.filter_mono (nhdsWithin_mono _ hUV)
  have hfalse : ∀ᶠ y in 𝓝[U] (q x), False := by
    filter_upwards [self_mem_nhdsWithin,hFGU,
      mem_nhdsWithin_of_mem_nhds hGBr] with y hy he hyB
    obtain ⟨t,htB,ht⟩ := hyB
    have hty : q t = y := by
      rw [← htB.1]
      change F (r t) = y
      rw [ht,he]
    exact htB.2 (hty.symm ▸ hy)
  have : NeBot (𝓝[U] (q x)) := mem_closure_iff_nhdsWithin_neBot.mp hp
  exact hfalse.exists.elim (fun _ h => h)
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateDerivativeRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem complex_span_real_linear_range {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Submodule.span ℂ (range L) =
      Submodule.span ℂ (range (fun i => L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change ((x i : ℂ) • L (Pi.single i 1)) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact mem_range_self _

theorem matrix_rank_eq_complex_tangent_dimension {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Matrix.rank (fun j i => L (Pi.single i 1) j) =
      Module.finrank ℂ (Submodule.span ℂ (range L)) := by
  rw [complex_span_real_linear_range L]
  exact Matrix.rank_eq_finrank_span_cols _

theorem complex_tangent_eq_of_rank_ge {d N m : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ))
    (T : Submodule ℂ (Fin N → ℂ)) (hT : Module.finrank ℂ T = m)
    (hLT : ∀ x, L x ∈ T)
    (hr : m ≤ Matrix.rank (fun j i => L (Pi.single i 1) j)) :
    Submodule.span ℂ (range L) = T := by
  have hle : Submodule.span ℂ (range L) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hLT x
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  simpa only [matrix_rank_eq_complex_tangent_dimension,hT] using hr

theorem chart_tangent_finrank {m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ)) {a : Fin m → ℂ}
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id) :
    Module.finrank ℂ (LinearMap.range (fderiv ℂ F a).toLinearMap) = m := by
  have hcomp := hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    hid.unique (hasFDerivAt_id a)
  have hinj : Function.Injective (fderiv ℂ F a) := by
    intro x y hxy
    have hh := congrArg (fderiv ℂ G (F a)) hxy
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh
  simpa using LinearMap.finrank_range_of_inj (f := (fderiv ℂ F a).toLinearMap) hinj

theorem real_derivative_mem_chart_tangent {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF : AnalyticAt ℂ F (G (q x))) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) (v : Fin d → ℝ) :
    fderiv ℝ q x v ∈ LinearMap.range (fderiv ℂ F (G (q x))).toLinearMap := by
  have hGc := hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFc := hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hc := hFc.comp x (hGc.comp x hq.hasFDerivAt)
  have he := hc.congr_of_eventuallyEq hFG.symm
  have hd := he.fderiv
  refine ⟨fderiv ℂ G (q x) (fderiv ℝ q x v),?_⟩
  exact (congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) hd).symm

theorem coordinate_derivative_rank {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hq : DifferentiableAt ℝ q x) :
    Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) =
      Module.finrank ℂ (Submodule.span ℂ (range (fderiv ℝ q x))) := by
  have he (j : Fin N) : fderiv ℝ (fun y => q y j) x =
      (ContinuousLinearMap.proj j).comp (fderiv ℝ q x) := by
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hq.hasFDerivAt).fderiv
  simp_rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  exact matrix_rank_eq_complex_tangent_dimension (fderiv ℝ q x).toLinearMap

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ParameterPeakMaximizer
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex Filter Metric
open scoped Topology

theorem parameterPeak_norm {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p q : Affine n) :
    ‖parameterPeak P a p q‖ =
      parameterPotential P a q / parameterPotential P a p *
        Real.exp (-coordinateEnergy (q-p)) := by
  simp only [parameterPeak,norm_mul,norm_div,Complex.norm_exp,Complex.add_re,
    peakLinear_re,map_sub,Complex.sub_re,parameterPotential]
  rw [show coordinateEnergy q-coordinateEnergy p-coordinateEnergy (q-p)+
      ((a q).re-(a p).re) = (coordinateEnergy q+(a q).re)-
        (coordinateEnergy p+(a p).re)-coordinateEnergy (q-p) by ring,
    Real.exp_sub,Real.exp_sub,Real.exp_neg]
  ring

theorem parameterPeak_analytic {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p : Affine n) :
    AnalyticOnNhd ℂ (parameterPeak P a p) univ := by
  intro q _
  have hsub : AnalyticAt ℂ (fun x : Affine n => x-p) q := analyticAt_id.sub analyticAt_const
  have ha := (a.analyticAt (q-p)).comp (f := fun x : Affine n => x-p) (x := q) hsub
  exact (((AnalyticOnNhd.eval_mvPolynomial P) q (mem_univ _)).mul analyticAt_const).mul
    (((peakLinear_analytic p q (mem_univ _)).add
      ha).cexp)

theorem parameterPeak_self {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {p : Affine n} (hp : MvPolynomial.eval p P ≠ 0) :
    parameterPeak P a p p = 1 := by simp [parameterPeak,peakLinear,hp]

theorem parameterPeak_bound {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {K : Set (Affine n)} {p : Affine n}
    (hp : MvPolynomial.eval p P ≠ 0) (hmax : IsMaxOn (parameterPotential P a) K p) :
    ∀ q ∈ K, ‖parameterPeak P a p q‖ ≤ Real.exp (-(dist q p)^2) := by
  intro q hq
  rw [parameterPeak_norm]
  have hpp : 0 < parameterPotential P a p :=
    mul_pos (norm_pos_iff.mpr hp) (Real.exp_pos _)
  have hh := (div_le_one hpp).mpr (hmax hq)
  calc
    _ ≤ 1 * Real.exp (-coordinateEnergy (q-p)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ ≤ Real.exp (-(dist q p)^2) := by
      rw [one_mul,dist_eq_norm]
      exact Real.exp_le_exp.mpr (neg_le_neg (sq_norm_le_coordinateEnergy _))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MaximizerBundleBorel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical ContDiff

lemma coordinateEnergy_contDiff {N : ℕ} {r : ℕ∞ω} : ContDiff ℝ r (@coordinateEnergy N) := by
  unfold coordinateEnergy
  exact ContDiff.sum (fun i _ => (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℝ] ℂ).contDiff.norm_sq ℂ)

lemma parameterLogBase_contDiffAt {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) {r : ℕ∞ω} :
    ContDiffAt ℝ r (parameterLogBase P) z := by
  have hP : ContDiffAt ℝ r (fun z => MvPolynomial.eval z P) z :=
    (((AnalyticOnNhd.eval_mvPolynomial P) z (mem_univ z)).restrictScalars (𝕜 := ℝ)).contDiffAt
  exact ((hP.norm ℂ hz).log (norm_ne_zero_iff.mpr hz)).add coordinateEnergy_contDiff.contDiffAt

lemma parameterPotential_eq_exp {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) :
    parameterPotential P a z = Real.exp (parameterLogBase P z + (a z).re) := by
  rw [parameterLogBase,add_assoc,Real.exp_add,Real.exp_log (norm_pos_iff.mpr hz)]
  rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentConormals
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

lemma ambientCovector_apply (c : ActualCriticalChart P q) (x : Fin d → ℝ)
    (k : Fin c.fiberDim → ℝ) (v : Affine N) :
    c.ambientCovector x k v = fderiv ℝ (parameterLogBase P) (q x) v + (c.param (x,k) v).re := rfl

lemma ambientCovector_comp (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    (k : Fin c.fiberDim → ℝ) :
    (c.ambientCovector x k).comp (fderiv ℝ q x).toLinearMap = 0 := by
  have hm : c.param (x,k) ∈ range (fun t => c.param (x,t)) := mem_range_self k
  change c.param (x,k) ∈ range (fun t => criticalBundleParam (realCriticalMatrix q) c.split
    (realCriticalConstant (parameterLogBase P ∘ q)) (x,t)) at hm
  rw [c.range_param x hx] at hm
  have hb := (parameterLogBase_contDiffAt P hP (r := 1)).differentiableAt one_ne_zero
  have he := (hb.hasFDerivAt.add
    (Complex.reCLM.comp ((c.param (x,k)).restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt
  have hf : (fderiv ℝ (parameterLogBase P) (q x) +
      Complex.reCLM.comp ((c.param (x,k)).restrictScalars ℝ)).comp (fderiv ℝ q x) = 0 :=
    he.fderiv.symm.trans hm
  apply LinearMap.ext
  intro v
  exact congrArg (fun L => L v) hf

lemma ambientCovector_range (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0) :
    range (c.ambientCovector x) =
      ((LinearMap.range (fderiv ℝ q x).toLinearMap).dualAnnihilator : Set (Module.Dual ℝ (Affine N))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨k,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro v ⟨w,rfl⟩
    exact congrArg (fun L : (Fin d → ℝ) →ₗ[ℝ] ℝ => L w) (c.ambientCovector_comp hx hq hP k)
  · intro l hl
    let b := fderiv ℝ (parameterLogBase P) (q x)
    let a := (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)) (l.toContinuousLinearMap-b)
    have ha : Complex.reCLM.comp (a.restrictScalars ℝ) = l.toContinuousLinearMap-b := by
      exact (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)).symm_apply_apply _
    have hm : a ∈ range (fun k => c.param (x,k)) := by
      change a ∈ range (fun t => criticalBundleParam (realCriticalMatrix q) c.split
        (realCriticalConstant (parameterLogBase P ∘ q)) (x,t))
      rw [c.range_param x hx]
      have hb := (parameterLogBase_contDiffAt P hP (r := 1)).differentiableAt one_ne_zero
      have he := (hb.hasFDerivAt.add (Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt
      change fderiv ℝ ((parameterLogBase P + (⇑(Complex.reCLM.comp (a.restrictScalars ℝ)))) ∘ q) x = 0
      rw [he.fderiv,ha]
      apply ContinuousLinearMap.ext
      intro v
      change b (fderiv ℝ q x v) + (l (fderiv ℝ q x v)-b (fderiv ℝ q x v)) = 0
      rw [add_sub_cancel]
      exact (Submodule.mem_dualAnnihilator _).mp hl _ ⟨v,rfl⟩
    obtain ⟨k,hk⟩ := hm
    change c.param (x,k) = a at hk
    refine ⟨k,?_⟩
    apply LinearMap.ext
    intro v
    rw [ambientCovector_apply,hk]
    have hh := congrArg (fun L : Affine N →L[ℝ] ℝ => L v) ha
    change (a v).re = l v-b v at hh
    rw [hh]
    exact add_sub_cancel _ _

end ActualCriticalChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PrimeZeroLocusFixed
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

lemma parameterPeak_log_norm {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p z : Affine N}
    (hp : MvPolynomial.eval p P ≠ 0) (hz : MvPolynomial.eval z P ≠ 0) :
    Real.log ‖parameterPeak P a p z‖ =
      (parameterLogBase P z + (a z).re) - (parameterLogBase P p + (a p).re) - coordinateEnergy (z-p) := by
  rw [parameterPeak_norm,parameterPotential_eq_exp P a hz,parameterPotential_eq_exp P a hp,
    ← Real.exp_sub,← Real.exp_add,Real.log_exp]
  ring

lemma coordinateEnergy_sub_hasFDerivAt {N : ℕ} (p : Affine N) :
    HasFDerivAt (fun z => coordinateEnergy (z-p)) (0 : Affine N →L[ℝ] ℝ) p := by
  have h (i : Fin N) : HasFDerivAt (fun z : Affine N => ‖z i-p i‖^2) (0 : Affine N →L[ℝ] ℝ) p := by
    simpa using ((ContinuousLinearMap.proj i : Affine N →L[ℝ] ℂ).hasFDerivAt (x := p) |>.sub_const (p i)).norm_sq
  simpa only [coordinateEnergy,Pi.sub_apply,Finset.sum_const_zero,Finset.sum_apply] using
    HasFDerivAt.fun_sum (fun i (_hi : i ∈ Finset.univ) => h i)

theorem parameterPeak_log_norm_hasFDerivAt {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p : Affine N} (hp : MvPolynomial.eval p P ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖parameterPeak P a p z‖)
      (fderiv ℝ (parameterLogBase P) p + Complex.reCLM.comp (a.restrictScalars ℝ)) p := by
  have hb := (parameterLogBase_contDiffAt P hp (r := 1)).differentiableAt one_ne_zero
  have hd := ((hb.hasFDerivAt.add (Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).sub_const
    (parameterLogBase P p + (a p).re)).sub (coordinateEnergy_sub_hasFDerivAt p)
  simp only [sub_zero] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [(MvPolynomial.continuous_eval P).continuousAt.eventually_ne hp] with z hz
  exact parameterPeak_log_norm P a hp hz

theorem parameterPeak_log_differential {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p : Affine N} (hp : MvPolynomial.eval p P ≠ 0) :
    AnalyticAt ℂ (fun z => Complex.log (parameterPeak P a p z)) p ∧
      Complex.log (parameterPeak P a p p) = 0 ∧
      Complex.reCLM.comp ((fderiv ℂ (fun z => Complex.log (parameterPeak P a p z)) p).restrictScalars ℝ) =
        fderiv ℝ (parameterLogBase P) p + Complex.reCLM.comp (a.restrictScalars ℝ) := by
  have hs := parameterPeak_self P a hp
  have hh : AnalyticAt ℂ (fun z => Complex.log (parameterPeak P a p z)) p :=
    (parameterPeak_analytic P a p p (mem_univ _)).clog (hs ▸ Complex.one_mem_slitPlane)
  refine ⟨hh,by rw [hs,Complex.log_one],?_⟩
  have hr := Complex.reCLM.hasFDerivAt.comp p (hh.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have he : (fun z => (Complex.log (parameterPeak P a p z)).re) =
      (fun z => Real.log ‖parameterPeak P a p z‖) := funext (fun _ => Complex.log_re _)
  change HasFDerivAt (fun z => (Complex.log (parameterPeak P a p z)).re) _ p at hr
  rw [he] at hr
  exact hr.unique (parameterPeak_log_norm_hasFDerivAt P a hp)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VanishingIdealPrime
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric
open scoped Topology

theorem IsSmooth.identity_principle {n m : ℕ} {S : Set (Affine n)}
    (hs : IsSmooth S) (hc : IsPreconnected S) {f : S → Affine m}
    (hf : HolomorphicOnSubset S f) {p : S} (hp : f =ᶠ[𝓝 p] 0) :
    ∀ q, f q = 0 := by
  let A : Set S := interior {q | f q = 0}
  have hAo : IsOpen A := isOpen_interior
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro q hq
    obtain ⟨d,W,hWS,hWo,hqW,D,hD,⟨e⟩⟩ := hs q
    let g : D → S := Set.inclusion hWS ∘ e.toHomeomorph.symm
    have hg : Topology.IsOpenEmbedding g :=
      (Topology.IsOpenEmbedding.inclusion hWS hWo).comp e.toHomeomorph.symm.isOpenEmbedding
    let a : D := e.toHomeomorph ⟨q.val,hqW⟩
    have hga : g a = q := by simp [g,a,Set.inclusion]
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hD a.val a.property
    let B : Set D := Subtype.val ⁻¹' ball a.val r
    have hBo : IsOpen B := isOpen_ball.preimage continuous_subtype_val
    have haB : a ∈ B := mem_ball_self hr
    have hqg : q ∈ g '' B := hga ▸ mem_image_of_mem g haB
    obtain ⟨b,hbg,hbA⟩ := (_root_.mem_closure_iff.mp hq) (g '' B) (hg.isOpenMap _ hBo) hqg
    obtain ⟨y,hyB,hyb⟩ := hbg
    have hfy : f ∘ g =ᶠ[𝓝 y] 0 := by
      have hz : f =ᶠ[𝓝 b] 0 := mem_interior_iff_mem_nhds.mp hbA
      rw [← hyb] at hz
      exact hz.comp_tendsto hg.continuous.continuousAt.tendsto
    let F := ambientExtend (f ∘ g)
    have hF : AnalyticOnNhd ℂ F D :=
      ((hf.restrict hWS).comp e.holomorphic_invFun).analyticOnNhd_extend hD
    have hFy : F =ᶠ[𝓝 y.val] 0 := by
      rw [← hD.isOpenEmbedding_subtypeVal.map_nhds_eq y]
      change (fun t : D => F t.val) =ᶠ[𝓝 y] 0
      simpa only [F,ambientExtend_apply] using hfy
    have hzero := (hF.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball a.val r).isPreconnected hyB hFy
    apply ((hg.isOpenMap _ hBo).subset_interior_iff.mpr ?_) hqg
    rintro t ⟨z,hz,rfl⟩
    change f (g z) = 0
    have ht := hzero hz
    simpa only [F,ambientExtend_apply,Function.comp_apply,Pi.zero_apply] using ht
  let : PreconnectedSpace S := Subtype.preconnectedSpace hc
  have hpu : p ∈ A := mem_interior_iff_mem_nhds.mpr hp
  have hAu : A = univ := (show IsClopen A from ⟨hAc,hAo⟩).eq_univ ⟨p,hpu⟩
  intro q
  exact (interior_subset (s := {q | f q = 0})) (show q ∈ A by rw [hAu]; trivial)

end

open Set Filter
open scoped Topology

theorem IsSmooth.vanishingIdeal_isPrime {n : ℕ} {S : Set (Affine n)}
    (hs : IsSmooth S) (hc : IsConnected S) :
    (MvPolynomial.vanishingIdeal ℂ S).IsPrime := by
  constructor
  · intro htop
    obtain ⟨p,hp⟩ := hc.nonempty
    have he : (1 : MvPolynomial (Fin n) ℂ) ∈ MvPolynomial.vanishingIdeal ℂ S := by
      rw [htop]; trivial
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using he p hp)
  · intro P Q hPQ
    by_cases hP : P ∈ MvPolynomial.vanishingIdeal ℂ S
    · exact Or.inl hP
    right
    have hex : ∃ p ∈ S, MvPolynomial.eval p P ≠ 0 := by
      change ¬ ∀ p ∈ S, MvPolynomial.eval p P = 0 at hP
      push Not at hP
      exact hP
    obtain ⟨a,ha,haP⟩ := hex
    let p : S := ⟨a,ha⟩
    let f : S → Affine 1 := fun x _ => MvPolynomial.eval x.val Q
    have hf : HolomorphicOnSubset S f := by
      intro x
      refine ⟨univ,isOpen_univ,mem_univ _,fun z _ => MvPolynomial.eval z Q,?_,?_⟩
      · intro z _
        exact analyticAt_pi_iff.mpr fun _ => (AnalyticOnNhd.eval_mvPolynomial Q) z (mem_univ _)
      · intro y _; rfl
    have hn : ∀ᶠ x : S in 𝓝 p, MvPolynomial.eval x.val P ≠ 0 := by
      exact (P.continuous_eval.comp continuous_subtype_val).continuousAt.eventually_ne haP
    have hz : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hn] with x hx
      have hmul := hPQ x.val x.property
      have hQ : MvPolynomial.eval x.val Q = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hx
        simpa using hmul
      ext i
      exact hQ
    have hh := hs.identity_principle hc.isPreconnected hf hz
    intro x hx
    exact congrFun (hh ⟨x,hx⟩) 0

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentChartConormals
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_boundary_generic_fiber {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
      (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
      (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
        p.complexMap x ∈ closure U \ U ∧
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
          ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  have hsm := cocompact_bounded_affine_smooth V U hV hUV hU hc hb Γ hhol
  let I := MvPolynomial.vanishingIdeal ℂ U
  have : I.IsPrime := hsm.vanishingIdeal_isPrime hc
  have hIV : MvPolynomial.zeroLocus ℂ I ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro x hx
    rw [hR]
    intro p hp
    apply hx p
    intro y hy
    exact (hR ▸ hUV hy) p hp
  exact prime_boundary_generic_fiber I rfl (hU.preimage (continuous_inclusion hIV))
    hc.isPreconnected hn hb hs

theorem affine_conormal_pullback_range
    {E F X K : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup K] [Module ℝ K]
    (L : E →ₗ[ℝ] F) (hL : Function.Injective L) (M : X →ₗ[ℝ] E)
    (A : K →ᵃ[ℝ] Module.Dual ℝ F)
    (hA : range A = ((LinearMap.range (L.comp M)).dualAnnihilator : Set (Module.Dual ℝ F))) :
    range (L.dualMap.toAffineMap.comp A) =
      ((LinearMap.range M).dualAnnihilator : Set (Module.Dual ℝ E)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨k,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro y ⟨x,rfl⟩
    have ha : A k ∈ (LinearMap.range (L.comp M)).dualAnnihilator := by
      change A k ∈ ((LinearMap.range (L.comp M)).dualAnnihilator : Set (Module.Dual ℝ F))
      rw [← hA]
      exact mem_range_self k
    exact (Submodule.mem_dualAnnihilator _).mp ha _ ⟨x,rfl⟩
  · intro l hl
    obtain ⟨g,hg⟩ := LinearMap.dualMap_surjective_of_injective hL l
    have hgA : g ∈ (LinearMap.range (L.comp M)).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      rintro y ⟨x,rfl⟩
      have he := congrArg (fun f : Module.Dual ℝ E => f (M x)) hg
      change g (L (M x)) = l (M x) at he
      exact he.trans ((Submodule.mem_dualAnnihilator _).mp hl _ ⟨x,rfl⟩)
    have hgAr : g ∈ range A := hA.symm ▸ hgA
    obtain ⟨k,rfl⟩ := hgAr
    exact ⟨k,hg⟩

namespace ActualCriticalChart
variable {d m N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

theorem independent_chart_conormals (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    (L : Affine m →L[ℝ] Affine N) (hL : Function.Injective L)
    (M : (Fin d → ℝ) →L[ℝ] Affine m) (hM : L.comp M = fderiv ℝ q x)
    {S : Set (Fin c.fiberDim → ℝ)} (hS : volume S ≠ 0) :
    ∃ v : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator) →
        (Fin c.fiberDim → ℝ),
      (∀ i, v i ∈ S) ∧
      LinearIndependent ℝ (fun i => (c.ambientCovector x (v i)).comp L.toLinearMap) := by
  let W := (LinearMap.range M.toLinearMap).dualAnnihilator
  let A := L.toLinearMap.dualMap.toAffineMap.comp (c.ambientCovector x)
  have hA : range A = (W : Set (Module.Dual ℝ (Affine m))) := by
    apply affine_conormal_pullback_range L.toLinearMap hL M.toLinearMap (c.ambientCovector x)
    have he : L.toLinearMap.comp M.toLinearMap = (fderiv ℝ q x).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap hM
    rw [he]
    exact c.ambientCovector_range hx hq hP
  have hav (k : Fin c.fiberDim → ℝ) : A k ∈ W := by
    change A k ∈ (W : Set (Module.Dual ℝ (Affine m)))
    rw [← hA]
    exact mem_range_self k
  let A' := affineMapCodRestrict A W hav
  have hs : Function.Surjective A' := by
    intro l
    have hl : l.val ∈ range A := by rw [hA]; exact l.property
    obtain ⟨v,hv⟩ := hl
    exact ⟨v,Subtype.ext hv⟩
  obtain ⟨v,hv,hi⟩ := exists_independent_affine_images_of_positive_measure volume hS A' hs
  refine ⟨v,hv,?_⟩
  exact hi.map' W.subtype (Submodule.ker_subtype _)
end ActualCriticalChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EntireSupports
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical
namespace ActualCriticalChart
variable {d m N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

theorem entire_supports (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    {K : Set (Affine N)} (hpos : volume (Prod.mk x ⁻¹' c.maxLocus K) ≠ 0)
    (F : Affine m → Affine N) (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0)
    (hFi : Function.Injective (fderiv ℂ F 0))
    (M : (Fin d → ℝ) →L[ℝ] Affine m)
    (hM : ((fderiv ℂ F 0).restrictScalars ℝ).comp M = fderiv ℝ q x) :
    ∃ h : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator) →
        Affine N → ℂ,
      (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
      (∀ i, h i (q x) = 1) ∧
      (∀ i, ∀ z ∈ K, ‖h i z‖ ≤ Real.exp (-(dist z (q x))^2)) ∧
      (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
      LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
      ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp M = 0 := by
  let L := (fderiv ℂ F 0).restrictScalars ℝ
  obtain ⟨v,hv,hi⟩ := c.independent_chart_conormals hx hq hP L hFi M hM hpos
  let h (i : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator)) :=
    parameterPeak P (c.param (x,v i)) (q x)
  have hd (i) : (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap =
      (c.ambientCovector x (v i)).comp L.toLinearMap := by
    have hh := (parameterPeak_log_norm_hasFDerivAt P (c.param (x,v i)) hP)
    have hh' : HasFDerivAt (fun z => Real.log ‖h i z‖)
        (fderiv ℝ (parameterLogBase P) (q x) +
          Complex.reCLM.comp ((c.param (x,v i)).restrictScalars ℝ)) (F 0) := by simpa only [hF0,h] using hh
    have he := (hh'.comp 0 (hF.differentiableAt.hasFDerivAt.restrictScalars ℝ)).fderiv
    change (fderiv ℝ ((fun z => Real.log ‖h i z‖) ∘ F) 0).toLinearMap = _
    rw [he]
    ext z
    rfl
  refine ⟨h,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact parameterPeak_analytic _ _ _
  · intro i; exact parameterPeak_self _ _ hP
  · intro i
    exact parameterPeak_bound P (c.param (x,v i)) hP (hv i).2.2
  · intro i
    have hr := ((parameterPeak_log_differential P (c.param (x,v i)) hP).1)
    have hr' : AnalyticAt ℂ (fun z => Complex.log (h i z)) (F 0) := by simpa only [hF0,h] using hr
    exact hr'.comp hF
  · simpa only [hd] using hi
  · intro i
    have hdM : (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap.comp M.toLinearMap = 0 := by
      rw [hd,LinearMap.comp_assoc]
      have he : L.toLinearMap.comp M.toLinearMap = (fderiv ℝ q x).toLinearMap :=
        congrArg ContinuousLinearMap.toLinearMap hM
      rw [he]
      exact c.ambientCovector_comp hx hq hP (v i)
    ext z
    exact congrArg (fun f => f z) hdM
end ActualCriticalChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicSupportIndependent
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set
open scoped Classical

theorem complex_independent_of_generic_real_conormals
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype ι]
    (S : Set E) (hS : Submodule.span ℂ S = ⊤)
    (l : ι → E →ₗ[ℂ] ℂ)
    (hz : ∀ i, ∀ x ∈ S, (l i x).re = 0)
    (hi : LinearIndependent ℝ
      (fun i => Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ))) :
    LinearIndependent ℂ l := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let B : E →ₗ[ℂ] ℂ := ∑ i, (c i).im • l i
  have hBS : S ⊆ LinearMap.ker B := by
    intro x hx
    have hr : (B x).re = 0 := by
      simp [B,LinearMap.sum_apply,LinearMap.smul_apply,hz _ x hx]
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    have him : (B x).im = 0 := by
      simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.re_sum,
        Complex.mul_re,hz _ x hx,mul_zero,zero_sub,Finset.sum_neg_distrib,
        LinearMap.zero_apply,Complex.zero_re,neg_eq_zero] at hh
      simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,Complex.smul_im] using hh
    exact Complex.ext hr him
  have hB : B = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hS]
    exact Submodule.span_le.mpr hBS
  have hbi : ∑ i, (c i).im •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hB
    simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.smul_re] using hh
  have hci := Fintype.linearIndependent_iff.mp hi (fun i => (c i).im) hbi
  have hbr : ∑ i, (c i).re •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    simpa [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.mul_re,hci] using hh
  have hcr := Fintype.linearIndependent_iff.mp hi (fun i => (c i).re) hbr
  intro i
  exact Complex.ext (hcr i) (hci i)
end

open Set Filter Topology
open scoped Classical

theorem log_norm_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E → ℂ) {x : E} (ha : AnalyticAt ℂ (fun z => Complex.log (h z)) x) :
    fderiv ℝ (fun z => Real.log ‖h z‖) x =
      Complex.reCLM.comp ((fderiv ℂ (fun z => Complex.log (h z)) x).restrictScalars ℝ) := by
  have hr := Complex.reCLM.hasFDerivAt.comp x (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun z => (Complex.log (h z)).re) _ x at hr
  have he : (fun z => (Complex.log (h z)).re) = (fun z => Real.log ‖h z‖) :=
    funext (fun _ => Complex.log_re _)
  rw [he] at hr
  exact hr.fderiv

theorem holomorphic_support_independent {m d k : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] Affine m)
    (hM : Submodule.span ℂ (range M) = ⊤)
    (h : Fin k → Affine m → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i z)) 0)
    (hi : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).toLinearMap))
    (hz : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).comp M = 0) :
    LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i z)) 0).toLinearMap) := by
  apply complex_independent_of_generic_real_conormals (range M) hM
  · intro i y hy
    obtain ⟨v,rfl⟩ := hy
    have he := congrArg (fun f : (Fin d → ℝ) →L[ℝ] ℝ => f v) (hz i)
    rw [log_norm_fderiv _ (ha i)] at he
    exact he
  · have he (i) : Complex.reCLM.toLinearMap.comp
        (((fderiv ℂ (fun z => Complex.log (h i z)) 0).toLinearMap).restrictScalars ℝ) =
        (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).toLinearMap := by
      rw [log_norm_fderiv _ (ha i)]
      rfl
    simpa only [he] using hi
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellGeometricRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology

theorem real_parametric_span_eq_chart_of_rank_ge {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ (range (fderiv ℝ q x)) =
      LinearMap.range (fderiv ℂ F 0).toLinearMap := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  apply complex_tangent_eq_of_rank_ge (fderiv ℝ q x).toLinearMap
    (LinearMap.range (fderiv ℂ F 0).toLinearMap)
  · exact chart_tangent_finrank F G hF (hF0 ▸ hG) hGF
  · intro v
    have hv := real_derivative_mem_chart_tangent F G q (hG0 ▸ hF) hG hq hFG v
    change fderiv ℝ q x v ∈ _
    simpa only [hG0] using hv
  · rw [matrix_rank_eq_complex_tangent_dimension]
    rwa [coordinate_derivative_rank q hq] at hr

end

open Set Filter Topology MeasureTheory

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InjectiveConormalFinrank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem chart_tangent_identities {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) :
    G (q x) = 0 ∧
    (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ ∧
    ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ (G ∘ q) x) = fderiv ℝ q x ∧
    Function.Injective (fderiv ℂ F 0) := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have hg : AnalyticAt ℂ G (F 0) := hF0 ▸ hG
  have hid := (hg.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ := by
    simpa only [hF0] using hid.unique (hasFDerivAt_id (0 : Affine m))
  refine ⟨hG0,hi,?_,?_⟩
  · have hr : DifferentiableAt ℝ (G ∘ q) x := hG.differentiableAt.restrictScalars ℝ |>.comp x hq
    have hf : AnalyticAt ℂ F ((G ∘ q) x) := by simpa only [Function.comp_apply,hG0] using hF
    have hh := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFG.symm
    simpa only [Function.comp_apply,hG0] using he.fderiv.symm
  · intro a b hab
    have hh := congrArg (fderiv ℂ G (q x)) hab
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem chart_parametric_generic {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (G ∘ q) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x)) = ⊤ := by
  obtain ⟨hG0,hi,hd,hFi⟩ := chart_tangent_identities F G q hF0 hF hG hq hGF hFG
  have hspan := real_parametric_span_eq_chart_of_rank_ge F G q hF0 hF hG hq hGF hFG hr
  have hder : fderiv ℝ (G ∘ q) x = ((fderiv ℂ G (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hqi
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  · let W := Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x))
    have hle : Submodule.span ℂ (range (fderiv ℝ q x)) ≤
        W.comap (fderiv ℂ G (q x)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      change fderiv ℂ G (q x) (fderiv ℝ q x v) ∈ W
      have he : fderiv ℂ G (q x) (fderiv ℝ q x v) = fderiv ℝ (G ∘ q) x v := by
        rw [hder]; rfl
      rw [he]
      exact Submodule.subset_span (mem_range_self v)
    apply top_unique
    intro v _
    have hv : fderiv ℂ F 0 v ∈ Submodule.span ℂ (range (fderiv ℝ q x)) := by
      rw [hspan]; exact ⟨v,rfl⟩
    have hh := hle hv
    change fderiv ℂ G (q x) (fderiv ℂ F 0 v) ∈ W at hh
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem injective_conormal_finrank {d m : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] Affine m) (hM : Function.Injective M) :
    d + Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator = 2*m := by
  have hr : Module.finrank ℝ (LinearMap.range M.toLinearMap) = d := by
    simpa using LinearMap.finrank_range_of_inj (f := M.toLinearMap) hM
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range M.toLinearMap)
  simpa [hr,Affine,Module.finrank_pi_fintype,Nat.mul_comm] using h
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SmallSlopeGoodSupported
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_small_slope_good_supported_boundary_oai {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
          (F : Affine m → Affine n) (G : Affine n → Affine m)
          (h : Fin k → Affine n → ℂ),
          x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
          SmallSlopeGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U))
            p.val.domain p.val.complexMap x ∧
          1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
          F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
          AnalyticAt ℂ G (p.val.complexMap x) ∧
          (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
          (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
          (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
          Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
          (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
          (∀ i, h i (p.val.complexMap x) = 1) ∧
          (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
          (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
          LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
          LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
          ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0 := by
  obtain ⟨m,P,C,_hP,hC,he⟩ := original_boundary_generic_fiber V U hV hUV hU hc hn hb hs Γ hhol
  refine ⟨m,C,fun bad hbad => ?_⟩
  let I := MvPolynomial.vanishingIdeal ℂ U
  let E : ∀ p : C, Set (Fin p.val.dim → ℝ) := fun p =>
    {x | x ∈ p.val.domain ∧ m ≤ p.val.complexRank x ∧
      ¬ SmallSlopeGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ I) p.val.domain p.val.complexMap x}
  have hUV' : U ⊆ MvPolynomial.zeroLocus ℂ I := fun u hu P hP => hP u hu
  have hE : ∀ p : C, volume (E p) = 0 := by
    intro p
    exact p.val.null_nonsmallgood_generic U (MvPolynomial.zeroLocus ℂ I) hUV'
      (zeroLocus_closed I) (isSemialgebraic_zeroLocus I) hs ((hC p.val p.property).2)
  obtain ⟨p,c,x,hxp,hxc,hr,hPx,hxE,hpos⟩ :=
    he (fun p => bad p ∪ E p) (fun p => measure_union_null (hbad p) (hE p))
  have hxb : x ∉ bad p := fun h => hxE (Or.inl h)
  have hxgood : SmallSlopeGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ I) p.val.domain p.val.complexMap x := by
    by_contra h
    exact hxE (Or.inr ⟨hxp,hr,h⟩)
  obtain ⟨hpbd,W,hWI,hW,hpW,B,hB,⟨e⟩⟩ := (hC p.val p.property).2 x hxp
  obtain ⟨F,G,hF0,hF,hG,hGF,hFG,hFV⟩ := e.centered_chart_germs hWI hW hB hpW
  have hq := p.val.analytic_complexMap x hxp
  have hqi := p.val.injective_fderiv_complexMap hxp
  have hqV : ∀ᶠ y in 𝓝 x, p.val.complexMap y ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) := by
    filter_upwards [p.val.isOpen_domain.mem_nhds hxp] with y hy
    obtain ⟨_,W',hWI',_,hpW',_⟩ := (hC p.val p.property).2 y hy
    exact hWI' hpW'
  have hqn : ∀ᶠ y in 𝓝 x, p.val.complexMap y ∉ U := by
    filter_upwards [p.val.isOpen_domain.mem_nhds hxp] with y hy
    exact ((hC p.val p.property).2 y hy).1.2
  have ht : Tendsto p.val.complexMap (𝓝 x)
      (𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hFGq : (F ∘ G ∘ p.val.complexMap) =ᶠ[𝓝 x] p.val.complexMap := ht hFG
  obtain ⟨_hG0,_hGFd,hd,hFi⟩ := chart_tangent_identities F G p.val.complexMap hF0 hF hG hq.differentiableAt hGF hFGq
  obtain ⟨hMi,hMg⟩ := chart_parametric_generic F G p.val.complexMap hF0 hF hG hq.differentiableAt hqi hGF hFGq hr
  let M := fderiv ℝ (G ∘ p.val.complexMap) x
  let k := Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator
  have hdk : p.val.dim + k = 2*m := injective_conormal_finrank M hMi
  have hdl : p.val.dim < 2*m := boundary_parametric_dimension_lt
    (show U ⊆ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) from
      fun u hu P hP => hP u hu) F G p.val.complexMap hpbd.1 hF0 hF hG hq hqi hGF hFG hqV hqn
  obtain ⟨h,ha,hs,hnorm,hl,hi,hz⟩ := c.entire_supports hxc hq.differentiableAt hPx hpos F hF0 hF hFi M hd
  have hic := holomorphic_support_independent M hMg (fun i z => h i (F z)) hl hi hz
  have hkm : k ≤ m := by
    have hh := hic.fintype_card_le_finrank
    simpa [Affine] using hh
  exact ⟨p,x,k,F,G,h,hxp,hxb,hpbd,hxgood,by omega,hkm,hdk,hF0,hF,hG,hGF,hFG,hFV,hMg,ha,hs,hnorm,hl,hi,hic,hz⟩
end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.original_small_slope_good_supported_boundary_oai.{u_1} := @OAI.Release061.original_small_slope_good_supported_boundary_oai.{u_1}
