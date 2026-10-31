-- Prove2me | solution 1 for OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:00:43.611229+00:00
-- url     : https://prove2.me/submissions/020916ef-d1f0-4136-b992-d242aff39473

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakCompactness
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma exists_weak_cluster_of_mass_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} (hcur : ∀ j, IsMetricCurrent (Ts j))
    (M : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) :
    ∃ (l' : Filter ι), NeBot l' ∧ l' ≤ l ∧
      ∃ T : Functional X k, ∀ b π, Tendsto (fun j => Ts j b π) l' (𝓝 (T b π)) := by
  have hbound (b : X → ℝ) (π : Fin k → X → ℝ) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ j, |Ts j b π| ≤ R := by
    by_cases h : Admissible b π
    · choose Ks hKs using h.2
      obtain ⟨B, hB⟩ := h.1.2
      refine ⟨((∏ i, (Ks i : ℝ)) * max B 0) * M, by positivity, ?_⟩
      intro j
      refine ((hcur j).mass_bound_uniform h.1 Ks hKs
        (fun x => (hB x).trans (le_max_left B 0))).trans ?_
      exact mul_le_mul_of_nonneg_left (hM j) (by positivity)
    · exact ⟨0, le_rfl, fun j => by rw [(hcur j).offDomain b π h, abs_zero]⟩
  choose R _ hR using hbound
  let C : Set (Functional X k) := {U | ∀ b π, U b π ∈ Icc (-R b π) (R b π)}
  have hC : IsCompact C :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  have hTsC (j : ι) : Ts j ∈ C := fun b π => abs_le.mp (hR b π j)
  obtain ⟨T, _, hcluster⟩ := hC.exists_mapClusterPt_of_frequently (l := l)
    (Eventually.of_forall hTsC).frequently
  let l' := comap Ts (𝓝 T) ⊓ l
  have hl' : NeBot l' := neBot_inf_comap_iff_map'.mpr hcluster
  have hT : Tendsto Ts l' (𝓝 T) := tendsto_iff_comap.mpr inf_le_left
  exact ⟨l', hl', inf_le_right, T, fun b π =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT b) π⟩

lemma exists_normal_weak_cluster_of_integral_mass_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1 + 1)}
    (hTs : ∀ j, IsIntegral (k + 1 + 1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N) :
    ∃ (l' : Filter ι), NeBot l' ∧ l' ≤ l ∧
      ∃ T : Functional X (k + 1 + 1), IsMetricCurrent T ∧
        IsMetricCurrent (boundarySucc T) ∧ mass T ≤ M ∧
        mass (boundarySucc T) ≤ N ∧
        ∀ b π, Tendsto (fun j => Ts j b π) l' (𝓝 (T b π)) := by
  obtain ⟨l', hl', hle, T, hlim⟩ := exists_weak_cluster_of_mass_bound
    (l := l) (fun j => (hTs j).1) M hM
  let := hl'
  obtain ⟨hT, hbd⟩ := normal_of_bounded_integral_weak_limit hTs M N hM hN hlim
  refine ⟨l', hl', hle, T, hT, hbd, ?_, ?_, hlim⟩
  · exact mass_le_of_bounded_weak_limit M (fun j => (hTs j).1) hM (fun b π _ => hlim b π)
  · exact mass_le_of_bounded_weak_limit N (fun j => (hTs j).2.2.1) hN
      (fun b π _ => boundarySucc_weak_limit hlim b π)

end Foundations

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CountableTests
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma exists_normal_weak_subsequence_of_integral_mass_bound
    {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
    (hTs : ∀ j, IsIntegral (k+1+1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ T : Functional X (k+1+1), IsMetricCurrent T ∧
        IsMetricCurrent (boundarySucc T) ∧ mass T ≤ M ∧
        mass (boundarySucc T) ≤ N ∧
        ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π)) := by
  obtain ⟨l, hl, hle, T, hT, hbd, hTM, hTN, hlim⟩ :=
    exists_normal_weak_cluster_of_integral_mass_bound (l := atTop) hTs M N hM hN
  let := hl
  have hsep (K : ℕ) : ∃ D : ℕ → TestClass (X := X) (k+1+1) K, DenseRange D :=
    TopologicalSpace.exists_dense_seq _
  choose D hD using hsep
  let evaluations (U : Functional X (k+1+1)) : (ℕ × ℕ) → ℝ :=
    fun ij => TestClass.eval U (D ij.1 ij.2)
  have heval : Tendsto (fun j => evaluations (Ts j)) l (𝓝 (evaluations T)) :=
    tendsto_pi_nhds.mpr fun ij => hlim _ _
  obtain ⟨ψ, hψ, hψlim⟩ := (heval.mapClusterPt.mono hle).tendsto_subseq
  refine ⟨ψ, hψ, T, hT, hbd, hTM, hTN, ?_⟩
  have hall (K : ℕ) (p : TestClass (X := X) (k+1+1) K) :
      Tendsto (fun j => TestClass.eval (Ts (ψ j)) p) atTop (𝓝 (TestClass.eval T p)) := by
    let C : ℝ≥0 := (K : ℝ≥0) ^ (k+1+1) * M +
      (k+1+1) * ((K : ℝ≥0) + K) ^ (k+1) * (K * N + K * M)
    have hL (j : ℕ) : LipschitzWith C (TestClass.eval (K := K) (Ts j)) := by
      simpa [C, Nat.cast_add, Nat.cast_one] using IntegerRectifiable.testClass_lipschitz (hTs j).2.1 (hTs j).1 (hTs j).2.2.1 M N
        (hM j) (hN j) K
    have hLlim : LipschitzWith C (TestClass.eval (K := K) T) :=
      lipschitz_of_pointwise_limit (l := l) hL (fun q => hlim q.val.1 (fun i => q.val.2 i))
    apply tendsto_of_lipschitz_dense (fun j => hL (ψ j)) hLlim (hD K) _ p
    intro i
    exact tendsto_pi_nhds.mp hψlim (K, i)
  intro b π
  by_cases hadm : Admissible b π
  · obtain ⟨K, p, hp₁, hp₂⟩ := admissible_mem_testClass hadm
    simpa only [TestClass.eval, hp₁, hp₂] using hall K p
  · have heq : (fun j => Ts (ψ j) b π) = fun _ => 0 :=
      funext fun j => (hTs (ψ j)).1.offDomain b π hadm
    rw [heq, hT.offDomain b π hadm]
    exact tendsto_const_nhds

end Foundations
end CAT0Fillings

namespace CAT0Fillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_countable_current_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, Admissible (b K j) (π K j)) ∧
      ∀ S T : Functional X d, IsMetricCurrent S → IsMetricCurrent T →
        (∀ K j, S (b K j) (π K j) = T (b K j) (π K j)) → S = T := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.1,fun K j i => (p K j).val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  · intro S T hS hT heq
    have he (K : ℕ) : TestClass.eval (K := K) S = TestClass.eval (K := K) T := by
      apply (hp K).equalizer (IsMetricCurrent.testClass_continuous hS K) (IsMetricCurrent.testClass_continuous hT K)
      funext j
      exact heq K j
    funext b π
    by_cases h : Admissible b π
    · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass h
      have hh := congrFun (he K) q
      simpa only [TestClass.eval,hb,hπ] using hh
    · rw [hS.offDomain b π h,hT.offDomain b π h]

theorem ae_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {d : ℕ} {S T : A → Functional X d}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, S a b π = T a b π) :
    ∀ᵐ a ∂μ, S a = T a := by
  obtain ⟨b,π,ha,hex⟩ := exists_countable_current_tests (X := X) d
  have hc : ∀ᵐ a ∂μ, ∀ K j, S a (b K j) (π K j) = T a (b K j) (π K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  exact hex _ _ hs ht h

end CAT0Fillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_BorelAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}

lemma borelAction_congr_ae (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hbc : b =ᵐ[μ] c) (π : Fin k → X → ℝ) :
    borelAction μ hT b π = borelAction μ hT c π := by
  by_cases hb : Integrable b μ
  · have hc := hb.congr hbc
    by_cases hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)
    · rw [borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
        (Integrable.toL1_eq_toL1_iff b c hb hc).mpr hbc]
    · simp only [borelAction, dite_eq_left hb, dite_eq_left hc, dite_eq_right hπ]
  · have hc : ¬Integrable c μ := fun hc => hb (hc.congr hbc.symm)
    simp only [borelAction, dite_eq_right hb, dite_eq_right hc]

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Poincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {ν : Measure E} [IsFiniteMeasure ν]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [IsFiniteMeasure ν] in
lemma convolution_direction_bound {f η : E → ℝ} (hf : LocallyIntegrable f μ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x)
    {v : E} (hv : DirectionalVariation f v μ ν) (z : E) :
    |((f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ η) z) v| ≤
      ∫ x, η (z-x) ∂ν := by
  let φ : E → ℝ := fun x => η (z-x)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hη.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have hd (x : E) : fderiv ℝ φ x = -(fderiv ℝ η (z-x)) := by
    have hh := ((hη.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (z-x)).hasFDerivAt.comp x
      ((hasFDerivAt_const z x).sub (hasFDerivAt_id x))
    simpa [φ,Function.comp_def] using hh.fderiv
  have hb := hv φ hφ hcφ
  simp only [hd,neg_apply,neg_mul,integral_neg,abs_neg] at hb
  have he : (fun x => |φ x|) = (fun x => η (z-x)) := by
    funext x
    exact abs_of_nonneg (hη0 _)
  rw [he] at hb
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
    (hη.continuous_fderiv (by simp)), convolution_def]
  simpa only [lsmul_apply,smul_eq_mul,mul_comm] using hb

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma continuous_kernelIntegral {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) : Continuous (fun z => ∫ x, η (z-x) ∂ν) := by
  obtain ⟨C,hbound⟩ := hη.bounded_above_of_compact_support hc
  exact continuous_of_dominated (bound := fun _ => C)
    (fun z => ((hη.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (fun z => ae_of_all _ fun x => hbound (z-x)) (integrable_const C)
    (ae_of_all _ fun x => hη.comp (continuous_id.sub continuous_const))

lemma kernelIntegral_ball_bound {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) (hint : ∫ x, η x ∂μ = 1)
    {ε : ℝ} (hs : Function.support η ⊆ closedBall 0 ε) (a : E) (r : ℝ) :
    (∫ z in closedBall a r, ∫ x, η (z-x) ∂ν ∂μ) ≤ ν.real (closedBall a (r+ε)) := by
  let Q := closedBall a r
  let A := closedBall a (r+ε)
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by simp [Q,measure_closedBall_lt_top]⟩
  obtain ⟨C,hC⟩ := hη.bounded_above_of_compact_support hc
  have hp : Integrable (fun p : E × E => η (p.1-p.2)) ((μ.restrict Q).prod ν) :=
    Integrable.of_bound (hη.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable C
      (ae_of_all _ fun p => hC _)
  have hfub := integral_integral_swap (f := fun z x => η (z-x)) hp
  change (∫ z, ∫ x, η (z-x) ∂ν ∂μ.restrict Q) ≤ _
  rw [hfub]
  have hz (x : E) : Integrable (fun z => η (z-x)) μ := by
    exact (hη.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.subRight x))
  have hpoint (x : E) : (∫ z in Q, η (z-x) ∂μ) ≤ A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      calc _ ≤ ∫ z, η (z-x) ∂μ := setIntegral_le_integral (hz x) (ae_of_all _ fun z => hη0 _)
        _ = 1 := by rw [integral_sub_right_eq_self, hint]
    · rw [indicator_of_notMem hx]
      have he : ∀ z ∈ Q, η (z-x) = 0 := by
        intro z hz
        by_contra hn
        have hn' : z-x ∈ closedBall 0 ε := hs hn
        have hd : dist x a ≤ r+ε := calc
          dist x a ≤ dist x z + dist z a := dist_triangle _ _ _
          _ ≤ ε + r := add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hn') hz
          _ = r+ε := add_comm _ _
        exact hx hd
      rw [setIntegral_congr_fun measurableSet_closedBall he,integral_zero]
  have hm := integral_mono hp.integral_prod_right
    ((integrable_const (1:ℝ) : Integrable (fun _ : E => (1:ℝ)) ν).indicator measurableSet_closedBall)
    hpoint
  exact hm.trans_eq (by rw [integral_indicator measurableSet_closedBall]; simp)

lemma euclidean_opNorm_le_coordinate_bound {k : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |L (EuclideanSpace.basisFun (Fin k) ℝ i)| ≤ B) : ‖L‖ ≤ k*B := by
  apply L.opNorm_le_bound (by positivity)
  intro x
  have he := congrArg L ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x)
  rw [map_sum] at he
  rw [←he]
  calc _ ≤ ∑ i : Fin k, ‖L (((EuclideanSpace.basisFun (Fin k) ℝ).repr x).ofLp i •
        EuclideanSpace.basisFun (Fin k) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, ‖x‖*B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [map_smul,norm_smul]
      apply mul_le_mul _ (hb i) (abs_nonneg _) (norm_nonneg _)
      simpa using (PiLp.norm_apply_le ((EuclideanSpace.basisFun (Fin k) ℝ).repr x) i)
    _ = k*B*‖x‖ := by simp; ring

lemma mollified_gradient_integral_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {m : Measure (EuclideanSpace ℝ (Fin k))} [m.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : LocallyIntegrable f m)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) m ν)
    (η : ContDiffBump (0 : EuclideanSpace ℝ (Fin k))) (a : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    (∫ z in closedBall a r,
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
        fderiv ℝ (η.normed m)) z‖ ∂m) ≤ k * ν.real (closedBall a (r+η.rOut)) := by
  have hc := η.hasCompactSupport_normed (μ := m)
  have hd := (η.contDiff_normed (μ := m) (n := (⊤ : ℕ∞))).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := (hc.fderiv ℝ).continuous_convolution_right
    ((lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k))) hf hd
  have hb (z : EuclideanSpace ℝ (Fin k)) :
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
          fderiv ℝ (η.normed m)) z‖ ≤ k * ∫ x, η.normed m (z-x) ∂ν := by
    apply euclidean_opNorm_le_coordinate_bound _ (integral_nonneg fun x => η.nonneg_normed _)
    intro i
    exact convolution_direction_bound hf η.contDiff_normed hc η.nonneg_normed (hv i) z
  have hk := (continuous_kernelIntegral (ν := ν) η.continuous_normed hc).const_mul (k:ℝ)
  have hm := integral_mono
    (hg.norm.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r))
    (hk.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r)) hb
  rw [integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (kernelIntegral_ball_bound η.continuous_normed hc η.nonneg_normed η.integral_normed
      (by rw [η.support_normed_eq]; exact ball_subset_closedBall) a r) (Nat.cast_nonneg k))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal Pointwise

noncomputable section
namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma setIntegral_translate (g : E → ℝ) (v : E) (s : Set E) :
    (∫ x in s, g (x+v) ∂μ) = ∫ x in (fun x => x+v) '' s, g x ∂μ := by
  let e := (Homeomorph.addRight v).toMeasurableEquiv
  have hmap : Measure.map e μ = μ := (measurePreserving_add_right μ v).map_eq
  have hpre : e ⁻¹' (e '' s) = s := e.injective.preimage_image s
  have hh := setIntegral_map_equiv (μ := μ) e g (e '' s)
  rw [hmap,hpre] at hh
  exact hh.symm

lemma affine_ball_integral_le {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a y : E} {r t : ℝ} (hy : y ∈ closedBall a r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    (∫ x in closedBall a r, g ((1-t) • x + t • y) ∂μ) ≤
      (2:ℝ)^Module.finrank ℝ E * ∫ x in closedBall a r, g x ∂μ := by
  have hR : 0 < 1-t := by linarith
  let s : Set E := (1-t) • closedBall a r
  let A : Set E := (fun x => x + t • y) '' s
  have hsub : A ⊆ closedBall a r := by
    rintro z ⟨w,⟨x,hx,rfl⟩,rfl⟩
    exact convex_closedBall a r hx hy (by linarith) ht0 (by ring)
  have he : (∫ x in closedBall a r, g ((1-t) • x+t • y) ∂μ) =
      ((1-t)^Module.finrank ℝ E)⁻¹ * ∫ x in A, g x ∂μ := by
    rw [Measure.setIntegral_comp_smul_of_pos μ (fun x => g (x+t • y)) _ hR,
      setIntegral_translate]
    rfl
  have hi : IntegrableOn g (closedBall a r) μ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall a r) hg.continuousOn
  have hm : (∫ x in A, g x ∂μ) ≤ ∫ x in closedBall a r, g x ∂μ :=
    setIntegral_mono_set hi (ae_of_all _ hg0) (ae_of_all _ hsub)
  have hc : ((1-t)^Module.finrank ℝ E)⁻¹ ≤ (2:ℝ)^Module.finrank ℝ E := by
    rw [←inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hR.le)
    apply (inv_le_comm₀ hR (by norm_num : (0:ℝ) < 2)).mpr
    norm_num
    linarith
  rw [he]
  exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (pow_nonneg hR.le _))).trans
    (mul_le_mul_of_nonneg_right hc (integral_nonneg hg0))

omit [MeasurableSpace E] [BorelSpace E] in
lemma halfMean_continuous {g : E → ℝ} (hg : Continuous g) :
    Continuous (fun p : E × E => halfMean g p.1 p.2) := by
  exact continuous_parametric_integral_of_continuous
    (by change Continuous (fun p : (E × E) × ℝ => g ((1-p.2) • p.1.1+p.2 • p.1.2)); fun_prop)
    isCompact_Icc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma halfMean_nonneg {g : E → ℝ} (hg0 : ∀ x, 0 ≤ g x) (x y : E) :
    0 ≤ halfMean g x y := integral_nonneg fun _ => hg0 _

lemma halfMean_integral_le {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a y : E} {r : ℝ} (hy : y ∈ closedBall a r) :
    (∫ x in closedBall a r, halfMean g x y ∂μ) ≤
      (1/2:ℝ)*(2:ℝ)^Module.finrank ℝ E * ∫ x in closedBall a r, g x ∂μ := by
  have hi : Integrable (fun p : E × ℝ => g ((1-p.2) • p.1+p.2 • y))
      ((μ.restrict (closedBall a r)).prod (volume.restrict (Icc 0 (1/2)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact ((isCompact_closedBall a r).prod isCompact_Icc)
      (by fun_prop)
  simp only [halfMean]
  rw [integral_integral_swap hi]
  apply le_trans (setIntegral_mono_on hi.integral_prod_right (integrableOn_const measure_Icc_lt_top.ne)
    measurableSet_Icc (fun t ht => affine_ball_integral_le hg hg0 hy ht.1 ht.2))
  simp only [integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num
  ring_nf
  exact le_rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma half_segment_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (x y : E) :
    |f x-f ((1/2:ℝ) • x+(1/2:ℝ) • y)| ≤ ‖y-x‖*halfMean (fun z => ‖f' z‖) x y := by
  let p (t : ℝ) := (1-t) • x+t • y
  have hp (t : ℝ) : HasDerivAt p (y-x) t := by
    convert (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const x).add
      ((hasDerivAt_id t).smul_const y) using 1 <;> first | (with_reducible_and_instances rfl) | (simp [p,sub_eq_add_neg,add_comm,Pi.add_def])
  have hder (t : ℝ) := (hf (p t)).comp_hasDerivAt t (hp t)
  have hc : Continuous (fun t => f' (p t) (y-x)) := by dsimp [p]; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1/2) (fun t _ => hder t) (hc.intervalIntegrable _ _)
  have hp0 : p 0 = x := by simp [p]
  have hp1 : p (1/2) = (1/2:ℝ) • x+(1/2:ℝ) • y := by norm_num [p]
  change (∫ t in (0:ℝ)..1/2, f' (p t) (y-x)) = f (p (1/2))-f (p 0) at hint
  rw [hp0,hp1] at hint
  rw [abs_sub_comm,←hint]
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ) ≤ 1/2)).trans
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1/2)
    (hc.abs.intervalIntegrable _ _)
    ((show Continuous (fun t : ℝ => ‖y-x‖*‖f' (p t)‖) by dsimp [p]; fun_prop).intervalIntegrable _ _)
    (fun t _ => by simpa only [Real.norm_eq_abs,mul_comm] using (f' (p t)).le_opNorm (y-x))
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
    ←integral_Icc_eq_integral_Ioc]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma segment_pair_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f')
    {a x y : E} {r : ℝ} (hx : x ∈ closedBall a r) (hy : y ∈ closedBall a r) :
    |f x-f y| ≤ 2*r*(halfMean (fun z => ‖f' z‖) x y + halfMean (fun z => ‖f' z‖) y x) := by
  have h1 := half_segment_bound hf hf' x y
  have h2 := half_segment_bound hf hf' y x
  have hd : ‖y-x‖ ≤ 2*r := by
    rw [←dist_eq_norm]
    exact (dist_triangle y a x).trans (by rw [dist_comm a x]; linarith [mem_closedBall.mp hy,mem_closedBall.mp hx])
  have hs : ‖x-y‖ = ‖y-x‖ := norm_sub_rev _ _
  have he : (1/2:ℝ) • y+(1/2:ℝ) • x = (1/2:ℝ) • x+(1/2:ℝ) • y := add_comm _ _
  rw [he,hs] at h2
  have ht := abs_sub_le (f x) (f ((1/2:ℝ) • x+(1/2:ℝ) • y)) (f y)
  rw [abs_sub_comm (f ((1/2:ℝ) • x+(1/2:ℝ) • y)) (f y)] at ht
  calc _ ≤ ‖y-x‖*(halfMean (fun z => ‖f' z‖) x y + halfMean (fun z => ‖f' z‖) y x) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (add_nonneg (halfMean_nonneg (fun _ => norm_nonneg _) x y)
      (halfMean_nonneg (fun _ => norm_nonneg _) y x))

theorem smooth_ball_poincare {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (a : E) {r : ℝ} (hr : 0 < r) :
    (∫ x in closedBall a r, |f x-(⨍ y in closedBall a r, f y ∂μ)| ∂μ) ≤
      2*(2:ℝ)^Module.finrank ℝ E*r*∫ x in closedBall a r, ‖f' x‖ ∂μ := by
  let Q := closedBall a r
  let H := halfMean (fun z => ‖f' z‖)
  let J := ∫ x in Q, ‖f' x‖ ∂μ
  let A := (1/2:ℝ)*(2:ℝ)^Module.finrank ℝ E*J
  have hQ : IsCompact Q := isCompact_closedBall a r
  have hQm : MeasurableSet Q := hQ.measurableSet
  have hQ0 : 0 < μ.real Q := ENNReal.toReal_pos
    (ne_of_gt ((measure_ball_pos μ a hr).trans_le (measure_mono ball_subset_closedBall)))
    measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hQ.measure_lt_top⟩
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hH : Continuous (fun p : E × E => H p.1 p.2) := halfMean_continuous hf'.norm
  have hHI : Integrable (fun p : E × E => H p.1 p.2) ((μ.restrict Q).prod (μ.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (hQ.prod hQ) hH.continuousOn
  have hPI : Integrable (fun p : E × E => |f p.1-f p.2|) ((μ.restrict Q).prod (μ.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (hQ.prod hQ) (by fun_prop)
  have hHbound : (∫ x in Q, ∫ y in Q, H x y ∂μ ∂μ) ≤ μ.real Q*A := by
    rw [integral_integral_swap hHI]
    apply le_trans (setIntegral_mono_on hHI.integral_prod_right (integrable_const A)
      hQm (fun y hy => halfMean_integral_le hf'.norm (fun _ => norm_nonneg _) hy))
    simp [integral_const,smul_eq_mul]
  have hdouble : (∫ x in Q, ∫ y in Q, |f x-f y| ∂μ ∂μ) ≤ 4*r*(μ.real Q*A) := by
    have hpoint (x : E) (hx : x ∈ Q) :
        (∫ y in Q, |f x-f y| ∂μ) ≤ 2*r*((∫ y in Q, H x y ∂μ)+(∫ y in Q, H y x ∂μ)) := by
      have hi1 : IntegrableOn (fun y => H x y) Q μ :=
        ContinuousOn.integrableOn_compact hQ (hH.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hi2 : IntegrableOn (fun y => H y x) Q μ :=
        ContinuousOn.integrableOn_compact hQ (hH.comp (continuous_id.prodMk continuous_const)).continuousOn
      rw [←integral_add hi1 hi2,←integral_const_mul]
      exact setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hQ (by fun_prop)) ((hi1.add hi2).const_mul _) hQm
        (fun y hy => segment_pair_bound hf hf' hx hy)
    have hh := setIntegral_mono_on hPI.integral_prod_left
      ((hHI.integral_prod_left.add hHI.integral_prod_right).const_mul (2*r)) hQm hpoint
    rw [integral_const_mul] at hh
    simp only [Pi.add_apply] at hh
    rw [integral_add hHI.integral_prod_left hHI.integral_prod_right] at hh
    have hswap := integral_integral_swap (f := fun x y => H x y) hHI
    rw [←hswap] at hh
    exact hh.trans (by nlinarith)
  have hfi : IntegrableOn f Q μ := ContinuousOn.integrableOn_compact hQ hfc.continuousOn
  have hmean (x : E) :
      |f x-(⨍ y in Q, f y ∂μ)| ≤ (μ.real Q)⁻¹*∫ y in Q, |f x-f y| ∂μ := by
    have he : f x-(⨍ y in Q, f y ∂μ) = (μ.real Q)⁻¹*∫ y in Q, f x-f y ∂μ := by
      rw [integral_sub (integrable_const (f x)) hfi,integral_const,setAverage_eq]
      simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
      field_simp [show (μ Q).toReal ≠ 0 from hQ0.ne']
    rw [he,abs_mul,abs_of_nonneg (inv_nonneg.mpr hQ0.le)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hQ0.le)
  have hosc := setIntegral_mono_on
    (ContinuousOn.integrableOn_compact hQ (hfc.sub continuous_const).abs.continuousOn)
    (hPI.integral_prod_left.const_mul ((μ.real Q)⁻¹)) hQm (fun x _ => hmean x)
  rw [integral_const_mul] at hosc
  apply (hosc.trans (mul_le_mul_of_nonneg_left hdouble (inv_nonneg.mpr hQ0.le))).trans_eq
  dsimp [A,J]
  have hn : μ.real Q ≠ 0 := hQ0.ne'
  change (μ.real Q)⁻¹*(4*r*(μ.real Q*((1/2:ℝ)*2^Module.finrank ℝ E*(∫ x in Q, ‖f' x‖ ∂μ)))) = _
  field_simp [hn]
  ring

end CAT0Fillings.JointBV

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Oscillation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma abs_setAverage_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs0 : 0 < μ.real s) (hsf : μ s ≠ ∞)
    {f : α → ℝ} (hf : IntegrableOn f s μ) (c : ℝ) :
    |(⨍ z in s, f z ∂μ) - c| ≤ (μ.real s)⁻¹ * ∫ z in s, |f z - c| ∂μ := by
  have hs : μ s ≠ 0 := by
    intro h
    simp [measureReal_def, h] at hs0
  have : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hsf.lt_top⟩
  have hi : IntegrableOn (fun z => f z - c) s μ := hf.sub (integrable_const c)
  have he : (⨍ z in s, f z ∂μ) - c =
      (μ.real s)⁻¹ * ∫ z in s, f z - c ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const]
    simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def] at *
    rw [setAverage_eq]
    simp only [smul_eq_mul, measureReal_def]
    field_simp
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs0.le)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hs0.le)

lemma abs_setAverage_sub_le_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (hst : s ⊆ t)
    (hs0 : 0 < μ.real s) (htf : μ t ≠ ∞)
    {f : α → ℝ} (hf : IntegrableOn f t μ) (c : ℝ) :
    |(⨍ z in s, f z ∂μ) - c| ≤ (μ.real s)⁻¹ * ∫ z in t, |f z - c| ∂μ := by
  have hsf : μ s ≠ ∞ := ne_of_lt ((measure_mono hst).trans_lt htf.lt_top)
  have : IsFiniteMeasure (μ.restrict t) := ⟨by simpa using htf.lt_top⟩
  apply (abs_setAverage_sub_le hs0 hsf (hf.mono_set hst) c).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs0.le)
  simpa only [Measure.restrict_restrict hs, inter_eq_left.mpr hst, Pi.sub_apply] using
    setIntegral_le_integral (s := s) (hf.sub (integrable_const c)).abs
      (ae_of_all _ fun point => abs_nonneg (f point - c))

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [BorelSpace E] in
lemma haar_closedBall_pos {x : E} {r : ℝ} (hr : 0 < r) :
    0 < μ.real (closedBall x r) := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall))
  · exact measure_closedBall_lt_top.ne

lemma haar_closedBall_scale (x y : E) {r : ℝ} (hr : 0 < r) (a : ℝ) (ha : 0 ≤ a) :
    μ.real (closedBall x (a * r)) = a ^ Module.finrank ℝ E * μ.real (closedBall y r) := by
  rw [Measure.addHaar_real_closedBall _ _ (mul_nonneg ha hr.le),
    Measure.addHaar_real_closedBall _ _ hr.le, mul_pow, mul_assoc]

lemma average_half_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : r ≤ R) :
    |(⨍ z in closedBall x (r / 2), f z ∂μ) -
      (⨍ z in closedBall x r, f z ∂μ)| ≤
      (2 : ℝ) ^ Module.finrank ℝ E * A * r := by
  have hrh : 0 < r / 2 := by positivity
  have hs0 := haar_closedBall_pos (μ := μ) (x := x) hrh
  have hI := hf.integrableOn_isCompact (isCompact_closedBall x r)
  have hsub : closedBall x (r / 2) ⊆ closedBall x r :=
    closedBall_subset_closedBall (by linarith)
  apply (abs_setAverage_sub_le_integral isClosed_closedBall.measurableSet hsub
    hs0 measure_closedBall_lt_top.ne hI _).trans
  have he : μ.real (closedBall x r) =
      (2 : ℝ) ^ Module.finrank ℝ E * μ.real (closedBall x (r / 2)) := by
    have hh := haar_closedBall_scale (μ := μ) x x hrh 2 (by norm_num)
    rwa [show 2 * (r / 2) = r by ring] at hh
  calc
    _ ≤ (μ.real (closedBall x (r / 2)))⁻¹ * (A * r * μ.real (closedBall x r)) :=
      mul_le_mul_of_nonneg_left (hA r hr hrR) (inv_nonneg.mpr hs0.le)
    _ = (2 : ℝ) ^ Module.finrank ℝ E * A * r := by rw [he]; field_simp

lemma point_average_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : r ≤ R)
    (hlim : Tendsto (fun n : ℕ => ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ)
      atTop (𝓝 (f x))) :
    |f x - (⨍ z in closedBall x r, f z ∂μ)| ≤
      2 * (2 : ℝ)^Module.finrank ℝ E * A * r := by
  let a (n : ℕ) := ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ
  let D := (2 : ℝ)^Module.finrank ℝ E * A * r
  have hstep (n : ℕ) : dist (a n) (a (n+1)) ≤ D * (1 / 2 : ℝ)^n := by
    have hrn : 0 < r * (1 / 2 : ℝ)^n := by positivity
    have hrnR : r * (1 / 2 : ℝ)^n ≤ R := by
      apply le_trans _ hrR
      exact mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
    have hh := average_half_bound hf hA hrn hrnR
    have he : r * (1 / 2 : ℝ)^n / 2 = r * (1 / 2 : ℝ)^(n+1) := by
      rw [pow_succ]; ring
    rw [he] at hh
    change |a n - a (n+1)| ≤ _
    rw [abs_sub_comm]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [a, D]
    ring
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hh := dist_le_tsum_of_dist_le_of_tendsto₀ _ hstep (hg.mul_left D) hlim
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1 / 2 : ℝ) < 1)] at hh
  norm_num only [one_div, inv_inv] at hh
  simpa only [a, pow_zero, mul_one, Real.dist_eq, abs_sub_comm, D, mul_comm, mul_left_comm,
    mul_assoc] using hh

lemma average_neighbor_bound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A : ℝ} {x y : E} {R r : ℝ} (hA : LocalMeanBound (μ := μ) f A x R)
    (hr : 0 < r) (hrR : 2 * r ≤ R) (hxy : dist y x ≤ r) :
    |(⨍ z in closedBall y r, f z ∂μ) -
      (⨍ z in closedBall x (2 * r), f z ∂μ)| ≤
      2 * (2 : ℝ) ^ Module.finrank ℝ E * A * r := by
  have hs0 := haar_closedBall_pos (μ := μ) (x := y) hr
  have hI := hf.integrableOn_isCompact (isCompact_closedBall x (2*r))
  have hsub : closedBall y r ⊆ closedBall x (2*r) := by
    intro z hz
    change dist z x ≤ 2 * r
    have hh := dist_triangle z y x
    have hz' : dist z y ≤ r := hz
    linarith
  apply (abs_setAverage_sub_le_integral isClosed_closedBall.measurableSet hsub
    hs0 measure_closedBall_lt_top.ne hI _).trans
  have he := haar_closedBall_scale (μ := μ) x y hr 2 (by norm_num)
  calc
    _ ≤ (μ.real (closedBall y r))⁻¹ * (A * (2*r) * μ.real (closedBall x (2*r))) :=
      mul_le_mul_of_nonneg_left (hA (2*r) (by positivity) hrR) (inv_nonneg.mpr hs0.le)
    _ = 2 * (2 : ℝ)^Module.finrank ℝ E * A * r := by
      rw [he]; field_simp

lemma ae_ballAverage_tendsto {f : E → ℝ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ)
      (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average hf] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt μ x)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma dyadic_closedBall_average_tendsto {f : E → ℝ} {x : E}
    (hx : Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ)
      (𝓝[>] 0) (𝓝 (f x))) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ⨍ z in closedBall x (r * (1 / 2 : ℝ)^n), f z ∂μ)
      atTop (𝓝 (f x)) := by
  apply hx.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds (x := r)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1))
  · exact Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity

lemma abs_sub_le_of_localMeanBound {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {A R : ℝ} {x y : E}
    (hAx : LocalMeanBound (μ := μ) f A x R)
    (hAy : LocalMeanBound (μ := μ) f A y R)
    (hx : Tendsto (fun r : ℝ => ⨍ z in closedBall x r, f z ∂μ) (𝓝[>] 0) (𝓝 (f x)))
    (hy : Tendsto (fun r : ℝ => ⨍ z in closedBall y r, f z ∂μ) (𝓝[>] 0) (𝓝 (f y)))
    (hxy : 2 * dist x y ≤ R) :
    |f x - f y| ≤ 8 * (2 : ℝ)^Module.finrank ℝ E * A * dist x y := by
  by_cases he : x = y
  · simp [he]
  have hr : 0 < dist x y := dist_pos.mpr he
  have hrR : dist x y ≤ R := by linarith
  have hx' := point_average_bound hf hAx (show 0 < 2 * dist x y by positivity) hxy
    (dyadic_closedBall_average_tendsto hx (by positivity))
  have hy' := point_average_bound hf hAy hr hrR (dyadic_closedBall_average_tendsto hy hr)
  have hc := average_neighbor_bound hf hAx hr hxy (by rw [dist_comm])
  have htri : |f x - f y| ≤
      |f x - (⨍ z in closedBall x (2 * dist x y), f z ∂μ)| +
      |(⨍ z in closedBall y (dist x y), f z ∂μ) -
        (⨍ z in closedBall x (2 * dist x y), f z ∂μ)| +
      |f y - (⨍ z in closedBall y (dist x y), f z ∂μ)| := by
    simpa only [Real.dist_eq, abs_sub_comm] using
      dist_triangle4 (f x) (⨍ z in closedBall x (2 * dist x y), f z ∂μ)
        (⨍ z in closedBall y (dist x y), f z ∂μ) (f y)
  linarith

end Euclidean
end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma integral_abs_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {F : ℕ → α → ℝ} (hf : Integrable f μ) (hF : ∀ j, Integrable (F j) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x))) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ j in atTop, (∫ x, |F j x| ∂μ) ≤ C) : (∫ x, |f x| ∂μ) ≤ C := by
  have hl' : ∀ᵐ x ∂μ, Tendsto (fun j => ENNReal.ofReal |F j x|) atTop
      (𝓝 (ENNReal.ofReal |f x|)) := hl.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx.abs
  have hfat : (∫⁻ x, ENNReal.ofReal |f x| ∂μ) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop := by
    calc _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal |F j x|) atTop ∂μ :=
        lintegral_congr_ae (hl'.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun j => (hF j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hu : liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [hbound] with j hj
    rw [←ofReal_integral_eq_lintegral_ofReal (hF j).abs (ae_of_all _ fun x => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hj
  rw [←ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun x => abs_nonneg _)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hfat.trans hu)

lemma pair_integral_le_oscillation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ) (c : ℝ) :
    (∫ p : α × α, |f p.1-f p.2| ∂μ.prod μ) ≤ 2*μ.real univ*(∫ x, |f x-c| ∂μ) := by
  have hi := (hf.sub (integrable_const c)).abs
  have hp := (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hm := integral_mono hp.abs ((hi.comp_fst μ).add (hi.comp_snd μ)) (fun p => by
    have ht := abs_sub_le (f p.1) c (f p.2)
    rwa [abs_sub_comm c (f p.2)] at ht)
  simp only [Pi.add_apply,Pi.sub_apply] at hm hi hp
  rw [integral_add (hi.comp_fst μ) (hi.comp_snd μ),integral_prod _ (hi.comp_fst μ),
    integral_prod _ (hi.comp_snd μ)] at hm
  simp only [integral_const,smul_eq_mul,integral_const_mul] at hm
  exact hm.trans_eq (by ring)

lemma oscillation_le_pair_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (hμ : 0 < μ.real univ) {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x-(⨍ y, f y ∂μ)| ∂μ) ≤
      (μ.real univ)⁻¹*(∫ p : α × α, |f p.1-f p.2| ∂μ.prod μ) := by
  have hp := ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hpoint (x : α) : |f x-(⨍ y, f y ∂μ)| ≤ (μ.real univ)⁻¹*∫ y, |f x-f y| ∂μ := by
    have hh := abs_setAverage_sub_le (s := univ) hμ (measure_ne_top _ _) (by simpa using hf) (f x)
    simpa [abs_sub_comm] using hh
  have hm := integral_mono (hf.sub (integrable_const _)).abs
    (hp.integral_prod_left.const_mul ((μ.real univ)⁻¹)) hpoint
  rw [integral_const_mul,←integral_prod _ hp] at hm
  exact hm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem ball_poincare_of_smooth_approx {f : E → ℝ} (hf : LocallyIntegrable f μ)
    (F : ℕ → E → ℝ) (F' : ℕ → E → E →L[ℝ] ℝ)
    (hF : ∀ j x, HasFDerivAt (F j) (F' j x) x) (hF' : ∀ j, Continuous (F' j))
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (a : E) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hgrad : ∀ᶠ j in atTop, (∫ x in closedBall a r, ‖F' j x‖ ∂μ) ≤ B) :
    (∫ x in closedBall a r, |f x-(⨍ y in closedBall a r, f y ∂μ)| ∂μ) ≤
      4*(2:ℝ)^Module.finrank ℝ E*r*B := by
  let Q := closedBall a r
  let m := μ.restrict Q
  have hQ : IsCompact Q := isCompact_closedBall a r
  have hm : 0 < m.real univ := by simpa [m,measureReal_restrict_apply_univ] using
    (haar_closedBall_pos (μ := μ) (x := a) hr)
  have : IsFiniteMeasure m := ⟨by simpa [m] using hQ.measure_lt_top⟩
  have hfi : Integrable f m := hf.integrableOn_isCompact hQ
  have hFi (j : ℕ) : Integrable (F j) m := ContinuousOn.integrableOn_compact hQ
    (continuous_iff_continuousAt.mpr (fun x => (hF j x).continuousAt)).continuousOn
  have hlm : ∀ᵐ x ∂m, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := ae_restrict_of_ae hl
  have hlp : ∀ᵐ p : E × E ∂m.prod m,
      Tendsto (fun j => F j p.1-F j p.2) atTop (𝓝 (f p.1-f p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlm,Measure.quasiMeasurePreserving_snd.ae hlm]
      with p h1 h2 using h1.sub h2
  have hpair : (∫ p : E × E, |f p.1-f p.2| ∂m.prod m) ≤
      m.real univ*(4*(2:ℝ)^Module.finrank ℝ E*r*B) := by
    apply integral_abs_le_of_ae_tendsto ((hfi.comp_fst m).sub (hfi.comp_snd m))
      (fun j => ((hFi j).comp_fst m).sub ((hFi j).comp_snd m)) hlp (by positivity)
    filter_upwards [hgrad] with j hj
    have hp := pair_integral_le_oscillation (hFi j) (⨍ y, F j y ∂m)
    have hs := smooth_ball_poincare (μ := μ) (hF j) (hF' j) a hr
    have hc : 0 ≤ 2*(2:ℝ)^Module.finrank ℝ E*r := by positivity
    have hbound := hs.trans (mul_le_mul_of_nonneg_left hj hc)
    change (∫ x, |F j x-(⨍ y, F j y ∂m)| ∂m) ≤ _ at hbound
    exact hp.trans ((mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq (by ring))
  have ho := oscillation_le_pair_integral hm hfi
  change (∫ x, |f x-(⨍ y, f y ∂m)| ∂m) ≤ _
  apply (ho.trans (mul_le_mul_of_nonneg_left hpair (inv_nonneg.mpr hm.le))).trans_eq
  rw [←mul_assoc,inv_mul_cancel₀ hm.ne',one_mul]

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Approximation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_const_coord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, π i x = c) : borelAction μ hT f π = 0 := by
  simpa using borelAction_locality_mul μ hT hμ hf (BoundedLip.const 1) π hπ
    ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_lipschitz {c ε : ℝ} {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : LipschitzWith K (levelClamp c ε u) :=
  (hu.const_min (c + ε)).const_max (c - ε)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_eq {c ε : ℝ} {u : X → ℝ} {x : X} (h : |u x - c| < ε) :
    levelClamp c ε u x = u x := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  dsimp [levelClamp]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_tendsto (c : ℝ) (u : X → ℝ) (x : X) :
    Tendsto (fun n : ℕ => levelClamp c (1 / (n + 1)) u x) atTop (𝓝 c) := by
  have hd : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds.sub hd :
      Tendsto (fun n : ℕ => c - 1 / (n + 1 : ℝ)) atTop (𝓝 (c - 0))))
    (by simpa using (tendsto_const_nhds.add hd :
      Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) atTop (𝓝 (c + 0))))
  · intro n
    dsimp [levelClamp]
    simpa only [one_div] using (le_max_left (c - 1 / (n + 1 : ℝ)) (min (c + 1 / (n + 1 : ℝ)) (u x)))
  · intro n
    simp only [levelClamp, one_div]
    apply max_le _ (min_le_left _ _)
    have h : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    simpa only [one_div] using (show c - 1 / (n + 1 : ℝ) ≤ c + 1 / (n + 1 : ℝ) by linarith)

lemma borelAction_eq_levelClamp (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) {ε : ℝ} (hε : 0 < ε) :
    borelAction μ hT f π =
      borelAction μ hT f (Function.update π i (levelClamp c ε (π i))) := by
  classical
  obtain ⟨K, hK⟩ := hπ i
  let v := levelClamp c ε (π i)
  let w : X → ℝ := fun x => π i x - v x
  let ζ : X → ℝ := fun x => max 0 (ε - dist (π i x) c)
  have hv : LipschitzWith K v := levelClamp_lipschitz hK
  have hw : ∃ L : ℝ≥0, LipschitzWith L w := ⟨K + K, hK.sub hv⟩
  have hζ : BoundedLip ζ := by
    apply Foundations.boundedLip_of_lipschitz
    have hd : LipschitzWith K (fun x => dist (π i x) c) :=
      by simpa only [one_mul, Function.comp_def] using (LipschitzWith.dist_left c).comp hK
    simpa using ((LipschitzWith.const ε).sub hd).const_max 0
  let ρ := Function.update π i w
  have hρ : ∀ j, ∃ L : ℝ≥0, LipschitzWith L (ρ j) := by
    intro j
    by_cases hji : j = i
    · simpa [ρ, hji] using hw
    · simpa [ρ, Function.update_of_ne hji] using hπ j
  have hz : borelAction μ hT (fun x => f x * ζ x) ρ = 0 := by
    apply borelAction_locality_mul μ hT hμ hf hζ ρ hρ
    refine ⟨i, {x | dist (π i x) c < ε}, 0,
      isOpen_lt (hK.continuous.dist continuous_const) continuous_const, ?_, ?_⟩
    · intro x hx
      change max 0 (ε - dist (π i x) c) ≠ 0 at hx
      change dist (π i x) c < ε
      by_contra h
      exact hx (max_eq_left (by linarith [le_of_not_gt h]))
    · intro x hx
      simp only [ρ, Function.update_self]
      change π i x - levelClamp c ε (π i) x = 0
      rw [levelClamp_eq (by simpa [Real.dist_eq] using hx), sub_self]
  have heq : (fun x => f x * ζ x) = ε • f := by
    funext x
    by_cases hfx : f x = 0
    · simp [hfx]
    · simp [ζ, hc x hfx, max_eq_right hε.le, mul_comm]
  rw [heq, borelAction_smul μ hT hf ρ ε hρ] at hz
  have hzero : borelAction μ hT f ρ = 0 := (mul_eq_zero.mp hz).resolve_left hε.ne'
  have hlin := borelAction_linearCoord μ hT hμ hf π hπ i v ⟨K, hv⟩ 1 (-1)
  have hform : Function.update π i (fun x => 1 * π i x + -1 * v x) = ρ := by
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rfl
  rw [hform, hzero] at hlin
  linarith

theorem borelAction_locality_level (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) : borelAction μ hT f π = 0 := by
  classical
  let πs (n : ℕ) := Function.update π i (levelClamp c (1 / (n + 1)) (π i))
  let π₀ := Function.update π i (fun _ => c)
  have hLip : ∀ j, ∃ K : ℝ≥0, ∀ n, LipschitzWith K (πs n j) := by
    intro j
    by_cases hji : j = i
    · obtain ⟨K,hK⟩ := hπ i
      exact ⟨K, fun _ => by simpa [πs, hji] using levelClamp_lipschitz hK⟩
    · obtain ⟨K,hK⟩ := hπ j
      exact ⟨K, fun _ => by simpa [πs, Function.update_of_ne hji] using hK⟩
  have hpt : ∀ j x, Tendsto (fun n => πs n j x) atTop (𝓝 (π₀ j x)) := by
    intro j x
    by_cases hji : j = i
    · simpa [πs, π₀, hji] using levelClamp_tendsto c (π i) x
    · simp [πs, π₀, Function.update_of_ne hji]
  have hlim := borelAction_sequentialContinuity μ hT hμ hf π₀ πs hLip hpt
  have heq (n : ℕ) : borelAction μ hT f (πs n) = borelAction μ hT f π :=
    (borelAction_eq_levelClamp μ hT hμ hf π hπ i c hc (by positivity)).symm
  simp only [heq] at hlim
  have heq' := tendsto_nhds_unique hlim (tendsto_const_nhds)
  have hπ₀ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π₀ j) := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, by simp [π₀, hji]⟩
    · simpa [π₀, Function.update_of_ne hji] using hπ j
  rw [← heq']
  exact borelAction_const_coord μ hT hμ hf π₀ hπ₀ i c (by simp [π₀])

theorem borelAction_congr_coord_on_support (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k)
    (u : X → ℝ) (hu : ∃ K : ℝ≥0, LipschitzWith K u)
    (heq : ∀ x, f x ≠ 0 → π i x = u x) :
    borelAction μ hT f π = borelAction μ hT f (Function.update π i u) := by
  classical
  obtain ⟨K,hK⟩ := hπ i
  obtain ⟨L,hL⟩ := hu
  let ρ := Function.update π i (fun x => π i x - u x)
  have hρ : ∀ j, ∃ M : ℝ≥0, LipschitzWith M (ρ j) := by
    intro j
    by_cases hj : j = i
    · exact ⟨K + L, by simpa [ρ, hj] using hK.sub hL⟩
    · simpa [ρ, Function.update_of_ne hj] using hπ j
  have hz := borelAction_locality_level μ hT hμ hf ρ hρ i 0
    (fun x hx => by simp [ρ, heq x hx])
  have hl := borelAction_linearCoord μ hT hμ hf π hπ i u ⟨L,hL⟩ 1 (-1)
  have hform : Function.update π i (fun x => 1 * π i x + -1 * u x) = ρ := by
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rfl
  rw [hform, hz] at hl
  linarith

end CAT0Fillings.BorelCoefficients
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
variable {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [Nonempty Y]

omit [SeparableSpace Y] [Nonempty Y] in
lemma metricCone_lipschitz (φ : Y → ℝ) (K : ℝ≥0) (q : Y) :
    LipschitzWith K (metricCone φ K q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [metricCone,Real.dist_eq,add_sub_add_left_eq_sub,←mul_sub,
    abs_mul,abs_of_nonneg K.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y q) K.coe_nonneg

lemma metricConeApprox_lipschitz (φ : Y → ℝ) (K : ℝ≥0) (n : ℕ) :
    LipschitzWith K (metricConeApprox φ K n) := by
  induction n with
  | zero => exact metricCone_lipschitz φ K _
  | succ n ih => simpa only [metricConeApprox,max_self] using ih.min (metricCone_lipschitz φ K _)

lemma le_metricConeApprox {φ : Y → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (n : ℕ) (x : Y) :
    φ x ≤ metricConeApprox φ K n x := by
  induction n with
  | zero => exact hφ.le_add_mul _ _
  | succ n ih => exact le_min ih (hφ.le_add_mul _ _)

lemma metricConeApprox_antitone (φ : Y → ℝ) (K : ℝ≥0) (x : Y) :
    Antitone (fun n => metricConeApprox φ K n x) :=
  antitone_nat_of_succ_le fun _ => min_le_left _ _

lemma metricConeApprox_le_cone (φ : Y → ℝ) (K : ℝ≥0) {n m : ℕ} (hm : m ≤ n) (x : Y) :
    metricConeApprox φ K n x ≤ metricCone φ K (denseSeq Y m) x := by
  apply (metricConeApprox_antitone φ K x hm).trans
  cases m with
  | zero => exact le_rfl
  | succ m => exact min_le_right _ _

lemma metricConeApprox_tendsto {φ : Y → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (x : Y) :
    Tendsto (fun n => metricConeApprox φ K n x) atTop (𝓝 (φ x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (le_metricConeApprox hφ n x)
  · intro b hb
    have hD : 0 < 2*(K : ℝ)+1 := by positivity
    obtain ⟨m,hm⟩ := (denseRange_denseSeq Y).exists_dist_lt x (div_pos (sub_pos.mpr hb) hD)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hcone := metricConeApprox_le_cone φ K hn x
    have hq := hφ.le_add_mul (denseSeq Y m) x
    rw [dist_comm (denseSeq Y m) x] at hq
    have hdist : dist x (denseSeq Y m) < (b-φ x)/(2*(K : ℝ)+1) := by
      simpa only [dist_comm] using hm
    have hsmall := (lt_div_iff₀ hD).mp hdist
    dsimp only [metricCone] at hcone
    nlinarith [dist_nonneg (x := x) (y := denseSeq Y m)]

variable {X : Type*} [MetricSpace X]

lemma LipLattice.pi_dist {m : ℕ} {P : (X → ℝ) → Prop} (hP : LipLattice P)
    {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ i, P (fun x => u x i)) (q : Fin m → ℝ) :
    P (fun x => dist (u x) q) := by
  classical
  have hcoord (i : Fin m) : LipschitzWith L (fun x => u x i) :=
    (LipschitzWith.eval i).comp hu |>.weaken (by simp)
  have habs (i : Fin m) : P (fun x => |u x i-q i|) := by
    have hp := hP.linear ⟨L,hcoord i⟩ ⟨0,LipschitzWith.const _⟩ (hgen i) (hP.const (q i)) 1 (-1)
    have hn := hP.linear ⟨L,hcoord i⟩ ⟨0,LipschitzWith.const _⟩ (hgen i) (hP.const (q i)) (-1) 1
    have hp' : P (fun x => u x i-q i) := by simpa only [one_mul,neg_mul,one_mul,sub_eq_add_neg] using hp
    have hn' : P (fun x => -(u x i-q i)) := by convert hn using 1; funext x; ring
    have hsub : LipschitzWith L (fun x => u x i-q i) := by
      simpa only [add_zero] using (hcoord i).sub (LipschitzWith.const (q i))
    convert hP.max ⟨L,hsub⟩ ⟨L,hsub.neg⟩ hp' hn' using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact abs_eq_max_neg
  have hs (s : Finset (Fin m)) :
      P (fun x => ((s.sup fun i => nndist (u x i) (q i) : ℝ≥0) : ℝ)) ∧
        LipschitzWith L (fun x => ((s.sup fun i => nndist (u x i) (q i) : ℝ≥0) : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simpa using And.intro (hP.const 0) ((LipschitzWith.const (0:ℝ)).weaken (by positivity))
    | @insert i s hi ih =>
      have hl : LipschitzWith L (fun x => (nndist (u x i) (q i) : ℝ)) :=
        by simpa only [one_mul,Function.comp_def,coe_nndist] using (LipschitzWith.dist_left (q i)).comp (hcoord i)
      have hp : P (fun x => (nndist (u x i) (q i) : ℝ)) := by
        simpa only [coe_nndist,Real.dist_eq] using habs i
      simpa only [Finset.sup_insert, NNReal.coe_max,max_self] using
        And.intro (hP.max ⟨L,hl⟩ ⟨L,ih.2⟩ hp ih.1) (hl.max ih.2)
  simpa only [dist_pi_def] using (hs Finset.univ).1

lemma LipLattice.comp_pi {m : ℕ} {P : (X → ℝ) → Prop} (hP : LipLattice P)
    {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ i, P (fun x => u x i)) {φ : (Fin m → ℝ) → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) : P (fun x => φ (u x)) := by
  have hc (q : Fin m → ℝ) : P (fun x => metricCone φ K q (u x)) := by
    have hp := hP.linear ⟨0,LipschitzWith.const (φ q)⟩ ⟨L,by simpa only [one_mul,Function.comp_def,coe_nndist] using (LipschitzWith.dist_left q).comp hu⟩
      (hP.const (φ q)) (hP.pi_dist hu hgen q) 1 K
    simpa only [one_mul,metricCone] using hp
  have hs : ∀ n, P (fun x => metricConeApprox φ K n (u x)) := by
    intro n
    induction n with
    | zero => exact hc _
    | succ n ih =>
      exact hP.min ⟨K*L,(metricConeApprox_lipschitz φ K n).comp hu⟩
        ⟨K*L,(metricCone_lipschitz φ K _).comp hu⟩ ih (hc _)
  exact hP.limit hs (fun n => (metricConeApprox_lipschitz φ K n).comp hu)
    (fun x => metricConeApprox_tendsto hφ (u x))

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Carriers
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.BorelRestriction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}

lemma restrictCurrent_controls_original (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : Controls (restrictCurrent hT E) (currentMassMeasure hT) := by
  intro b π hb hπ
  exact (restrictCurrent_controls hT hE b π hb hπ).trans
    (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => abs_nonneg _) (integrable_boundedLip _ hb).abs)

lemma borelAction_restriction (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {f : X → ℝ} (hf : Integrable f (currentMassMeasure hT))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction (currentMassMeasure hT) (restrictCurrent_isMetricCurrent hT hE) f π =
      borelAction (currentMassMeasure hT) hT (E.indicator f) π := by
  let μ := currentMassMeasure hT
  let hR := restrictCurrent_isMetricCurrent hT hE
  have hc := restrictCurrent_controls_original hT hE
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hlim := borelAction_tendsto μ hR hc hf (fun n => integrable_boundedLip μ (g n).property) hg π hπ
  have hind : Tendsto (fun n => ∫ x, |E.indicator (g n).val x - E.indicator f x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hg
    apply integral_mono ((integrable_boundedLip μ (g n).property).indicator hE |>.sub (hf.indicator hE) |>.abs)
      ((integrable_boundedLip μ (g n).property).sub hf).abs
    intro x
    by_cases hx : x ∈ E
    · simp only [Pi.sub_apply,indicator_of_mem hx,le_refl]
    · simp only [Pi.sub_apply,indicator_of_notMem hx,sub_self,abs_zero]
      exact abs_nonneg _
  have hlim' := borelAction_tendsto μ hT (currentMassMeasure_controls hT) (hf.indicator hE)
    (fun n => (integrable_boundedLip μ (g n).property).indicator hE) hind π hπ
  have he (n : ℕ) : borelAction μ hR (g n).val π = borelAction μ hT (E.indicator (g n).val) π := by
    rw [borelAction_eq μ hR hc ⟨(g n).property,hπ⟩,restrictCurrent_apply hT E ⟨(g n).property,hπ⟩]
  simp only [he] at hlim
  exact tendsto_nhds_unique hlim hlim'

lemma restrictCurrent_restrict (hT : IsMetricCurrent T) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    restrictCurrent (restrictCurrent_isMetricCurrent hT hE) F = restrictCurrent hT (E ∩ F) := by
  let hR := restrictCurrent_isMetricCurrent hT hE
  have hμR : currentMassMeasure hR ≤ currentMassMeasure hT :=
    currentMassMeasure_le hR (restrictCurrent_controls_original hT hE)
  funext b π
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hR F hab,restrictCurrent_apply hT (E∩F) hab,
      borelAction_independent _ hR (currentMassMeasure_controls hR)
        (restrictCurrent_controls_original hT hE)
        ((integrable_boundedLip _ hab.1).indicator hF)
        ((integrable_boundedLip _ hab.1).indicator hF) π hab.2,
      borelAction_restriction hT hE ((integrable_boundedLip _ hab.1).indicator hF) π hab.2]
    congr 1
    ext x
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE,hxF]
  · simp only [restrictCurrent,ite_eq_right hab]

lemma restrictCurrent_eq_self_of_mass_compl_zero (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) (hμ : currentMassMeasure hT Eᶜ = 0) : restrictCurrent hT E = T := by
  funext b π
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hT E hab]
    have he : E.indicator b =ᵐ[currentMassMeasure hT] b := by
      filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, x ∈ E from
        (ae_mem_iff_measure_eq hE.nullMeasurableSet).mpr (by
          simpa only [hμ,add_zero] using
            measure_add_measure_compl (μ := currentMassMeasure hT) hE)] with x hx
      exact indicator_of_mem hx _
    rw [borelAction_congr_ae _ hT he,borelAction_eq _ hT (currentMassMeasure_controls hT) hab]
  · simp only [restrictCurrent,ite_eq_right hab,hT.offDomain b π hab]

lemma massMeasure_restrict_compl_zero (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) Eᶜ = 0 := by
  rw [restriction_massMeasure hT hE,Measure.restrict_apply hE.compl,compl_inter_self,measure_empty]

end CAT0Fillings.BorelRestriction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma borelAction_mul_zero_of_lip {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0)
    {f : X → ℝ} (hf : Integrable f (currentMassMeasure hT))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction (currentMassMeasure hT) hT (fun x => w x * f x) π = 0 := by
  let μ := currentMassMeasure hT
  obtain ⟨B,hB⟩ := hw.2
  have hbnd : ∀ᵐ x ∂μ, ‖w x‖ ≤ B := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hB x
  have hfi : Integrable (fun x => w x * f x) μ := by
    simpa only [mul_comm] using hf.mul_bdd hw.continuous.aestronglyMeasurable hbnd
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hgi n : Integrable (fun x => w x * (g n).val x) μ :=
    integrable_boundedLip μ (hw.mul (g n).property)
  have hlim : Tendsto (fun n => ∫ x, |w x * (g n).val x - w x * f x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hg.const_mul B)
    rw [←integral_const_mul]
    apply integral_mono ((hgi n).sub hfi).abs (((integrable_boundedLip μ (g n).property).sub hf).abs.const_mul B)
    intro x
    change |w x * (g n).val x - w x * f x| ≤ B * |(g n).val x - f x|
    rw [←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
  have ht := borelAction_tendsto μ hT (currentMassMeasure_controls hT) hfi hgi hlim π hπ
  have he n : borelAction μ hT (fun x => w x * (g n).val x) π = 0 := by
    rw [borelAction_eq μ hT (currentMassMeasure_controls hT) ⟨hw.mul (g n).property,hπ⟩]
    exact hz _ _ ⟨(g n).property,hπ⟩
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma massMeasure_nonzero_zero_of_mul_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0) :
    currentMassMeasure hT {x | w x ≠ 0} = 0 := by
  let E (n : ℕ) : Set X := {x | 1 / (n+1:ℝ) ≤ |w x|}
  have hE n : MeasurableSet (E n) := measurableSet_le measurable_const hw.continuous.abs.measurable
  have hzero n : restrictCurrent hT (E n) = 0 := by
    funext b π
    by_cases hab : Admissible b π
    · obtain ⟨B,hB⟩ := hab.1.2
      let f : X → ℝ := (E n).indicator (fun x => b x / w x)
      have hfm : Measurable f := (hab.1.continuous.measurable.div hw.continuous.measurable).indicator (hE n)
      have hfB x : ‖f x‖ ≤ max B 0 * (n+1:ℝ) := by
        by_cases hx : x ∈ E n
        · have hw0 : 0 < |w x| := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(n+1:ℝ)) hx
          simp only [f,indicator_of_mem hx,Real.norm_eq_abs,abs_div]
          apply (div_le_iff₀ hw0).mpr
          have hc : (1:ℝ) ≤ (n+1:ℝ)*|w x| := by
            simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mp hx
          calc |b x| ≤ max B 0 := (hB x).trans (le_max_left _ _)
            _ ≤ max B 0 * ((n+1:ℝ)*|w x|) := le_mul_of_one_le_right (le_max_right _ _) hc
            _ = _ := by ring
        · simp only [f,indicator_of_notMem hx,norm_zero]
          positivity
      have hfi : Integrable f (currentMassMeasure hT) :=
        (integrable_const (max B 0 * (n+1:ℝ))).mono' hfm.aestronglyMeasurable (Eventually.of_forall hfB)
      rw [restrictCurrent_apply hT (E n) hab]
      have he : (E n).indicator b = fun x => w x * f x := by
        funext x
        by_cases hx : x ∈ E n
        · have hw0 : w x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(n+1:ℝ)) hx)
          simp only [f,indicator_of_mem hx]
          field_simp
        · simp [f,hx]
      rw [he]
      exact borelAction_mul_zero_of_lip hT hw hz hfi π hab.2
    · simp [restrictCurrent,hab]
  have hμ n : currentMassMeasure hT (E n) = 0 := by
    have hm := restriction_mass hT (hE n)
    rw [hzero n] at hm
    have hm0 : mass (0 : Functional X k) = 0 := mass_zero k
    rw [hm0] at hm
    exact (ENNReal.toReal_eq_zero_iff _).mp hm.symm |>.resolve_right (measure_ne_top _ _)
  have hsub : {x | w x ≠ 0} ⊆ ⋃ n, E n := by
    intro x hx
    have hw0 : 0 < |w x| := abs_pos.mpr hx
    obtain ⟨n,hn⟩ := exists_nat_gt (1/|w x|)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change 1 / (n+1:ℝ) ≤ |w x|
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    have hh := (div_lt_iff₀ hw0).mp hn
    nlinarith
  exact measure_mono_null hsub (measure_iUnion_null fun n => hμ n)

lemma mul_action_zero_of_massMeasure_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    T (fun x => w x * b x) π = 0 := by
  have he : (fun x => w x * b x) =ᵐ[currentMassMeasure hT] 0 := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    simp [hx]
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩,
    borelAction_congr_ae _ hT he,borelAction_of_integrable _ hT (integrable_zero X ℝ _) π hab.2]
  simp

lemma boundary_mul_zero_of_massMeasure {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc T (fun x => w x * b x) π = 0 := by
  let E : Set X := {x | w x = 0}
  have hE : MeasurableSet E := hw.continuous.measurable (measurableSet_singleton 0)
  have he : (fun _ : X => (1:ℝ)) =ᵐ[currentMassMeasure hT] E.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    exact (indicator_of_mem (show x ∈ E from hx) (fun _ : X => (1:ℝ))).symm
  let σ := Matrix.vecCons (fun x => w x * b x) π
  have hσ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (σ j) :=
    fun j => Fin.cases (hw.mul hab.1).1 (fun i => hab.2 i) j
  rw [boundarySucc,ite_eq_left ⟨hw.mul hab.1,hab.2⟩]
  change T (fun _ => 1) σ = 0
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨BoundedLip.const 1,hσ⟩,
    borelAction_congr_ae _ hT he]
  apply borelAction_locality_level _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1:ℝ)).indicator hE) σ hσ 0 0
  intro x hx
  have hxE : x ∈ E := mem_of_indicator_ne_zero hx
  change w x * b x = 0
  rw [show w x = 0 from hxE,zero_mul]

lemma massMeasure_boundary_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hB {x | w x ≠ 0} = 0 := by
  apply massMeasure_nonzero_zero_of_mul_zero hB hw
  intro b π hab
  exact boundary_mul_zero_of_massMeasure hT hw hz hab

lemma massMeasure_restrict_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {w : X → ℝ} (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) {x | w x ≠ 0} = 0 := by
  rw [restriction_massMeasure hT hE]
  exact le_antisymm ((Measure.restrict_le_self _).trans_eq hz) bot_le

lemma massMeasure_superlevelSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    (hS : IsMetricCurrent (superlevelSlice hT hB u t))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hS {x | w x ≠ 0} = 0 := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hBT := massMeasure_boundary_nonzero_zero hT hB hw hz
  have hRT := massMeasure_restrict_nonzero_zero hT hE hz
  have hRB := massMeasure_restrict_nonzero_zero hB hE hBT
  apply massMeasure_nonzero_zero_of_mul_zero hS hw
  intro b π hab
  change restrictCurrent hB _ (fun x => w x * b x) π -
    boundarySucc (restrictCurrent hT _) (fun x => w x * b x) π = 0
  rw [mul_action_zero_of_massMeasure_nonzero_zero (restrictCurrent_isMetricCurrent hB hE) hw hRB hab,
    boundary_mul_zero_of_massMeasure (restrictCurrent_isMetricCurrent hT hE) hw hRT hab,sub_self]

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_FullCarrier
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma boundedLip_sub_const [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) :
    BoundedLip (fun x => u x-t) :=
  boundedLip_of_lipschitz (hu.1.choose_spec.sub (LipschitzWith.const t))

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_isMetricCurrent [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w) :
    IsMetricCurrent (weightedCurrent (currentMassMeasure hT) hT w) := by
  obtain ⟨B,hB⟩ := hw.2
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    (integrable_boundedLip _ hw) (M := ⟨max B 0,le_max_right _ _⟩)
  exact Eventually.of_forall fun x => (hB x).trans (le_max_left _ _)

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_apply [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    weightedCurrent (currentMassMeasure hT) hT w b π = T (fun x => w x * b x) π := by
  rw [weightedCurrent,ite_eq_left hab]
  exact borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩

lemma massMeasure_normalSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) :
    currentMassMeasure (normalSlice_approx h u t).metric {x | w x ≠ 0} = 0 := by
  classical
  by_cases hs : NormalApprox k (superlevelSlice h.normal.1 h.normal.2 u t)
  · have he : normalSlice h u t = superlevelSlice h.normal.1 h.normal.2 u t := ite_eq_left hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    exact mul_action_zero_of_massMeasure_nonzero_zero hs.metric hw
      (massMeasure_superlevelSlice_nonzero_zero h.normal.1 h.normal.2 hu t hs.metric hw hz) hab
  · have he : normalSlice h u t = 0 := ite_eq_right hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    rfl

lemma massMeasure_fullSlice_nonzero_zero {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (π : Fin k → X → ℝ) (hπ : ∀ i, Continuous (π i))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) (z : Euc k) :
    currentMassMeasure (fullSlice_approx h π z).metric {x | w x ≠ 0} = 0 := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    exact ih (normalSlice_approx h (π 0) (Prism.split k z).1) (Fin.tail π)
      (fun i => hπ i.succ) (massMeasure_normalSlice_nonzero_zero h (hπ 0) _ hw hz) (Prism.split k z).2

lemma ae_superlevelSlice_weighted_integral {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice hT.1 hT.2.2.1 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice hT.1 hT.2.2.1 u t b π := by
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  filter_upwards [ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1
    (boundedLip_of_lipschitz hK) (hS.mono fun _ ht => ht.1) hact hweight,hweight b π hab φ hφ] with t he ht
  simpa only [he] using ht

lemma NormalApprox.ae_superlevelSlice_weighted {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice h.normal.1 h.normal.2 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice h.normal.1 h.normal.2 u t b π := by
  have hcopy := h
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hcopy
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) C C hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) h.normal.1
    (fun j => (hTs (ψ j)).2.2.1) h.normal.2 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hK)
  have ht := ae_all_iff.mpr (fun j => ae_superlevelSlice_weighted_integral (hTs (ψ j)) hX hK hab hφ)
  filter_upwards [hweak,ht] with t hwt he
  have hl := hwt (fun x => φ (u x)*b x) π
  have hr := (hwt b π).const_mul (φ t)
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma ae_normalSlice_mul_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∀ᵐ t : ℝ, normalSlice h u t (fun x => (u x-t)*b x) π = 0 := by
  have hs := h.ae_superlevelSlice_weighted hX hu.1.choose_spec hab
    (φ := id) (by simpa only [Function.comp_def,id_eq] using hu)
  filter_upwards [ae_normalSlice_eq h hX hu.1.choose_spec,hs] with t he ht
  have hlin := (normalSlice_approx h u t).metric.linearFirst (fun x => u x*b x) b π 1 (-t) (hu.mul hab.1) hab.1 hab.2
  have hw : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [hw] at hlin
  rw [hlin,he]
  simp only [id_eq] at ht
  rw [ht]
  simp only [one_mul]
  ring

theorem ae_normalSlice_mass_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, currentMassMeasure (normalSlice_approx h u t).metric {x | u x ≠ t} = 0 := by
  let W (t : ℝ) := weightedCurrent (currentMassMeasure (normalSlice_approx h u t).metric)
    (normalSlice_approx h u t).metric (fun x => u x-t)
  have hW t : IsMetricCurrent (W t) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const hu t)
  have he : ∀ᵐ t : ℝ, W t = (0 : Functional X k) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero k)
    intro b π hab
    filter_upwards [ae_normalSlice_mul_level h hX hu hab] with t ht
    exact (weightedCurrent_boundedLip_apply _ (boundedLip_sub_const hu t) hab).trans ht
  filter_upwards [he] with t ht
  have hh : currentMassMeasure (normalSlice_approx h u t).metric {x | u x-t ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const hu t)
    intro b π hab
    rw [←weightedCurrent_boundedLip_apply (normalSlice_approx h u t).metric (boundedLip_sub_const hu t) hab]
    exact congrFun (congrFun ht b) π
  simpa only [sub_ne_zero] using hh

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma level_eval_of_carrier {T : Functional X 0} (hT : IsMetricCurrent T)
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (hz : currentMassMeasure hT {x | u x ≠ t} = 0)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    T (fun x => u x*b x) σ = t*T b σ := by
  have hh := mul_action_zero_of_massMeasure_nonzero_zero hT (boundedLip_sub_const hu t)
    (by simpa only [sub_ne_zero] using hz) (show Admissible b σ from ⟨hb,fun i => Fin.elim0 i⟩)
  have hl := hT.linearFirst (fun x => u x*b x) b σ 1 (-t) (hu.mul hb) hb (fun i => Fin.elim0 i)
  have he : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [he,hh] at hl
  linarith

lemma ae_fullSlice_level_eval {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let P (z : Euc (k+1)) := fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ
    have hm : MeasurableSet {z | P z} := measurableSet_eq_fun
      (measurable_fullSlice h π hπ _ _) (((PiLp.continuous_apply 2 _ i).measurable).mul (measurable_fullSlice h π hπ b σ))
    have hp : ∀ᵐ p : ℝ × Euc k ∂volume.prod volume, P ((Prism.split k).symm p) := by
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage (Prism.split k).symm.continuous.measurable)).mpr
      dsimp only [P,mem_ofPred_eq]
      refine Fin.cases ?_ (fun j => ?_) i
      · filter_upwards [ae_normalSlice_mass_level h hX (hπ 0)] with t ht
        filter_upwards [] with z
        exact level_eval_of_carrier (fullSlice_approx (normalSlice_approx h (π 0) t) (Fin.tail π) z).metric
          (hπ 0) t
          (by simpa only [sub_ne_zero] using (massMeasure_fullSlice_nonzero_zero
            (normalSlice_approx h (π 0) t) (Fin.tail π) (fun j => (hπ j.succ).1.choose_spec.continuous)
            (boundedLip_sub_const (hπ 0) t) (by simpa only [sub_ne_zero] using ht) z)) hb σ
      · exact Eventually.of_forall fun t => ih (normalSlice_approx h (π 0) t)
          (Fin.tail π) (fun j => hπ j.succ) j
    have hh := (Prism.split_measurePreserving k).quasiMeasurePreserving.ae hp
    simpa only [Measure.volume_eq_prod,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma ae_fullSlice_mass_level {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | π i x ≠ z i} = 0 := by
  let W (z : Euc k) := weightedCurrent (currentMassMeasure (fullSlice_approx h π z).metric)
    (fullSlice_approx h π z).metric (fun x => π i x-z i)
  have hW z : IsMetricCurrent (W z) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const (hπ i) (z i))
  have he : ∀ᵐ z : Euc k, W z = (0 : Functional X 0) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero 0)
    intro b σ hab
    filter_upwards [ae_fullSlice_level_eval h hX π hπ i hab.1 σ] with z hz
    change weightedCurrent _ (fullSlice_approx h π z).metric _ b σ = 0
    rw [weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    have hl := (fullSlice_approx h π z).metric.linearFirst (fun x => π i x*b x) b σ 1 (-(z i))
      ((hπ i).mul hab.1) hab.1 hab.2
    have hw : (fun x => 1*(π i x*b x)+ -(z i)*b x) = (fun x => (π i x-z i)*b x) := by funext x;ring
    rw [hw,hz] at hl
    simpa only [Pi.zero_apply] using hl.trans (by ring)
  filter_upwards [he] with z hz
  have hh : currentMassMeasure (fullSlice_approx h π z).metric {x | π i x-z i ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const (hπ i) (z i))
    intro b σ hab
    rw [←weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    exact congrFun (congrFun hz b) σ
  simpa only [sub_ne_zero] using hh

lemma ae_fullSlice_mass_fiber {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | coordinateMap π x ≠ z} = 0 := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_fullSlice_mass_level h hX π hπ i)] with z hz
  apply measure_mono_null (t := ⋃ i, {x | π i x ≠ z i}) ?_ (measure_iUnion_null fun i => hz i)
  intro x hx
  apply mem_iUnion.mpr
  by_contra hn
  push Not at hn
  exact hx (by ext i; simpa only [mem_ofPred_eq,not_not] using hn i)

lemma ae_fullSlice_weighted {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => φ (coordinateMap π x)*b x) σ =
      φ z*fullSlice h π z b σ := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  apply level_eval_of_carrier (fullSlice_approx h π z).metric hφπ (φ z) ?_ hb σ
  apply measure_mono_null (t := {x | coordinateMap π x ≠ z}) ?_ hz
  intro x hx he
  exact hx (congrArg φ he)

lemma fullSlice_weighted_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z : Euc k => φ z*fullSlice h π z b (fun j => Fin.elim0 j)) ∧
      T (fun x => φ (coordinateMap π x)*b x) π =
        ∫ z : Euc k, φ z*fullSlice h π z b (fun j => Fin.elim0 j) := by
  have he := ae_fullSlice_weighted h hX π hπ hφπ hb (fun j => Fin.elim0 j)
  refine ⟨(fullSlice_eval_integrable h hX π hπ (hφπ.mul hb) _).congr he,?_⟩
  exact (fullSlice_action_integral h hX π hπ (hφπ.mul hb)).trans (integral_congr_ae he)

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_WeakCalculus
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma linear_pi_expansion (L : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  have he : v = ∑ i, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

lemma ae_fderivWithin_scalar_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (fun x => φ (fun i => π i x))) C.domain z =
        (dφ (fun i => C.scalar (π i) z)).comp
          (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)) := by
  have hall : ∀ᵐ z ∂volume.restrict C.domain,
      ∀ i, DifferentiableWithinAt ℝ (C.scalar (π i)) C.domain z :=
    ae_all_iff.mpr fun i => C.ae_differentiableWithinAt_scalar (hπ i).choose_spec
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,hall] with z hz hzs hD
  have hPi := hasFDerivWithinAt_pi.mpr (fun i => (hD i).hasFDerivWithinAt)
  have hcomp := (hφ (fun i => C.scalar (π i) z)).comp_hasFDerivWithinAt z hPi
  have he : EqOn (C.scalar (fun x => φ (fun i => π i x)))
      (fun z => φ (fun i => C.scalar (π i) z)) C.domain := by
    intro y hy
    simp only [C.scalar_eq hy]
  exact (hcomp.congr he (he hzs)).fderivWithin hz

lemma ae_jacobian_update_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => φ (fun j => π j x))) z =
        dφ (fun j => C.scalar (π j) z) (Pi.single i 1) * C.jacobian π z := by
  filter_upwards [C.ae_fderivWithin_scalar_multi π hπ hφ] with z hz
  rw [C.jacobian_update,hz]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a j =>
    fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)
  let a : Fin k → ℝ := fun j => dφ (fun l => C.scalar (π l) z) (Pi.single j 1)
  have he : (fun j => ((dφ (fun i => C.scalar (π i) z)).comp
      (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)))
        (EuclideanSpace.single j 1)) = ∑ l, a l • M l := by
    ext j
    rw [ContinuousLinearMap.comp_apply,linear_pi_expansion]
    simp only [ContinuousLinearMap.pi_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,a,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact Matrix.det_updateRow_sum M i a

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_multi [BorelSpace X] [CompactSpace X]
    {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  classical
  obtain ⟨C,_,_,_,hrep⟩ := hT
  rw [hrep,hrep]
  apply tsum_congr
  intro q
  have had : Admissible b (Function.update π i (fun x => φ (fun j => π j x))) := by
    refine ⟨hb,?_⟩
    intro j
    by_cases he : j = i
    · simpa [he] using hφπ.1
    · simpa only [Function.update_of_ne he] using hπ j
  rw [IntegerChart.action,ite_eq_left had,IntegerChart.action,ite_eq_left ⟨hb.mul hdπ,hπ⟩]
  apply integral_congr_ae
  filter_upwards [(C q).ae_jacobian_update_multi π hπ hφ i,ae_restrict_mem (C q).borel] with z hz hzs
  rw [hz]
  simp only [(C q).scalar_eq hzs]
  ring

end CAT0Fillings.Foundations

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [Nonempty X] in
lemma NormalApprox.product_rule [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) + T f (Matrix.vecCons b π) =
      _root_.OAI.CAT0Fillings.boundarySucc T (fun x => b x * f x) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := (hlim b (Matrix.vecCons f π)).add (hlim f (Matrix.vecCons b π))
  have hright := boundarySucc_weak_limit hlim (fun x => b x * f x) π
  have he j := IntegerRectifiable.product_rule (hTs j).2.1 hb hf π hπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

omit [Nonempty X] in
lemma NormalApprox.apply_update_multi [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := hlim b (Function.update π i (fun x => φ (fun j => π j x)))
  have hright := hlim (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_update_multi (hrect j) hb π hπ hφ i hφπ hdπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.apply_permute [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    T b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ)*T b π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hl := hlim b (π ∘ σ)
  have hr := (hlim b π).const_mul ((Equiv.Perm.sign σ : ℤ):ℝ)
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_permute (hrect j) hab σ
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma NormalApprox.abs_apply_permute {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    |T b (π ∘ σ)| = |T b π| := by
  rw [hT.apply_permute hab σ,abs_mul,abs_unit_intCast,one_mul]

lemma NormalApprox.head_measure_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ}
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (hf : BoundedLip f)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    |T b (Matrix.vecCons f π)| ≤ (K:ℝ)^k *
      ((∫ x, |f x| ∂currentMassMeasure hT.normal.1) +
       (∫ x, |f x| ∂currentMassMeasure hT.normal.2)) := by
  have hbl : BoundedLip b := ⟨⟨1,hb⟩,1,hb1⟩
  have hp := hT.product_rule hbl hf π (fun i => ⟨K,hπ i⟩)
  have he : T b (Matrix.vecCons f π) =
      _root_.OAI.CAT0Fillings.boundarySucc T (fun x => b x*f x) π - T f (Matrix.vecCons b π) := by linarith
  have hbd := hT.normal.2.mass_bound (currentMassMeasure_controls hT.normal.2)
    (hbl.mul hf) (fun _ => K) hπ
  have hcur := hT.normal.1.mass_bound (currentMassMeasure_controls hT.normal.1)
    (π := Matrix.vecCons b π) hf (Matrix.vecCons 1 (fun _ => K)) (by intro i;exact Fin.cases hb (fun j => hπ j) i)
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,NNReal.coe_one,one_mul,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hbd hcur
  have hbi : (∫ x, |b x*f x| ∂currentMassMeasure hT.normal.2) ≤
      ∫ x, |f x| ∂currentMassMeasure hT.normal.2 := by
    apply integral_mono (integrable_boundedLip _ (hbl.mul hf)).abs (integrable_boundedLip _ hf).abs
    intro x
    change |b x*f x| ≤ |f x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hb1 x) (abs_nonneg _)).trans_eq (one_mul _)
  rw [he]
  calc _ ≤ |boundarySucc T (fun x => b x*f x) π| + |T f (Matrix.vecCons b π)| := abs_sub _ _
    _ ≤ (K:ℝ)^k * (∫ x, |f x| ∂currentMassMeasure hT.normal.2) +
        (K:ℝ)^k * (∫ x, |f x| ∂currentMassMeasure hT.normal.1) :=
      add_le_add (hbd.trans (mul_le_mul_of_nonneg_left hbi (pow_nonneg K.coe_nonneg _))) hcur
    _ = _ := by ring

lemma NormalApprox.coordinate_measure_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ}
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (hf : BoundedLip f)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) (i : Fin (k+1)) :
    |T b (Function.update π i f)| ≤ (K:ℝ)^k *
      ((∫ x, |f x| ∂currentMassMeasure hT.normal.1) +
       (∫ x, |f x| ∂currentMassMeasure hT.normal.2)) := by
  classical
  let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hne (j : Fin k) : σ j.succ ≠ i := by
    intro he
    have hh := congrArg σ he
    simp [σ] at hh
  have he : (Function.update π i f) ∘ σ = Matrix.vecCons f ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · simp only [Function.comp_apply,Function.update_of_ne (hne j),Matrix.cons_val_succ,ρ]
  have ha : Admissible b (Function.update π i f) := by
    refine ⟨⟨⟨1,hb⟩,1,hb1⟩,?_⟩
    intro j
    by_cases hj : j = i
    · simpa [hj] using hf.1
    · simpa only [Function.update_of_ne hj] using (show ∃ L, LipschitzWith L (π j) from ⟨K,hπ j⟩)
  rw [←hT.abs_apply_permute ha σ,he]
  exact hT.head_measure_bound hb hb1 hf ρ (fun j => hπ (σ j.succ))

theorem fullSlice_distributional_bound {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    {φ : (Fin (k+1) → ℝ) → ℝ}
    {dφ : (Fin (k+1) → ℝ) → (Fin (k+1) → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin (k+1))
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    |∫ z : Euc (k+1), dφ (WithLp.ofLp z) (Pi.single i 1)*
        fullSlice h π z b (fun j => Fin.elim0 j)| ≤
      (K:ℝ)^k * ((∫ x, |φ (fun j => π j x)| ∂currentMassMeasure h.normal.1) +
       (∫ x, |φ (fun j => π j x)| ∂currentMassMeasure h.normal.2)) := by
  have hbl : BoundedLip b := ⟨⟨1,hb⟩,1,hb1⟩
  have he := (fullSlice_weighted_integral h hX π (fun j => boundedLip_of_lipschitz (hπ j))
    (φ := fun z => dφ (WithLp.ofLp z) (Pi.single i 1)) hdπ hbl).2
  rw [←he]
  have hc := h.apply_update_multi hbl π (fun j => ⟨K,hπ j⟩) hφ i hφπ hdπ
  have hw : (fun x => dφ (fun j => π j x) (Pi.single i 1)*b x) =
      (fun x => b x*dφ (fun j => π j x) (Pi.single i 1)) := by funext x;ring
  change |T (fun x => dφ (fun j => π j x) (Pi.single i 1)*b x) π| ≤ _
  rw [hw,←hc]
  exact h.coordinate_measure_bound hb hb1 hφπ π hπ i

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_JointPoincare
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV

lemma scalar_convolution_comm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (f g : E → ℝ) :
    (f ⋆[lsmul ℝ ℝ, μ] g) = (g ⋆[lsmul ℝ ℝ, μ] f) := by
  have he : (lsmul ℝ ℝ).flip = lsmul ℝ ℝ := by ext; simp
  simpa only [he] using (convolution_flip (L := lsmul ℝ ℝ) (f := g) (g := f) (μ := μ))

lemma shrinkingBump_tendsto {E : Type*} [NormedAddCommGroup E] :
    Tendsto (fun j => (shrinkingBump (E := E) j).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem ball_poincare_of_directional_variation {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : LocallyIntegrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (a : EuclideanSpace ℝ (Fin k)) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall a r, |f z - (⨍ w in closedBall a r, f w ∂μ)| ∂μ) ≤
      (4*(2:ℝ)^k*k) * r * ν.real (closedBall a (2*r)) := by
  let η (j : ℕ) := shrinkingBump (E := EuclideanSpace ℝ (Fin k)) j
  let F (j : ℕ) := f ⋆[lsmul ℝ ℝ, μ] (η j).normed μ
  let F' (j : ℕ) := f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
    fderiv ℝ ((η j).normed μ)
  have hF (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) : HasFDerivAt (F j) (F' j x) x :=
    (η j).hasCompactSupport_normed.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf
      (η j).contDiff_normed x
  have hF' (j : ℕ) : Continuous (F' j) :=
    ((η j).hasCompactSupport_normed.fderiv ℝ).continuous_convolution_right
      ((lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k))) hf
      (((η j).contDiff_normed (n := (⊤ : ℕ∞))).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := η) shrinkingBump_tendsto (K := 2) (Eventually.of_forall (fun j => le_rfl)) hf
    filter_upwards [hh] with x hx
    simpa only [F,scalar_convolution_comm f] using hx
  have hg : ∀ᶠ j in atTop, (∫ z in closedBall a r, ‖F' j z‖ ∂μ) ≤
      k * ν.real (closedBall a (2*r)) := by
    have hh : ∀ᶠ j in atTop, (η j).rOut < r := (shrinkingBump_tendsto.eventually (gt_mem_nhds hr))
    filter_upwards [hh] with j hj
    exact (mollified_gradient_integral_bound hf hv (η j) a r).trans
      (mul_le_mul_of_nonneg_left
        (measureReal_mono (closedBall_subset_closedBall (by linarith : r+(η j).rOut ≤ 2*r)))
        (Nat.cast_nonneg k))
  have hp := ball_poincare_of_smooth_approx hf F F' hF hF' hl a hr (by positivity) hg
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hp
  exact hp.trans_eq (by ring)

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma parameterEquiv_apply (k : ℕ) (z : Fin k → ℝ) :
    parameterEquiv k z = WithLp.toLp 2 z := rfl

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma coordinateMap_lipschitz {k : ℕ} (π : Fin k → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) : ∃ L, LipschitzWith L (coordinateMap π) := by
  have hp : LipschitzWith K (fun x i => π i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr (fun i => (hπ i).dist_le_mul x y)
  exact ⟨_,(parameterEquiv k).toContinuousLinearMap.lipschitz.comp hp⟩

lemma fullSlice_directional_variation {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (i : Fin (k+1)) :
    DirectionalVariation (fun z => fullSlice h π z b (fun j => Fin.elim0 j))
      (EuclideanSpace.basisFun (Fin (k+1)) ℝ i) volume (fullSliceControl h π K) := by
  intro φ hφ hc
  let A := parameterEquiv (k+1)
  let v := EuclideanSpace.basisFun (Fin (k+1)) ℝ i
  let ψ : (Fin (k+1) → ℝ) → ℝ := fun z => φ (A z)
  let dψ (z : Fin (k+1) → ℝ) := (fderiv ℝ φ (A z)).comp A.toContinuousLinearMap
  have hψ (z) : HasFDerivAt ψ (dψ z) z :=
    ((hφ.differentiable (by simp)) (A z)).hasFDerivAt.comp z A.hasFDerivAt
  have he (z : Fin (k+1) → ℝ) : dψ z (Pi.single i 1) = fderiv ℝ φ (A z) v := by
    simp only [dψ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    congr 1
    simp only [v,EuclideanSpace.basisFun_apply]
    rfl
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbφ : BoundedLip (fun x => φ (coordinateMap π x)) := boundedLip_of_lipschitz (hM.comp hL)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc : HasCompactSupport (fun z => fderiv ℝ φ z v) := by
    exact (hc.fderiv ℝ).comp_left (g := fun L => L v) rfl
  obtain ⟨N,hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hdc hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbd : BoundedLip (fun x => dψ (fun j => π j x) (Pi.single i 1)) := by
    simp only [he]
    exact boundedLip_of_lipschitz (hN.comp hL)
  have hh := fullSlice_distributional_bound h hX π hπ hb hb1 hψ i hbφ hbd
  have hA (z : Euc (k+1)) : A (WithLp.ofLp z) = z := rfl
  simp only [he,hA] at hh
  change |∫ z, (fderiv ℝ φ z) v * fullSlice h π z b (fun j => Fin.elim0 j)| ≤ _
  rw [fullSliceControl,integral_smul_nnreal_measure]
  rw [integral_map hL.continuous.measurable.aemeasurable hφ.continuous.abs.aestronglyMeasurable]
  rw [integral_add_measure (integrable_boundedLip _ hbφ).abs (integrable_boundedLip _ hbφ).abs]
  simpa only [NNReal.smul_def,smul_eq_mul,NNReal.coe_pow,ψ,A,parameterEquiv_apply,coordinateMap] using hh

theorem fullSlice_ball_poincare {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    (a : Euc (k+1)) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall a r, |fullSlice h π z b (fun j => Fin.elim0 j) -
      (⨍ w in closedBall a r, fullSlice h π w b (fun j => Fin.elim0 j))|) ≤
      (4*(2:ℝ)^(k+1)*(k+1)) * r * (fullSliceControl h π K).real (closedBall a (2*r)) := by
  simpa only [Nat.cast_add,Nat.cast_one] using ball_poincare_of_directional_variation
    (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i))
      (b := b) ⟨⟨1,hb⟩,1,hb1⟩ (fun j => Fin.elim0 j)).locallyIntegrable
    (fun i => fullSlice_directional_variation h hX π hπ hb hb1 i) a hr

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_AtomGraphs
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma zeroChart_exists_supported_atom [Nonempty X] (C : IntegerChart X 0) :
    ∃ a : ℤ, ∃ x : X, (a ≠ 0 → x ∈ C.image) ∧ C.action = atomCurrent a x := by
  by_cases h : (0 : Euc 0) ∈ C.domain
  · exact ⟨C.multiplicity 0, C.param ⟨0, h⟩,
      fun _ => ⟨⟨0, h⟩, rfl⟩, C.zero_action h⟩
  · refine ⟨0, Classical.arbitrary X, fun ha => (ha rfl).elim, ?_⟩
    rw [C.zero_action_eq_zero h]
    funext b π
    simp only [atomCurrent, Int.cast_zero, zero_mul, ite_self, Pi.zero_apply]

theorem integerRectifiable_zero_distinct_representation [CompactSpace X] [Nonempty X]
    {T : Functional X 0} (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (∀ i, a i ≠ 0) ∧ Function.Injective x ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨C, hd, hC, hCS, heq⟩ := hI
  choose a x hsupp hact using fun i => zeroChart_exists_supported_atom (C i)
  have hmass i : mass (C i).action = |(a i : ℝ)| := by
    rw [hact i, mass_atomCurrent]
  have haS : Summable (fun i => |(a i : ℝ)|) := by simpa only [hmass] using hCS
  have hfinite := finite_support_int_of_summable_abs a haS
  let s := hfinite.toFinset
  have hs : ∀ i, i ∈ s ↔ a i ≠ 0 := fun i => hfinite.mem_toFinset
  let e := s.equivFin.symm
  have hezero : ∀ i, a (e i) ≠ 0 := fun i => (hs _).mp (e i).property
  refine ⟨s.card, fun i => a (e i), fun i => x (e i), hezero, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    by_contra hne
    have hi : x (e i) ∈ (C (e i)).image := hsupp _ (hezero i)
    have hj : x (e i) ∈ (C (e j)).image := by
      simpa only [hij] using hsupp _ (hezero j)
    exact Set.disjoint_left.mp (hd hne) hi hj
  · intro b π
    by_cases hadm : Admissible b π
    · rw [heq]
      simp_rw [hact]
      rw [tsum_eq_sum (s := s) (fun i hi => by
        have hai : a i = 0 := not_not.mp (fun hn => hi ((hs i).mpr hn))
        simp only [atomCurrent, hai, Int.cast_zero, zero_mul, ite_self])]
      rw [← Finset.sum_attach]
      exact (e.sum_comp (fun i : s => atomCurrent (a i) (x i) b π)).symm
    · simp only [hT.offDomain b π hadm, atomCurrent, ite_eq_right hadm, Finset.sum_const_zero]

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_lipschitz (p : X) (r : ℝ) : LipschitzWith 1 (atomicTent p r) := by
  have hdist : LipschitzWith 1 (fun z : X => dist z p) := LipschitzWith.dist_left p
  have hsub : LipschitzWith 1 (fun z : X => r - dist z p) := by
    simpa using (LipschitzWith.const r).sub hdist
  have hother : LipschitzWith 1 (fun z : X => max 0 (r - dist z p)) :=
    hsub.const_max 0
  change LipschitzWith 1 (fun z : X => min (dist z p) (max 0 (r - dist z p)))
  simpa only [max_self] using hdist.min hother

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_unit_bound (p : X) {r : ℝ} (hr : r ≤ 1) (z : X) :
    |atomicTent p r z| ≤ 1 := by
  have h0 : 0 ≤ atomicTent p r z := le_min dist_nonneg (le_max_left _ _)
  rw [abs_of_nonneg h0]
  exact (min_le_right _ _).trans (max_le (by norm_num)
    ((sub_le_self _ dist_nonneg).trans hr))

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_near {p z : X} {r : ℝ} (h : 2 * dist z p ≤ r) :
    atomicTent p r z = dist z p := by
  exact min_eq_left ((by linarith : dist z p ≤ r - dist z p).trans (le_max_right _ _))

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_far {p z : X} {r : ℝ} (h : r ≤ dist z p) :
    atomicTent p r z = 0 := by
  simp only [atomicTent, max_eq_left (sub_nonpos.mpr h), min_eq_right dist_nonneg]

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma exists_separated_center_code [SeparableSpace X] [Nonempty X]
    {m : ℕ} (x : Fin m → X) (hx : Function.Injective x) :
    ∃ (r : ℚ) (c : Fin m → ℕ), 0 < (r : ℝ) ∧ 4 * (r : ℝ) ≤ 1 ∧
      (∀ i, dist (x i) (TopologicalSpace.denseSeq X (c i)) ≤ (r : ℝ)) ∧
      ∀ i j, i ≠ j → 8 * (r : ℝ) ≤
        dist (TopologicalSpace.denseSeq X (c i)) (TopologicalSpace.denseSeq X (c j)) := by
  have he : ∀ᶠ r : ℝ in 𝓝 0, r < 1 / 4 ∧
      ∀ i j : Fin m, i ≠ j → 10 * r < dist (x i) (x j) := by
    refine (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).and ?_
    simp only [Filter.eventually_all]
    intro i j hij
    have hd : 0 < dist (x i) (x j) := dist_pos.mpr (fun h => hij (hx h))
    filter_upwards [eventually_lt_nhds (by positivity : (0 : ℝ) < dist (x i) (x j) / 10)] with r hr
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨r, hr0, hrδ⟩ := exists_pos_rat_lt hδ
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr := hball (show (r : ℝ) ∈ ball (0 : ℝ) δ by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr0'] using hrδ)
  choose c hc using fun i : Fin m =>
    (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt (x i) hr0'
  refine ⟨r, c, hr0', by linarith [hr.1], fun i => (hc i).le, ?_⟩
  intro i j hij
  have hd := hr.2 i j hij
  have htri : dist (x i) (x j) ≤
      dist (x i) (TopologicalSpace.denseSeq X (c i)) +
      dist (TopologicalSpace.denseSeq X (c i)) (TopologicalSpace.denseSeq X (c j)) +
      dist (x j) (TopologicalSpace.denseSeq X (c j)) := by
    calc
      _ ≤ dist (x i) (TopologicalSpace.denseSeq X (c i)) +
          dist (TopologicalSpace.denseSeq X (c i)) (x j) := dist_triangle _ _ _
      _ ≤ _ := by
        have := dist_triangle (TopologicalSpace.denseSeq X (c i))
          (TopologicalSpace.denseSeq X (c j)) (x j)
        rw [dist_comm (TopologicalSpace.denseSeq X (c j)) (x j)] at this
        linarith
  linarith [hc i, hc j]

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitRepresentation_matched_distance [SeparableSpace X] [Nonempty X]
    {S U : Functional X 0} (c : AtomCode) (hc : c.Valid (X := X))
    (x y : Fin c.size → X)
    (hx : ∀ i, dist (x i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius)
    (hy : ∀ i, dist (y i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius)
    (hS : UnitRepresentation S c.weights x) (hU : UnitRepresentation U c.weights y)
    {D : ℝ}
    (hD : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      |S b (fun j => Fin.elim0 j) - U b (fun j => Fin.elim0 j)| ≤ D)
    (i : Fin c.size) : dist (x i) (y i) ≤ D := by
  classical
  let p j := TopologicalSpace.denseSeq X (c.centers j)
  have hnear : 2 * dist (y i) (x i) ≤ 4 * c.radius := by
    have ht := dist_triangle_right (y i) (x i) (p i)
    linarith [hx i, hy i]
  have hfar (z : Fin c.size → X) (hz : ∀ j, dist (z j) (p j) ≤ c.radius)
      (j : Fin c.size) (hji : j ≠ i) : 4 * c.radius ≤ dist (z j) (x i) := by
    have ht : dist (p j) (p i) ≤ dist (z j) (p j) + dist (z j) (x i) + dist (x i) (p i) := by
      calc
        _ ≤ dist (p j) (z j) + dist (z j) (p i) := dist_triangle _ _ _
        _ ≤ _ := by
          have := dist_triangle (z j) (x i) (p i)
          rw [dist_comm (p j) (z j)]
          linarith
    linarith [hc.2.2.2 j i hji, hz j, hx i, hc.1]
  let b := atomicTent (x i) (4 * c.radius)
  have hbx j : b (x j) = 0 := by
    by_cases hji : j = i
    · subst j; exact atomicTent_center _ _
    · exact atomicTent_far (hfar x hx j hji)
  have hsi : S b (fun j => Fin.elim0 j) = 0 := by
    rw [hS b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1)]
    apply Finset.sum_eq_zero
    intro j _
    rw [hbx, mul_zero]
  have hui : U b (fun j => Fin.elim0 j) = (c.weights i : ℝ) * dist (y i) (x i) := by
    rw [hU b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1), Finset.sum_eq_single i]
    · change _ * atomicTent _ _ _ = _
      rw [atomicTent_near hnear]
    · intro j _ hji
      change _ * atomicTent _ _ _ = _
      rw [atomicTent_far (hfar y hy j hji), mul_zero]
    · simp
  have hbound := hD b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1)
  rw [hsi, hui, zero_sub, abs_neg, abs_mul, abs_of_nonneg dist_nonneg] at hbound
  have ha1 : (1 : ℝ) ≤ |(c.weights i : ℝ)| := by exact_mod_cast Int.one_le_abs (hc.2.2.1 i)
  calc
    dist (x i) (y i) = 1 * dist (y i) (x i) := by simp [dist_comm]
    _ ≤ |(c.weights i : ℝ)| * dist (y i) (x i) := mul_le_mul_of_nonneg_right ha1 dist_nonneg
    _ ≤ D := hbound

variable {P : Type*} [MetricSpace P]

omit [MeasurableSpace X] [BorelSpace X] [MetricSpace P] in
lemma atomDomain_subset [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) : atomDomain S E c ⊆ E :=
  fun _ h => h.1

omit [MeasurableSpace X] [BorelSpace X] in
lemma isCompact_atomDomain [CompactSpace X] [Nonempty X]
    (S : P → Functional X 0) {E : Set P} (hE : IsCompact E) (c : AtomCode)
    (hS : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      ContinuousOn (fun t => S t b (fun j => Fin.elim0 j)) E) :
    IsCompact (atomDomain S E c) := by
  apply hE.of_isClosed_subset _ (atomDomain_subset S E c)
  apply IsSeqClosed.isClosed
  intro z t hz hzt
  have htE : t ∈ E := hE.isClosed.mem_of_tendsto hzt (Eventually.of_forall fun j => (hz j).1)
  choose x hx hrepr using fun j => (hz j).2.2
  obtain ⟨y, φ, hφ, hy⟩ := CompactSpace.tendsto_subseq x
  have hyi i : Tendsto (fun j => x (φ j) i) atTop (𝓝 (y i)) :=
    (continuous_apply i).tendsto _ |>.comp hy
  refine ⟨htE, (hz 0).2.1, y, ?_, ?_⟩
  · intro i
    exact le_of_tendsto ((hyi i).dist tendsto_const_nhds)
      (Eventually.of_forall fun j => hx (φ j) i)
  · intro b hb hb1
    have hztE : Tendsto z atTop (𝓝[E] t) := tendsto_nhdsWithin_iff.mpr
      ⟨hzt, Eventually.of_forall fun j => (hz j).1⟩
    have hL := ((hS b hb hb1 t htE).tendsto.comp hztE).comp hφ.tendsto_atTop
    have hR : Tendsto (fun j => ∑ i, (c.weights i : ℝ) * b (x (φ j) i)) atTop
        (𝓝 (∑ i, (c.weights i : ℝ) * b (y i))) := by
      apply tendsto_finsetSum
      intro i _
      exact tendsto_const_nhds.mul ((hb.continuous.tendsto _).comp (hyi i))
    have hL' : Tendsto (fun j => ∑ i, (c.weights i : ℝ) * b (x (φ j) i)) atTop
        (𝓝 (S t b (fun j => Fin.elim0 j))) := by
      convert hL using 1
      all_goals try with_reducible_and_instances rfl
      funext j
      exact (hrepr (φ j) b hb hb1).symm
    exact tendsto_nhds_unique hL' hR

omit [MetricSpace P] in
lemma integral_mem_atomDomain [CompactSpace X] [Nonempty X]
    (S : P → Functional X 0) {E : Set P} {t : P} (ht : t ∈ E)
    (hI : IsIntegral 0 (S t)) : ∃ c : AtomCode, t ∈ atomDomain S E c := by
  classical
  obtain ⟨m, a, x, ha, hinj, hrepr⟩ := integerRectifiable_zero_distinct_representation hI.1 hI.2
  obtain ⟨r, centers, hr0, hr1, hx, hsep⟩ := exists_separated_center_code x hinj
  let c : AtomCode := ⟨m, a, centers, r⟩
  refine ⟨c, ht, ⟨hr0, hr1, ha, hsep⟩, x, hx, ?_⟩
  intro b hb hb1
  rw [hrepr]
  apply Finset.sum_congr rfl
  intro i _
  exact atomCurrent_apply _ _ ⟨⟨1, hb⟩, 1, hb1⟩

omit [MeasurableSpace X] [BorelSpace X] [MetricSpace P] in
lemma selectedAtom_spec [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) (t : atomDomain S E c) :
    (∀ i, dist (selectedAtom S E c t i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius) ∧
    UnitRepresentation (S t) c.weights (selectedAtom S E c t) := Classical.choose_spec t.property.2.2

omit [MeasurableSpace X] [BorelSpace X] in
lemma selectedAtom_lipschitz [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) {K : ℝ≥0}
    (hS : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      LipschitzOnWith K (fun t => S t b (fun j => Fin.elim0 j)) E)
    (i : Fin c.size) : LipschitzWith K (fun t : atomDomain S E c => selectedAtom S E c t i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  apply unitRepresentation_matched_distance c s.property.2.1
    (selectedAtom S E c s) (selectedAtom S E c t)
    (selectedAtom_spec S E c s).1 (selectedAtom_spec S E c t).1
    (selectedAtom_spec S E c s).2 (selectedAtom_spec S E c t).2
  intro b hb hb1
  simpa only [Real.dist_eq, Subtype.dist_eq] using (hS b hb hb1).dist_le_mul s s.property.1 t t.property.1

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_GraphAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomCode_atoms_injective (c : AtomCode) (hc : c.Valid (X := X))
    (x : Fin c.size → X)
    (hx : ∀ i, dist (x i) (denseSeq X (c.centers i)) ≤ c.radius) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hsep := hc.2.2.2 i j hne
  have htri := dist_triangle (denseSeq X (c.centers i)) (x i) (denseSeq X (c.centers j))
  rw [dist_comm (denseSeq X (c.centers i)) (x i), hij] at htri
  have hi := hx i
  rw [hij] at hi
  linarith [hi, hx j, hc.1]

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_LipschitzPieces
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

lemma measurable_real_closedBall (ν : Measure E) [SFinite ν] (r : ℝ) :
    Measurable (fun x : E => ν.real (closedBall x r)) := by
  have hs : MeasurableSet {p : E × E | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact (measurable_measure_prodMk_left hs).ennreal_toReal

lemma measurableSet_densityPiece (ν : Measure E) [SFinite ν] (N j : ℕ) :
    MeasurableSet (DensityPiece (μ := μ) ν N j) := by
  simp only [DensityPiece, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (measurable_real_closedBall ν q)
    ((measurable_real_closedBall μ q).const_mul (N : ℝ))

lemma ae_mem_iUnion_densityPiece (ν : Measure E) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂μ, ∃ N j : ℕ, x ∈ DensityPiece (μ := μ) ν N j := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_rnDeriv ν,
    Measure.rnDeriv_lt_top ν μ] with x hx hfin
  have hlim := (ENNReal.tendsto_toReal hfin.ne).comp
    (hx.comp (Besicovitch.tendsto_filterAt μ x))
  simp only [Function.comp_def, ENNReal.toReal_div] at hlim
  obtain ⟨N, hN⟩ := exists_nat_gt ((ν.rnDeriv μ x).toReal)
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ν.real (closedBall x r) / μ.real (closedBall x r) < (N : ℝ) :=
    (tendsto_order.1 hlim).2 _ hN
  obtain ⟨s, hs, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, j, ?_⟩
  intro q hq hjq
  have hqδ : (q : ℝ) < δ := hjq.trans_lt hj
  have hqs : (q : ℝ) ∈ s := hball (by
    simp only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq]
    exact hqδ)
  have hh := hsub ⟨hqs, hq⟩
  exact (div_lt_iff₀ (haar_closedBall_pos (μ := μ) hq)).mp hh |>.le

lemma measure_ball_bound_of_densityPiece (ν : Measure E) [IsLocallyFiniteMeasure ν]
    {N j : ℕ} {x : E} (hx : x ∈ DensityPiece (μ := μ) ν N j)
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrj : 2 * κ * r ≤ 1 / (j+1 : ℝ)) :
    ν.real (closedBall x (κ*r)) ≤
      (N : ℝ) * (2 * κ)^Module.finrank ℝ E * μ.real (closedBall x r) := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show κ*r < 2*κ*r by nlinarith [mul_pos hκ hr])
  have hq : 0 < (q : ℝ) := (mul_pos hκ hr).trans hq1
  have hsmall : ν.real (closedBall x (κ*r)) ≤ ν.real (closedBall x q) :=
    measureReal_mono (closedBall_subset_closedBall hq1.le) measure_closedBall_lt_top.ne
  have hlarge : μ.real (closedBall x q) ≤ μ.real (closedBall x (2*κ*r)) :=
    measureReal_mono (closedBall_subset_closedBall hq2.le) measure_closedBall_lt_top.ne
  calc
    _ ≤ (N : ℝ) * μ.real (closedBall x q) := hsmall.trans (hx q hq (hq2.le.trans hrj))
    _ ≤ (N : ℝ) * μ.real (closedBall x (2*κ*r)) :=
      mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg _)
    _ = _ := by
      rw [haar_closedBall_scale (μ := μ) x x hr (2*κ) (by positivity)]
      ring

lemma localMeanBound_of_densityPiece {f : E → ℝ} {ν : Measure E}
    [IsLocallyFiniteMeasure ν] {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ x : E, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall x r, |f z - (⨍ w in closedBall x r, f w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall x (κ*r)))
    {N j : ℕ} {x : E} (hx : x ∈ DensityPiece (μ := μ) ν N j) :
    LocalMeanBound (μ := μ) f (C * N * (2*κ)^Module.finrank ℝ E)
      x ((1 / (j+1 : ℝ)) / (2*κ)) := by
  intro r hr hrR
  have hd := measure_ball_bound_of_densityPiece ν hx hκ hr
    (by nlinarith [(le_div_iff₀ (show 0 < 2*κ by positivity)).mp hrR])
  calc
    _ ≤ C*r*ν.real (closedBall x (κ*r)) := hP x r hr
    _ ≤ C*r*((N : ℝ)*(2*κ)^Module.finrank ℝ E*μ.real (closedBall x r)) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hC hr.le)
    _ = _ := by ring

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]

lemma exists_compact_cover_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [Measure.IsAddHaarMeasure μ] {F : Set E} (hF : MeasurableSet F) (hfin : μ F ≠ ∞) :
    ∃ K : ℕ → Set E, (∀ i, K i ⊆ F ∧ IsCompact (K i)) ∧
      ∀ᵐ x ∂μ, x ∈ F → x ∈ ⋃ i, K i := by
  choose K hKF hK hsmall using fun n : ℕ =>
    hF.exists_isCompact_sdiff_lt hfin (show (1/2 : ℝ≥0∞)^n ≠ 0 by exact pow_ne_zero _ (by norm_num))
  refine ⟨K, fun i => ⟨hKF i, hK i⟩, ?_⟩
  have hbound (n : ℕ) : μ (F \ ⋃ i, K i) ≤ (1/2 : ℝ≥0∞)^n :=
    (measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))).trans (hsmall n).le
  have hz : μ (F \ ⋃ i, K i) = 0 := by
    apply le_antisymm _ bot_le
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1/2 : ℝ≥0∞) < 1)) (Eventually.of_forall hbound)
  apply ae_iff.mpr
  have he : {a | ¬(a ∈ F → a ∈ ⋃ i, K i)} = F \ ⋃ i, K i := by
    ext x
    exact Classical.not_imp
  rwa [he]

theorem common_compact_lipschitz_pieces {ι : Type*} [Countable ι]
    (f : ι → E → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ a x, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall x r, |f a z - (⨍ w in closedBall x r, f a w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall x (κ*r)))
    (G : Set E) (hG : ∀ᵐ x ∂μ, x ∈ G) :
    ∃ (K : (ℕ × ℕ × ℕ × ℕ) → Set E) (L : (ℕ × ℕ × ℕ × ℕ) → ℝ≥0),
      (∀ i, IsCompact (K i) ∧ K i ⊆ G) ∧
      (∀ i a, LipschitzOnWith (L i) (f a) (K i)) ∧
      (∀ᵐ x ∂μ, x ∈ ⋃ i, K i) := by
  classical
  let F : Set E := {x | x ∈ G ∧ ∀ a, Tendsto
    (fun r : ℝ => ⨍ z in closedBall x r, f a z ∂μ) (𝓝[>] 0) (𝓝 (f a x))}
  have hF : ∀ᵐ x ∂μ, x ∈ F := by
    filter_upwards [hG, ae_all_iff.mpr (fun a => ae_ballAverage_tendsto (hf a))] with x hx hy
    exact ⟨hx,hy⟩
  have hFn : NullMeasurableSet F μ := by
    apply (MeasurableSet.univ : MeasurableSet (univ : Set E)).nullMeasurableSet.congr
    filter_upwards [hF] with x hx
    apply propext
    exact ⟨fun _ => hx, fun _ => mem_univ x⟩
  obtain ⟨F₀, hF₀F, hF₀m, hF₀eq⟩ := hFn.exists_measurable_subset_ae_eq
  have hF₀ : ∀ᵐ x ∂μ, x ∈ F₀ := by
    filter_upwards [hF,hF₀eq] with x hx he
    exact he.mpr hx
  let R (j : ℕ) : ℝ := (1 / (j+1 : ℝ)) / (2*κ)
  have hR (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  let H (i : ℕ × ℕ × ℕ) : Set E :=
    F₀ ∩ DensityPiece (μ := μ) ν i.1 i.2.1 ∩
      closedBall (denseSeq E i.2.2) (R i.2.1 / 4)
  have hHm (i : ℕ × ℕ × ℕ) : MeasurableSet (H i) :=
    (hF₀m.inter (measurableSet_densityPiece ν i.1 i.2.1)).inter isClosed_closedBall.measurableSet
  have hHfin (i : ℕ × ℕ × ℕ) : μ (H i) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top)
  choose K hK hKcover using fun i : ℕ × ℕ × ℕ => exists_compact_cover_ae (hHm i) (hHfin i)
  let A (N : ℕ) : ℝ := C * N * (2*κ)^Module.finrank ℝ E
  have hA (N : ℕ) : 0 ≤ A N := by dsimp [A]; positivity
  let L (i : ℕ × ℕ × ℕ × ℕ) : ℝ≥0 :=
    ⟨8 * (2 : ℝ)^Module.finrank ℝ E * A i.1, by positivity⟩
  refine ⟨fun i => K (i.1,i.2.1,i.2.2.1) i.2.2.2, L, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hK _ _).2,?_⟩
    intro x hx
    exact (hF₀F ((hK _ _).1 hx).1.1).1
  · intro i a
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxH := (hK _ _).1 hx
    have hyH := (hK _ _).1 hy
    have hxF := hF₀F hxH.1.1
    have hyF := hF₀F hyH.1.1
    have hxM := localMeanBound_of_densityPiece hC hκ (hP a) hxH.1.2
    have hyM := localMeanBound_of_densityPiece hC hκ (hP a) hyH.1.2
    have hxy : 2 * dist x y ≤ R i.2.1 := by
      have htri := dist_triangle x (denseSeq E i.2.2.1) y
      have hx' : dist x (denseSeq E i.2.2.1) ≤ R i.2.1 / 4 := hxH.2
      have hy' : dist (denseSeq E i.2.2.1) y ≤ R i.2.1 / 4 := by
        simpa only [mem_closedBall, dist_comm] using hyH.2
      linarith
    exact abs_sub_le_of_localMeanBound (hf a) hxM hyM (hxF.2 a) (hyF.2 a) hxy
  · filter_upwards [hF₀, ae_mem_iUnion_densityPiece (μ := μ) ν,
      ae_all_iff.mpr hKcover] with x hx hD hcov
    obtain ⟨N,j,hNj⟩ := hD
    obtain ⟨l,hl⟩ := (denseRange_denseSeq E).exists_dist_lt x (show 0 < R j / 4 by positivity)
    have hxH : x ∈ H (N,j,l) := ⟨⟨hx,hNj⟩,hl.le⟩
    obtain ⟨m,hm⟩ := mem_iUnion.mp (hcov (N,j,l) hxH)
    exact mem_iUnion.mpr ⟨(N,j,l,m),hm⟩

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_BorelAtoms
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem common_zero_current_pieces {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (S : E → Functional X 0)
    (hI : ∀ᵐ t ∂μ, IsIntegral 0 (S t))
    (hf : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      LocallyIntegrable (fun t => S t b (fun j => Fin.elim0 j)) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      ∀ t, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall t r,
        |S z b (fun j => Fin.elim0 j) -
          (⨍ w in closedBall t r, S w b (fun j => Fin.elim0 j) ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r))) :
    ∃ (K : JointPieceIndex → Set E) (L : JointPieceIndex → ℝ≥0),
      (∀ i, IsCompact (K i) ∧ ∀ t ∈ K i, IsIntegral 0 (S t)) ∧
      (∀ i b, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
        LipschitzOnWith (L i) (fun t => S t b (fun j => Fin.elim0 j)) (K i)) ∧
      (∀ᵐ t ∂μ, t ∈ ⋃ i, K i) := by
  classical
  obtain ⟨q,hq⟩ := exists_dense_seq (TestClass (X := X) 0 1)
  let f (j : ℕ) (t : E) := TestClass.eval (S t) (q j)
  have hb (p : TestClass (X := X) 0 1) : ∀ x, |p.val.1 x| ≤ 1 := by
    intro x
    simpa only [Nat.cast_one, Real.norm_eq_abs] using (p.val.1.norm_coe_le_norm x).trans p.property.2.1
  have hpi (p : TestClass (X := X) 0 1) :
      (fun i => (p.val.2 i : X → ℝ)) = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  have hf' (j : ℕ) : LocallyIntegrable (f j) μ := by
    simpa only [f,TestClass.eval,hpi] using hf (q j).val.1 (by simpa only [Nat.cast_one] using (q j).property.1) (hb (q j))
  have hP' (j : ℕ) (t : E) (r : ℝ) (hr : 0 < r) :
      (∫ z in closedBall t r, |f j z - (⨍ w in closedBall t r, f j w ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r)) := by
    simpa only [f,TestClass.eval,hpi] using
      hP (q j).val.1 (by simpa only [Nat.cast_one] using (q j).property.1) (hb (q j)) t r hr
  obtain ⟨K,L,hK,hL,hcover⟩ := common_compact_lipschitz_pieces (μ := μ) f hf' ν hC hκ
    hP' {t | IsIntegral 0 (S t)} hI
  refine ⟨K,L,fun i => ⟨(hK i).1,(hK i).2⟩,?_,hcover⟩
  intro i b hbLip hbOne
  let bc : C(X,ℝ) := ⟨b,hbLip.continuous⟩
  have hn : ‖bc‖ ≤ 1 := (ContinuousMap.norm_le bc (by norm_num)).mpr (by
    simpa only [Real.norm_eq_abs,bc, ContinuousMap.coe_mk] using hbOne)
  let p : TestClass (X := X) 0 1 := ⟨(bc,fun z => Fin.elim0 z),by simpa only [Nat.cast_one,bc,ContinuousMap.coe_mk] using hbLip,
    by simpa only [Nat.cast_one] using hn,fun z => Fin.elim0 z⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hcurx : IsMetricCurrent (S x) := ((hK i).2 hx).1
  have hcury : IsMetricCurrent (S y) := ((hK i).2 hy).1
  have hbound : ∀ p : TestClass (X := X) 0 1,
      dist (TestClass.eval (S x) p) (TestClass.eval (S y) p) ≤ (L i : ℝ)*dist x y := by
    intro p
    exact hq.induction_on p
      (isClosed_le ((Foundations.IsMetricCurrent.testClass_continuous hcurx 1).dist
        (Foundations.IsMetricCurrent.testClass_continuous hcury 1))
        continuous_const) (fun j => (hL i j).dist_le_mul x hx y hy)
  have hpEval (U : Functional X 0) : TestClass.eval U p = U b (fun j => Fin.elim0 j) := by
    unfold TestClass.eval
    rw [hpi p]
    rfl
  simpa only [hpEval] using hbound p

theorem joint_integer_atom_graphs (S : E → Functional X 0)
    (hI : ∀ᵐ t ∂μ, IsIntegral 0 (S t))
    (hf : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      LocallyIntegrable (fun t => S t b (fun j => Fin.elim0 j)) μ)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ)
    (hP : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
      ∀ t, ∀ r : ℝ, 0 < r →
      (∫ z in closedBall t r,
        |S z b (fun j => Fin.elim0 j) -
          (⨍ w in closedBall t r, S w b (fun j => Fin.elim0 j) ∂μ)| ∂μ) ≤
        C * r * ν.real (closedBall t (κ*r))) :
    ∃ (D : JointPieceIndex × AtomCode → Set E)
      (L : JointPieceIndex × AtomCode → ℝ≥0)
      (γ : ∀ i : JointPieceIndex × AtomCode, D i → Fin i.2.size → X),
      (∀ i, IsCompact (D i)) ∧ (∀ᵐ t ∂μ, t ∈ ⋃ i, D i) ∧
      (∀ i j, LipschitzWith (L i) (fun t => γ i t j)) ∧
      (∀ i (t : D i), IsIntegral 0 (S t)) ∧
      (∀ i (t : D i), UnitRepresentation (S t) i.2.weights (γ i t)) ∧
      (∀ i (t : D i), Function.Injective (γ i t)) ∧
      (∀ i (_ : D i) j, i.2.weights j ≠ 0) := by
  classical
  obtain ⟨K,L,hK,hL,hcover⟩ := common_zero_current_pieces S hI hf ν hC hκ hP
  let D (i : JointPieceIndex × AtomCode) := atomDomain S (K i.1) i.2
  let γ (i : JointPieceIndex × AtomCode) (t : D i) := selectedAtom S (K i.1) i.2 t
  refine ⟨D,fun i => L i.1,γ,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact isCompact_atomDomain S (hK i.1).1 i.2
      (fun b hb hb1 => (hL i.1 b hb hb1).continuousOn)
  · filter_upwards [hcover,hI] with t ht hi
    obtain ⟨i,hit⟩ := mem_iUnion.mp ht
    obtain ⟨c,hc⟩ := integral_mem_atomDomain S hit hi
    exact mem_iUnion.mpr ⟨(i,c),hc⟩
  · intro i j
    exact selectedAtom_lipschitz S (K i.1) i.2 (hL i.1) j
  · intro i t
    exact (hK i.1).2 t t.property.1
  · intro i t
    exact (selectedAtom_spec S (K i.1) i.2 t).2
  · intro i t
    exact atomCode_atoms_injective i.2 t.property.2.1 _
      (selectedAtom_spec S (K i.1) i.2 t).1

  · intro i t j
    exact t.property.2.1.2.2.1 j

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma UnitRepresentation.action {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin 0 → X → ℝ) : S b π = ∑ i, (a i : ℝ)*b (x i) := by
  obtain ⟨K,hK⟩ := hb.1
  obtain ⟨B,hB⟩ := hb.2
  let C : ℝ := max (K : ℝ) (max B 1)
  have hC1 : 1 ≤ C := (le_max_right B 1).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hKC : (K : ℝ) ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B 1).trans (le_max_right _ _)
  let f : X → ℝ := fun z => C⁻¹*b z
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [f,Real.dist_eq,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hC),NNReal.coe_one,one_mul]
    calc
      C⁻¹ * |b z-b w| ≤ C⁻¹*((K : ℝ)*dist z w) :=
        mul_le_mul_of_nonneg_left (hK.dist_le_mul z w) (inv_nonneg.mpr hC.le)
      _ ≤ C⁻¹*(C*dist z w) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hKC dist_nonneg) (inv_nonneg.mpr hC.le)
      _ = dist z w := by field_simp
  have hf1 (z : X) : |f z| ≤ 1 := by
    simp only [f,abs_mul,abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹*|b z| ≤ C⁻¹*C := mul_le_mul_of_nonneg_left ((hB z).trans hBC) (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hs := h f hf hf1
  have hp : π = (fun j => Fin.elim0 j) := funext fun j => Fin.elim0 j
  have hlin := hS.linearFirst b b π C⁻¹ 0 hb hb (fun j => Fin.elim0 j)
  simp only [zero_mul,add_zero] at hlin
  change S f π = C⁻¹*S b π at hlin
  rw [←hp,hlin] at hs
  have hsum : (∑ i, (a i : ℝ)*f (x i)) = C⁻¹*∑ i, (a i : ℝ)*b (x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    ring
  rw [hsum] at hs
  exact mul_left_cancel₀ (inv_ne_zero hC.ne') hs

lemma UnitRepresentation.controls {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) :
    Controls S (∑ i, ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)) := by
  classical
  intro b π hb _
  rw [h.action hS hb π,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,
      ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,←abs_mul]
    exact Finset.abs_sum_le_sum_abs _ _
  · intro i _
    let := finite_atom_measure (a i) (x i)
    exact (integrable_boundedLip _ hb).abs

lemma UnitRepresentation.massMeasure_compl_eq_zero {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {E : Set X} (hE : MeasurableSet E)
    (hx : ∀ i, x i ∈ E) : currentMassMeasure hS Eᶜ = 0 := by
  classical
  let μ : Measure X := ∑ i, ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)
  let : ∀ i : Fin m, IsFiniteMeasure (ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)) :=
    fun i => finite_atom_measure (a i) (x i)
  have hμ : Controls S μ := h.controls hS
  apply le_antisymm ((currentMassMeasure_le hS hμ Eᶜ).trans ?_) (show (0 : ℝ≥0∞) ≤ _ from bot_le)
  simp only [μ,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  have hz (i : Fin m) : Measure.dirac (x i) Eᶜ = 0 := by
    rw [Measure.dirac_apply' _ hE.compl]
    exact indicator_of_notMem (by simpa only [mem_compl_iff,not_not] using hx i) _
  simp [hz]

lemma UnitRepresentation.borelAction_zero {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {f : X → ℝ}
    (hf : Measurable f) (hx : ∀ i, f (x i) = 0) (π : Fin 0 → X → ℝ) :
    currentBorelAction S f π = 0 := by
  have hE : MeasurableSet {z : X | f z = 0} := hf (measurableSet_singleton 0)
  have hm := h.massMeasure_compl_eq_zero hS hE hx
  have he : f =ᵐ[currentMassMeasure hS] 0 := by
    exact ae_iff.mpr hm
  rw [currentBorelAction_eq hS,borelAction_congr_ae _ hS he]
  rw [borelAction_of_integrable _ hS (integrable_zero X ℝ _)
    π (fun j => Fin.elim0 j)]
  simp

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_AtomCarrier
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma UnitRepresentation.borelAction {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {f : X → ℝ}
    (hf : Measurable f) {B : ℝ≥0} (hB : ∀ z, |f z| ≤ B) (π : Fin 0 → X → ℝ) :
    currentBorelAction S f π = ∑ i, (a i : ℝ)*f (x i) := by
  classical
  let νi (i : Fin m) := ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)
  let : ∀ i, IsFiniteMeasure (νi i) := fun i => finite_atom_measure (a i) (x i)
  let ν : Measure X := ∑ i, νi i
  have hν : Controls S ν := h.controls hS
  have hfν : Integrable f ν := integrable_bounded_measurable ν hf hB
  have hfμ : Integrable f (currentMassMeasure hS) := integrable_bounded_measurable _ hf hB
  have hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j) := fun j => Fin.elim0 j
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation ν hfν
  have hlim := borelAction_tendsto ν hS hν hfν
    (fun n => integrable_boundedLip ν (g n).property) hg π hπ
  have he (n : ℕ) : BorelCoefficients.borelAction ν hS (g n).val π = ∑ i, (a i : ℝ)*(g n).val (x i) := by
    rw [borelAction_eq ν hS hν ⟨(g n).property,hπ⟩]
    exact h.action hS (g n).property π
  have ht : Tendsto (fun n => ∑ i, (a i : ℝ)*(g n).val (x i)) atTop
      (𝓝 (∑ i, (a i : ℝ)*f (x i))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hg
    rw [Real.dist_eq,←Finset.sum_sub_distrib]
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        Integrable (fun z => |(g n).val z-f z|) (νi i) := by
      intro i _
      exact ((integrable_boundedLip (νi i) (g n).property).sub
        (integrable_bounded_measurable (νi i) hf hB)).abs
    change _ ≤ ∫ z, |(g n).val z-f z| ∂(∑ i, νi i)
    rw [integral_finsetSum_measure hi]
    simp only [νi,integral_smul_measure,integral_dirac,
      ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,←abs_mul,←mul_sub]
    exact Finset.abs_sum_le_sum_abs _ _
  simp only [he] at hlim
  rw [currentBorelAction_eq hS,
    borelAction_independent _ hS (currentMassMeasure_controls hS) hν hfμ hfν π hπ]
  exact tendsto_nhds_unique hlim ht

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma UnitRepresentation.atom_in_carrier {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) (ha : ∀ i, a i ≠ 0) (hx : Function.Injective x)
    {E : Set X} (_ : MeasurableSet E) (hμ : currentMassMeasure hS Eᶜ = 0) (i : Fin m) :
    x i ∈ E := by
  classical
  by_contra hi
  let f : X → ℝ := ({x i} : Set X).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_singleton _)
  have hf1 (z : X) : |f z| ≤ (1 : ℝ≥0) := by
    by_cases hz : z = x i <;> simp [f,hz]
  have he : f =ᵐ[currentMassMeasure hS] 0 := by
    have hEae : ∀ᵐ z ∂currentMassMeasure hS, z ∈ E := ae_iff.mpr hμ
    filter_upwards [hEae] with z hz
    apply indicator_of_notMem
    intro hzi
    exact hi ((mem_singleton_iff.mp hzi) ▸ hz)
  have hz : currentBorelAction S f (fun j => Fin.elim0 j) = 0 := by
    rw [currentBorelAction_eq hS,borelAction_congr_ae _ hS he]
    rw [borelAction_of_integrable _ hS (integrable_zero _ _ _) _ (fun j => Fin.elim0 j)]
    simp
  rw [h.borelAction hS hf hf1] at hz
  have hs : (∑ j, (a j : ℝ)*f (x j)) = (a i : ℝ) := by
    rw [Finset.sum_eq_single i]
    · simp [f]
    · intro j _ hji
      have hne : x j ≠ x i := fun hh => hji (hx hh)
      simp [f,hne]
    · simp
  rw [hs] at hz
  exact ha i (Int.cast_eq_zero.mp hz)

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_GraphCharts
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem fullSlice_compact_atom_graphs {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    ∃ (D : FullGraphIndex → Set (Euc (k+1)))
      (L U : FullGraphIndex → ℝ≥0)
      (γ : ∀ i : FullGraphIndex, D i → Fin i.2.size → X),
      (∀ i, IsCompact (D i)) ∧ (∀ᵐ z : Euc (k+1), z ∈ ⋃ i, D i) ∧
      (∀ i j, LipschitzWith (L i) (fun t => γ i t j)) ∧
      (∀ i j, AntilipschitzWith (U i) (fun t => γ i t j)) ∧
      (∀ i (t : D i) j, coordinateMap π (γ i t j) = t) ∧
      (∀ i (t : D i), UnitRepresentation (fullSlice h π t) i.2.weights (γ i t)) ∧
      (∀ i (t : D i), Function.Injective (γ i t)) := by
  classical
  have hπb (i) := boundedLip_of_lipschitz (hπ i)
  obtain ⟨D,L,γ,hD,hcover,hL,hI,hrep,hinj,hweights⟩ := joint_integer_atom_graphs
    (μ := volume) (fullSlice h π) (Eventually.of_forall (fullSlice_integral h π))
    (fun b hb hb1 => (fullSlice_eval_integrable h hX π hπb ⟨⟨1,hb⟩,1,hb1⟩
      (fun j => Fin.elim0 j)).locallyIntegrable)
    (fullSliceControl h π K) (C := 4*(2:ℝ)^(k+1)*(k+1)) (κ := 2)
    (by positivity) (by norm_num)
    (fun b hb hb1 a _r hr => fullSlice_ball_poincare h hX π hπ hb hb1 a hr)
  obtain ⟨A,hA⟩ := coordinateMap_lipschitz π hπ
  let (i : FullGraphIndex) : CompactSpace (D i) := isCompact_iff_compactSpace.mp (hD i)
  let F (i : FullGraphIndex) := {t : D i | ∀ j, coordinateMap π (γ i t j) = t}
  have hF (i) : IsCompact (F i) := by
    apply IsClosed.isCompact
    simpa only [F,ofPred_forall, Function.comp_def] using isClosed_iInter (fun j => isClosed_eq (hA.continuous.comp (hL i j).continuous) continuous_subtype_val)
  let D' (i : FullGraphIndex) : Set (Euc (k+1)) := Subtype.val '' F i
  have hsub (i) : D' i ⊆ D i := by
    rintro z ⟨t,ht,rfl⟩
    exact t.property
  let γ' (i : FullGraphIndex) (t : D' i) := γ i ⟨t,hsub i t.property⟩
  have hbase (i) (t : D' i) (j) : coordinateMap π (γ' i t j) = t := by
    obtain ⟨s,hs,he⟩ := t.property
    have ht : (⟨t,hsub i t.property⟩ : D i) = s := Subtype.ext he.symm
    change coordinateMap π (γ i ⟨t,hsub i t.property⟩ j) = t
    rw [ht,hs j,he]
  refine ⟨D',L,fun _ => A,γ',?_,?_,?_,?_,hbase,?_,?_⟩
  · intro i
    exact (hF i).image continuous_subtype_val
  · filter_upwards [hcover,ae_fullSlice_mass_fiber h hX π hπb] with z hz hmass
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    apply mem_iUnion.mpr
    refine ⟨i,⟨⟨z,hi⟩,?_,rfl⟩⟩
    intro j
    exact (hrep i ⟨z,hi⟩).atom_in_carrier (fullSlice_approx h π z).metric
      (hweights i ⟨z,hi⟩) (hinj i ⟨z,hi⟩)
      (measurableSet_eq_fun hA.continuous.measurable measurable_const) hmass j
  · intro i j
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact (hL i j).dist_le_mul ⟨s,hsub i s.property⟩ ⟨t,hsub i t.property⟩
  · intro i j
    apply AntilipschitzWith.of_le_mul_dist
    intro s t
    have hh := hA.dist_le_mul (γ' i s j) (γ' i t j)
    rwa [hbase i s j,hbase i t j] at hh
  · intro i t
    exact hrep i ⟨t,hsub i t.property⟩
  · intro i t
    exact hinj i ⟨t,hsub i t.property⟩

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] {k : ℕ}

lemma jointGraphChart_image {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) :
    (jointGraphChart hD γ hγ a).image = Set.range γ := rfl

lemma jointGraphChart_base_jacobian {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K, LipschitzWith K (π i))
    (hbase : ∀ t : D, ∀ i, π i (γ t) = t.val i) :
    ∀ᵐ z ∂volume.restrict D, (jointGraphChart hD γ hγ a).jacobian π z = 1 := by
  let C := jointGraphChart hD γ hγ a
  have he (i : Fin k) := C.ae_fderivWithin_scalar_eq_linear C.borel (subset_refl _)
    (hπ i).choose_spec (EuclideanSpace.proj i) (by
      intro z hz
      rw [C.scalar_eq hz]
      exact hbase ⟨z,hz⟩ i)
  filter_upwards [ae_all_iff.mpr he] with z hz
  change (Matrix.of fun i j => fderivWithin ℝ (C.scalar (π i)) D z (EuclideanSpace.single j 1)).det = 1
  change ∀ i, fderivWithin ℝ (C.scalar (π i)) D z = EuclideanSpace.proj i at hz
  have hm : (Matrix.of fun i j => fderivWithin ℝ (C.scalar (π i)) D z (EuclideanSpace.single j 1)) =
      (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    rw [Matrix.of_apply,hz i]
    simp [Matrix.one_apply]
  rw [hm,Matrix.det_one]

lemma jointGraphChart_base_action [MeasurableSpace X] [BorelSpace X]
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K, LipschitzWith K (π i))
    (hbase : ∀ t : D, ∀ i, π i (γ t) = t.val i)
    {b : X → ℝ} (hb : BoundedLip b) :
    (jointGraphChart hD γ hγ a).action b π = ∫ z in D, (a : ℝ)*jointGraphFunction γ b z := by
  let C := jointGraphChart hD γ hγ a
  rw [IntegerChart.action,ite_eq_left ⟨hb,hπ⟩]
  apply integral_congr_ae
  filter_upwards [jointGraphChart_base_jacobian hD γ hγ a π hπ hbase,ae_restrict_mem hD.measurableSet] with z hj hz
  rw [hj,mul_one,C.scalar_eq hz]
  change z ∈ D at hz
  simp only [jointGraphFunction,dite_eq_left hz]
  rfl

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_JointKernel
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma tuple_lipschitz_update {π : Fin k → X → ℝ}
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k)
    {v : X → ℝ} (hv : ∃ K : ℝ≥0, LipschitzWith K v) :
    ∀ j, ∃ K : ℝ≥0, LipschitzWith K (Function.update π i v j) := by
  classical
  intro j
  by_cases he : j = i
  · simpa [he] using hv
  · simpa only [Function.update_of_ne he] using hπ j

lemma TupleKernel.of_boundedLip {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (hz : ∀ b, BoundedLip b → T b π = 0) : TupleKernel μ hT π := by
  intro f hf
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have ht := borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg π hπ
  have he (n : ℕ) : borelAction μ hT (g n).val π = 0 := by
    rw [borelAction_eq μ hT hμ ⟨(g n).property,hπ⟩]
    exact hz (g n).val (g n).property
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma TupleKernel.coord_const {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) (c : ℝ) : TupleKernel μ hT (Function.update π i (fun _ => c)) := by
  classical
  intro f hf
  exact borelAction_const_coord μ hT hμ hf _
    (tuple_lipschitz_update hπ i ⟨0,LipschitzWith.const c⟩) i c (fun _ => by simp)

lemma TupleKernel.coord_linear {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) (a c : ℝ) :
    TupleKernel μ hT (Function.update π i (fun x => a*u x+c*v x)) := by
  classical
  intro f hf
  have hh := borelAction_linearCoord μ hT hμ hf (Function.update π i u)
    (tuple_lipschitz_update hπ i hu) i v hv a c
  simp only [Function.update_self,Function.update_idem,hku f hf,hkv f hf,mul_zero,add_zero] at hh
  exact hh

lemma TupleKernel.coord_min {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) :
    TupleKernel μ hT (Function.update π i (fun x => min (u x) (v x))) := by
  classical
  obtain ⟨K,hK⟩ := hu
  obtain ⟨L,hL⟩ := hv
  intro f hf
  let E := {x | u x ≤ v x}
  have hE : MeasurableSet E := measurableSet_le hK.continuous.measurable hL.continuous.measurable
  let τ := Function.update π i (fun x => min (u x) (v x))
  have hτ := tuple_lipschitz_update hπ i ⟨max K L,hK.min hL⟩
  have h1 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE)
    τ hτ i u ⟨K,hK⟩ (by
      intro x hx
      have hxE : x ∈ E := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      simpa only [τ,Function.update_self] using min_eq_left hxE)
  have h2 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE.compl)
    τ hτ i v ⟨L,hL⟩ (by
      intro x hx
      have hxE : x ∈ Eᶜ := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      simpa only [τ,Function.update_self] using min_eq_right (le_of_not_ge (show ¬u x ≤ v x from hxE)))
  simp only [τ,Function.update_idem,hku _ (hf.indicator hE)] at h1
  simp only [τ,Function.update_idem,hkv _ (hf.indicator hE.compl)] at h2
  have heq : f = fun x => E.indicator f x+Eᶜ.indicator f x := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [heq]
  change borelAction μ hT (E.indicator f + Eᶜ.indicator f) τ = 0
  rw [borelAction_add μ hT (hf.indicator hE) (hf.indicator hE.compl) _ hτ,h1,h2]
  simp

lemma TupleKernel.coord_neg {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u : X → ℝ} (hu : ∃ K, LipschitzWith K u)
    (hku : TupleKernel μ hT (Function.update π i u)) :
    TupleKernel μ hT (Function.update π i (fun x => -u x)) := by
  simpa using TupleKernel.coord_linear μ hμ hπ i hu hu hku hku (-1) 0

lemma TupleKernel.coord_max {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) :
    TupleKernel μ hT (Function.update π i (fun x => max (u x) (v x))) := by
  have hnu : ∃ K, LipschitzWith K (fun x => -u x) := ⟨hu.choose,hu.choose_spec.neg⟩
  have hnv : ∃ K, LipschitzWith K (fun x => -v x) := ⟨hv.choose,hv.choose_spec.neg⟩
  have hm := TupleKernel.coord_min μ hμ hπ i hnu hnv
    (TupleKernel.coord_neg μ hμ hπ i hu hku) (TupleKernel.coord_neg μ hμ hπ i hv hkv)
  have hLm : ∃ K, LipschitzWith K (fun x => min (-u x) (-v x)) :=
    ⟨max hnu.choose hnv.choose,hnu.choose_spec.min hnv.choose_spec⟩
  have he : (fun x => -(min (-u x) (-v x))) = (fun x => max (u x) (v x)) := by
    funext x
    by_cases hx : u x ≤ v x
    · simp only [max_eq_right hx,min_eq_right (neg_le_neg hx),neg_neg]
    · have hx' := le_of_not_ge hx
      simp only [max_eq_left hx',min_eq_left (neg_le_neg hx'),neg_neg]
  simpa only [he] using TupleKernel.coord_neg μ hμ hπ i hLm hm

lemma TupleKernel.coord_limit {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {us : ℕ → X → ℝ} {u : X → ℝ} {K : ℝ≥0}
    (hs : ∀ n, TupleKernel μ hT (Function.update π i (us n)))
    (hK : ∀ n, LipschitzWith K (us n))
    (hlim : ∀ x, Tendsto (fun n => us n x) atTop (𝓝 (u x))) :
    TupleKernel μ hT (Function.update π i u) := by
  classical
  intro f hf
  have hunif : ∀ j, ∃ L, ∀ n, LipschitzWith L (Function.update π i (us n) j) := by
    intro j
    by_cases he : j = i
    · subst j
      exact ⟨K,by simpa using hK⟩
    · exact ⟨(hπ j).choose,fun n => by simpa only [Function.update_of_ne he] using (hπ j).choose_spec⟩
  have hpoint : ∀ j x, Tendsto (fun n => Function.update π i (us n) j x) atTop
      (𝓝 (Function.update π i u j x)) := by
    intro j x
    by_cases he : j = i
    · subst j
      simpa using hlim x
    · simpa only [Function.update_of_ne he] using tendsto_const_nhds (x := π j x)
  have ht := borelAction_sequentialContinuity μ hT hμ hf (Function.update π i u)
    (fun n => Function.update π i (us n)) hunif hpoint
  simp only [hs _ f hf] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma tupleKernel_lipLattice {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    LipLattice (fun u => TupleKernel μ hT (Function.update π i u)) where
  const := TupleKernel.coord_const μ hμ hπ i
  linear := fun hu hv hku hkv => TupleKernel.coord_linear μ hμ hπ i hu hv hku hkv
  min := fun hu hv hku hkv => TupleKernel.coord_min μ hμ hπ i hu hv hku hkv
  max := fun hu hv hku hkv => TupleKernel.coord_max μ hμ hπ i hu hv hku hkv
  limit := fun hs hK hlim => TupleKernel.coord_limit μ hμ hπ i hs hK hlim

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma tupleKernel_comp_pi {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {m : ℕ} {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ ρ : Fin k → Fin m, TupleKernel μ hT (fun i x => u x (ρ i)))
    (φ : Fin k → (Fin m → ℝ) → ℝ) (hφ : ∀ i, ∃ K, LipschitzWith K (φ i)) :
    TupleKernel μ hT (fun i x => φ i (u x)) := by
  classical
  let Fits (s : Finset (Fin k)) (π : Fin k → X → ℝ) : Prop :=
    ∀ i, (i ∈ s → ∃ (K : ℝ≥0) (ψ : (Fin m → ℝ) → ℝ), LipschitzWith K ψ ∧ π i = fun x => ψ (u x)) ∧
      (i ∉ s → ∃ j : Fin m, π i = fun x => u x j)
  have hul (j : Fin m) : LipschitzWith L (fun x => u x j) := by
    simpa only [one_mul,Function.comp_def,Function.eval] using (LipschitzWith.eval j).comp hu
  have hfitlip {s : Finset (Fin k)} {π : Fin k → X → ℝ} (hf : Fits s π) :
      ∀ i, ∃ K, LipschitzWith K (π i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨K,ψ,hψ,he⟩ := (hf i).1 hi
      exact ⟨K*L,by simpa only [he,Function.comp_def] using hψ.comp hu⟩
    · obtain ⟨j,he⟩ := (hf i).2 hi
      exact ⟨L,he ▸ hul j⟩
  have hstep (s : Finset (Fin k)) : ∀ π, Fits s π → TupleKernel μ hT π := by
    induction s using Finset.induction_on with
    | empty =>
      intro π hf
      choose ρ hρ using fun i => (hf i).2 (Finset.notMem_empty i)
      have he : π = fun i x => u x (ρ i) := by funext i;exact hρ i
      rw [he]
      exact hgen ρ
    | @insert i s hi ih =>
      intro π hf
      obtain ⟨K,ψ,hψ,heψ⟩ := (hf i).1 (Finset.mem_insert_self i s)
      have hsgen (j : Fin m) : TupleKernel μ hT (Function.update π i (fun x => u x j)) := by
        apply ih
        intro l
        constructor
        · intro hl
          have hli : l ≠ i := by rintro rfl;exact hi hl
          obtain ⟨K',ψ',hψ',heψ'⟩ := (hf l).1 (Finset.mem_insert_of_mem hl)
          exact ⟨K',ψ',hψ',by simpa only [Function.update_of_ne hli] using heψ'⟩
        · intro hl
          by_cases hli : l = i
          · subst l
            exact ⟨j,by simp⟩
          · have hl' : l ∉ insert i s := by simp only [Finset.mem_insert];exact not_or.mpr ⟨hli,hl⟩
            obtain ⟨j',hj'⟩ := (hf l).2 hl'
            exact ⟨j',by simpa only [Function.update_of_ne hli] using hj'⟩
      have hc := (tupleKernel_lipLattice μ hμ (hfitlip hf) i).comp_pi hu hsgen hψ
      have hup : Function.update π i (fun x => ψ (u x)) = π := by rw [←heψ];exact Function.update_eq_self i π
      simpa only [hup] using hc
  apply hstep Finset.univ
  intro i
  constructor
  · intro _
    exact ⟨(hφ i).choose,φ i,(hφ i).choose_spec,rfl⟩
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_Uniqueness
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_congr_coords_on_support (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π ρ : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (heq : ∀ i x, x ∈ Function.support f → π i x = ρ i x) :
    borelAction μ hT f π = borelAction μ hT f ρ := by
  classical
  let mix (s : Finset (Fin k)) := fun i => if i ∈ s then ρ i else π i
  have hmix (s : Finset (Fin k)) : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (mix s i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [mix,ite_eq_left hi] using hρ i
    · simpa only [mix,ite_eq_right hi] using hπ i
  have hs (s : Finset (Fin k)) : borelAction μ hT f π = borelAction μ hT f (mix s) := by
    induction s using Finset.induction_on with
    | empty => simp only [mix,Finset.notMem_empty,ite_false, if_false]
    | @insert i s hi ih =>
      have he := borelAction_congr_coord_on_support μ hT hμ hf (mix s) (hmix s) i (ρ i) (hρ i) (by
        intro x hx
        simpa only [mix,ite_eq_right hi] using heq i x hx)
      have hu : Function.update (mix s) i (ρ i) = mix (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [mix]
        · simp [mix,hj]
      rw [hu] at he
      exact ih.trans he
  simpa only [mix,Finset.mem_univ,ite_true, if_true] using hs Finset.univ

end CAT0Fillings.BorelCoefficients
namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [Nonempty X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma graph_coord_extension {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X]
    {D : Set (Euc k)} (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    {v : X → ℝ} {J : ℝ≥0} (hv : LipschitzWith J v) :
    ∃ (ψ : (Fin k → ℝ) → ℝ) (K : ℝ≥0), LipschitzWith K ψ ∧
      ∀ t : D, ψ (fun i => π i (γ t)) = v (γ t) := by
  classical
  let g : Euc k → ℝ := fun t => if ht : t ∈ D then v (γ ⟨t,ht⟩) else 0
  have hg : LipschitzOnWith (J*L) g D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [g,dite_eq_left hs,dite_eq_left ht,Subtype.dist_eq,Function.comp_apply] using
      (hv.comp hγ).dist_le_mul ⟨s,hs⟩ ⟨t,ht⟩
  obtain ⟨φ,hφ,heq⟩ := hg.extend_real
  refine ⟨fun z => φ (parameterEquiv k z),_,
    hφ.comp (parameterEquiv k).toContinuousLinearMap.lipschitz,?_⟩
  intro t
  change φ (coordinateMap π (γ t)) = v (γ t)
  rw [hbase t]
  simpa only [g,dite_eq_left t.property] using (heq t.property).symm

lemma baseTuple_lipschitz {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x i => π i x) := by
  classical
  choose K hK using hπ
  refine ⟨Finset.univ.sup K,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (Finset.univ.sup K).coe_nonneg dist_nonneg)).mpr
  intro i
  exact ((hK i).weaken (Finset.le_sup (Finset.mem_univ i))).dist_le_mul x y

theorem current_eq_zero_on_joint_graph {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0)
    (hz : ∀ (ρ : Fin k → Fin k) b, BoundedLip b → T b (π ∘ ρ) = 0) :
    T = fun _ _ => 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hE : MeasurableSet (Set.range γ) := (isCompact_range hγ.continuous).measurableSet
  obtain ⟨K,hK⟩ := baseTuple_lipschitz π hπ
  have hgen (ρ : Fin k → Fin k) : TupleKernel μ hT (fun i x => π (ρ i) x) := by
    apply TupleKernel.of_boundedLip μ hμ (fun i => hπ (ρ i))
    exact hz ρ
  funext b σ
  by_cases hab : Admissible b σ
  · have hext (i : Fin k) := graph_coord_extension γ hγ π hbase (hab.2 i).choose_spec
    choose ψ J hJ hψ using hext
    have hker := tupleKernel_comp_pi μ hμ hK hgen ψ (fun i => ⟨J i,hJ i⟩)
    have hb := integrable_boundedLip μ hab.1
    have hbE := hb.indicator hE
    have hbe : (Set.range γ).indicator b =ᵐ[μ] b := by
      filter_upwards [show ∀ᵐ x ∂μ, x ∈ Set.range γ from ae_iff.mpr hsupp] with x hx
      exact indicator_of_mem hx _
    rw [←borelAction_eq μ hT hμ hab,←borelAction_congr_ae μ hT hbe]
    calc
      _ = borelAction μ hT ((Set.range γ).indicator b) (fun i x => ψ i (fun j => π j x)) := by
        apply borelAction_congr_coords_on_support μ hT hμ hbE σ _ hab.2
          (fun i => ⟨J i*K,hJ i |>.comp hK⟩)
        intro i x hx
        have hxE : x ∈ Set.range γ := by
          by_contra hh
          exact hx (indicator_of_notMem hh _)
        obtain ⟨t,rfl⟩ := hxE
        exact (hψ i t).symm
      _ = 0 := hker _ hbE
  · exact hT.offDomain b σ hab

theorem current_eq_on_joint_graph {U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U)
    (hμ : Controls T μ) (ν : Measure X) [IsFiniteMeasure ν] (hν : Controls U ν)
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hbase : ∀ t : D, coordinateMap π (γ t) = t)
    (hsupp : μ (Set.range γ)ᶜ = 0) (hsupp' : ν (Set.range γ)ᶜ = 0)
    (hbaseact : ∀ (ρ : Fin k → Fin k) b, BoundedLip b → T b (π ∘ ρ) = U b (π ∘ ρ)) :
    T = U := by
  have hd : IsMetricCurrent (T + -U) := hT.add hU.neg
  have hc : Controls (T + -U) (μ+ν) := controls_add hμ (controls_neg_iff.mpr hν)
  have hz := current_eq_zero_on_joint_graph (μ+ν) (hT := hd) hc hD γ hγ π hπ hbase
    (by simp only [Measure.add_apply,hsupp,hsupp',add_zero]) (by
      intro ρ b hb
      change T b (π ∘ ρ) + -U b (π ∘ ρ) = 0
      rw [hbaseact ρ b hb]
      exact add_neg_cancel _)
  funext b σ
  have he := congrFun (congrFun hz b) σ
  change T b σ + -U b σ = 0 at he
  linarith

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_Localization
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma integral_zero_unitRepresentation {S : Functional X 0} (hS : IsIntegral 0 S) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (∀ i, a i ≠ 0) ∧ Function.Injective x ∧ UnitRepresentation S a x := by
  obtain ⟨m,a,x,ha,hx,he⟩ := integerRectifiable_zero_distinct_representation hS.1 hS.2
  refine ⟨m,a,x,ha,hx,?_⟩
  intro b hb hb1
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [atomCurrent,ite_eq_left ⟨⟨⟨1,hb⟩,1,hb1⟩,fun j => Fin.elim0 j⟩]

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma joint_graph_atom_mem_iff {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {D : Set (Euc k)} {m : ℕ}
    (γ : D → Fin m → X)
    {π : Fin k → X → ℝ} (hbase : ∀ t j, coordinateMap π (γ t j) = t)
    (hinj : ∀ t, Function.Injective (γ t)) (t : D) (i j : Fin m) :
    γ t i ∈ Set.range (fun s => γ s j) ↔ i = j := by
  constructor
  · rintro ⟨s,he⟩
    have ht : s = t := Subtype.ext (by simpa only [hbase] using congrArg (coordinateMap π) he)
    subst s
    exact (hinj t he).symm
  · rintro rfl
    exact ⟨t,rfl⟩

lemma fullSlice_graph_action {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, Continuous (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    {b : X → ℝ} (hb : BoundedLip b) (j : Fin m) :
    ∀ᵐ z : Euc k, currentBorelAction (fullSlice h π z)
      ((Set.range (fun s => γ s j)).indicator b) (fun i => Fin.elim0 i) =
      if hz : z ∈ D then (a j : ℝ)*b (γ ⟨z,hz⟩ j) else 0 := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let E := Set.range (fun s => γ s j)
  have hE : MeasurableSet E := (isCompact_range (hγ j)).measurableSet
  have hf : Measurable (E.indicator b) := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |E.indicator b x| ≤ B' := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      exact (hBb x).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  have hA : Continuous (coordinateMap π) := by
    exact (parameterEquiv k).continuous.comp (continuous_pi fun i => (hπ i).continuous)
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hzM
  have hI := fullSlice_integral h π z
  by_cases hz : z ∈ D
  · rw [dite_eq_left hz,(hrep ⟨z,hz⟩).borelAction hI.1 hf hfB]
    rw [Finset.sum_eq_single j]
    · rw [indicator_of_mem (show γ ⟨z,hz⟩ j ∈ E from ⟨⟨z,hz⟩,rfl⟩)]
    · intro i _ hij
      rw [indicator_of_notMem ((joint_graph_atom_mem_iff γ hbase hinj ⟨z,hz⟩ i j).not.mpr hij),mul_zero]
    · simp
  · rw [dite_eq_right hz]
    obtain ⟨q,c,x,hc,hx,hrep'⟩ := integral_zero_unitRepresentation hI
    apply hrep'.borelAction_zero hI.1 hf
    intro i
    apply indicator_of_notMem
    rintro ⟨s,he⟩
    have hlevel := hrep'.atom_in_carrier hI.1 hc hx
      (measurableSet_eq_fun hA.measurable measurable_const) hzM i
    change coordinateMap π (x i) = z at hlevel
    rw [←he,hbase] at hlevel
    exact hz (hlevel ▸ s.property)

lemma full_graph_restriction_base_action {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, ∃ L U : ℝ≥0, LipschitzWith L (fun t => γ t j) ∧
      AntilipschitzWith U (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    (j : Fin m) {b : X → ℝ} (hb : BoundedLip b) :
    restrictCurrent h.metric (Set.range (fun t => γ t j)) b π =
      (jointGraphChart hD (fun t => γ t j) (hγ j) (a j)).action b π := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let E := Set.range (fun t => γ t j)
  have hγc (i : Fin m) : Continuous (fun t => γ t i) := (hγ i).choose_spec.choose_spec.1.continuous
  have hE : MeasurableSet E := (isCompact_range (hγc j)).measurableSet
  let f := E.indicator b
  have hf : Measurable f := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |f x| ≤ B' := by
    by_cases hx : x ∈ E
    · exact (by simpa only [f,indicator_of_mem hx] using (show |b x| ≤ B' from (hBb x).trans (le_max_left B 0)))
    · simp only [f,indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  have ha := fullSlice_borel_integral h hX π hπ hf B' hfB
  have hs := fullSlice_graph_action h hX π hπ hD γ hγc a hbase hinj hrep hb j
  rw [restrictCurrent_apply h.metric E ⟨hb,fun i => (hπ i).1⟩,
    ←currentBorelAction_eq h.metric f π,ha.2]
  rw [jointGraphChart_base_action hD _ (hγ j) (a j) π (fun i => (hπ i).1) (by
    intro t i
    exact congrArg (fun z : Euc k => z i) (hbase t j)) hb]
  rw [←integral_indicator hD.measurableSet]
  apply integral_congr_ae
  filter_upwards [hs] with z hz
  rw [hz]
  by_cases hzD : z ∈ D
  · simp only [dite_eq_left hzD,indicator_of_mem hzD,jointGraphFunction]
  · simp only [dite_eq_right hzD,indicator_of_notMem hzD]

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_ScalarCharts
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma jacobian_reindex (π : Fin k → X → ℝ) (ρ : Fin k → Fin k) (z : Euc k) :
    C.jacobian (π ∘ ρ) z = reindexFactor ρ * C.jacobian π z := by
  classical
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j =>
    fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1)
  let R : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => if ρ i = j then 1 else 0
  have he : M.submatrix ρ id = R*M := by
    ext i j
    simp [M,R,Matrix.mul_apply]
  change (M.submatrix ρ id).det = R.det*M.det
  rw [he,Matrix.det_mul]

lemma action_reindex [MeasurableSpace X] {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (ρ : Fin k → Fin k) :
    C.action b (π ∘ ρ) = reindexFactor ρ * C.action b π := by
  have hρ : Admissible b (π ∘ ρ) := ⟨h.1,fun i => h.2 (ρ i)⟩
  simp only [action,ite_eq_left h,ite_eq_left hρ,C.jacobian_reindex]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end IntegerChart
namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

lemma IntegerRectifiable.apply_reindex {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (ρ : Fin k → Fin k) :
    T b (π ∘ ρ) = reindexFactor ρ*T b π := by
  obtain ⟨C,_,_,_,hrep⟩ := hT
  rw [hrep,hrep,←tsum_mul_left]
  exact tsum_congr fun j => (C j).action_reindex h ρ

end Foundations
namespace Slicing
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.apply_reindex {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (ρ : Fin k → Fin k) :
    T b (π ∘ ρ) = reindexFactor ρ*T b π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hl := hlim b (π ∘ ρ)
  have hr := (hlim b π).const_mul (reindexFactor ρ)
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_reindex (hrect j) hab ρ
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

end Slicing
namespace BorelCoefficients
open MassMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma borelAction_reindex {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (ρ : Fin k → Fin k) (hρ : ∀ b, BoundedLip b → T b (π ∘ ρ) = reindexFactor ρ*T b π)
    {f : X → ℝ} (hf : Integrable f μ) :
    borelAction μ hT f (π ∘ ρ) = reindexFactor ρ*borelAction μ hT f π := by
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hl := borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg (π ∘ ρ) (fun i => hπ (ρ i))
  have hr := (borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg π hπ).const_mul (reindexFactor ρ)
  have he n : borelAction μ hT (g n).val (π ∘ ρ) =
      reindexFactor ρ*borelAction μ hT (g n).val π := by
    have had : Admissible (g n).val (π ∘ ρ) := ⟨(g n).property,fun i => hπ (ρ i)⟩
    rw [borelAction_eq μ hT hμ had,
      borelAction_eq μ hT hμ ⟨(g n).property,hπ⟩]
    exact hρ (g n).val (g n).property
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

end BorelCoefficients
namespace BorelRestriction
open MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma restrictCurrent_reindex {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (ρ : Fin k → Fin k) (hρ : ∀ b, BoundedLip b → T b (π ∘ ρ) = reindexFactor ρ*T b π)
    {E : Set X} (hE : MeasurableSet E) {b : X → ℝ} (hb : BoundedLip b) :
    restrictCurrent hT E b (π ∘ ρ) = reindexFactor ρ*restrictCurrent hT E b π := by
  have had : Admissible b (π ∘ ρ) := ⟨hb,fun i => hπ (ρ i)⟩
  rw [restrictCurrent_apply hT E had,
    restrictCurrent_apply hT E ⟨hb,hπ⟩]
  exact borelAction_reindex hT _ (currentMassMeasure_controls hT) hπ ρ hρ
    ((integrable_boundedLip _ hb).indicator hE)

end BorelRestriction
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_Identification
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma chart_mass_compl_image_zero {k : ℕ} (C : IntegerChart X k)
    (hC : IsMetricCurrent C.action) : currentMassMeasure hC C.imageᶜ = 0 := by
  have he := C.restrictCurrent_image_eq hC C.measurableSet_image (subset_refl _)
  have hs := massMeasure_restrict_compl_zero hC C.measurableSet_image
  simpa only [he] using hs

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem joint_graph_restriction_eq_chart {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, ∃ L U : ℝ≥0, LipschitzWith L (fun t => γ t j) ∧
      AntilipschitzWith U (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    (j : Fin m) :
    restrictCurrent h.metric (Set.range (fun t => γ t j)) =
      (jointGraphChart hD (fun t => γ t j) (hγ j) (a j)).action := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let C := jointGraphChart hD (fun t => γ t j) (hγ j) (a j)
  let E := Set.range (fun t => γ t j)
  have hγc (i : Fin m) : Continuous (fun t => γ t i) := (hγ i).choose_spec.choose_spec.1.continuous
  have hE : MeasurableSet E := (isCompact_range (hγc j)).measurableSet
  have hR := restrictCurrent_isMetricCurrent h.metric hE
  have hC : IsMetricCurrent C.action := C.action_isMetricCurrent
  apply current_eq_on_joint_graph (currentMassMeasure hR) hR hC
    (currentMassMeasure_controls hR) (currentMassMeasure hC) (currentMassMeasure_controls hC)
    hD (fun t => γ t j) (hγ j).choose_spec.choose_spec.1 π (fun i => (hπ i).1)
    (fun t => hbase t j) (massMeasure_restrict_compl_zero h.metric hE)
  · have he : C.image = E := jointGraphChart_image hD _ (hγ j) (a j)
    simpa only [he] using chart_mass_compl_image_zero C hC
  intro ρ b hb
  rw [restrictCurrent_reindex h.metric (fun i => (hπ i).1) ρ
      (fun b hb => h.apply_reindex ⟨hb,fun i => (hπ i).1⟩ ρ) hE hb,
    C.action_reindex ⟨hb,fun i => (hπ i).1⟩ ρ,
    full_graph_restriction_base_action h hX π hπ hD γ hγ a hbase hinj hrep j hb]

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_JointCharts
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma restrictCurrent_congr {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {S U : Functional X k}
    (hS : IsMetricCurrent S) (hU : IsMetricCurrent U) (he : S = U) (E : Set X) :
    restrictCurrent hS E = restrictCurrent hU E := by
  subst U
  rfl

lemma integerRectifiable_of_chart_restrictions {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (C : ℕ → IntegerChart X k)
    (hact : ∀ i, (C i).action = restrictCurrent hT (C i).image)
    (hcover : currentMassMeasure hT (⋃ i, (C i).image)ᶜ = 0) :
    IntegerRectifiable T := by
  classical
  let Z : ℕ → Set X := disjointed (fun i => (C i).image)
  have hZ i : MeasurableSet (Z i) := MeasurableSet.disjointed (fun j => (C j).measurableSet_image) i
  have hd : Pairwise (fun i j => Disjoint (Z i) (Z j)) := disjoint_disjointed _
  have hZi i : Z i ⊆ (C i).image := disjointed_subset _ i
  have hZunion : (⋃ i, Z i) = ⋃ i, (C i).image := iUnion_disjointed
  let D i := (C i).restrictImage (Z i) (hZ i)
  have hDim i : (D i).image = Z i := by
    rw [IntegerChart.restrictImage_image,inter_eq_right.mpr (hZi i)]
  have hDa i : (D i).action = restrictCurrent hT (Z i) := by
    have hC : IsMetricCurrent (C i).action := (C i).action_isMetricCurrent
    have he := (C i).restrictImage_action (Z i) (hZ i) hC
    have hr : restrictCurrent hC (Z i) =
        restrictCurrent (restrictCurrent_isMetricCurrent hT (C i).measurableSet_image) (Z i) := by
      exact restrictCurrent_congr hC
        (restrictCurrent_isMetricCurrent hT (C i).measurableSet_image) (hact i) (Z i)
    exact he.trans (hr.trans (by rw [restrictCurrent_restrict hT (C i).measurableSet_image (hZ i),
      inter_eq_right.mpr (hZi i)]))
  refine ⟨D,?_,?_,?_,?_⟩
  · simpa only [hDim] using hd
  · intro i
    rw [hDa]
    exact restrictCurrent_isMetricCurrent hT (hZ i)
  · simp only [hDa]
    exact summable_restriction_mass hT Z hZ hd
  · intro b π
    rw [show T = restrictCurrent hT (⋃ i, Z i) from
      (restrictCurrent_eq_self_of_mass_compl_zero hT (MeasurableSet.iUnion hZ)
        (by simpa only [hZunion] using hcover)).symm]
    rw [restrictCurrent_iUnion hT Z hZ hd]
    exact tsum_congr fun i => congrFun (congrFun (hDa i).symm b) π

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_joint_chart_mass_cover {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X) :
    ∃ C : FullGraphCode → IntegerChart X (k+1),
      (∀ i, (C i).action = restrictCurrent h.metric (C i).image) ∧
      currentMassMeasure h.metric (⋃ i, (C i).image)ᶜ = 0 := by
  classical
  obtain ⟨b,π,hadm,htests⟩ := exists_countable_current_tests (X := X) (k+1)
  let p (q : ℕ × ℕ) := π q.1 q.2
  have hp (q : ℕ × ℕ) : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (p q i) := (hadm q.1 q.2).2
  have hu (q : ℕ × ℕ) : ∃ K : ℝ≥0, ∀ i, LipschitzWith K (p q i) := by
    choose L hL using hp q
    exact ⟨Finset.univ.sup L,fun i => (hL i).weaken (Finset.le_sup (Finset.mem_univ i))⟩
  choose K hK using hu
  have hpb q i := boundedLip_of_lipschitz (hK q i)
  choose E L U α hEc hEae hαL hαA hαu hαrep hαinj using
    fun q => fullSlice_compact_atom_graphs h hX (p q) (hK q)
  let D (i : FullGraphCode) : Set (Euc (k+1)) := E i.1 i.2.1
  let γ (i : FullGraphCode) (t : D i) : X := α i.1 i.2.1 t i.2.2
  have hD (i : FullGraphCode) : IsCompact (D i) := hEc i.1 i.2.1
  have hγ (i : FullGraphCode) : ∃ K L : ℝ≥0,
      LipschitzWith K (γ i) ∧ AntilipschitzWith L (γ i) :=
    ⟨L i.1 i.2.1,U i.1 i.2.1,hαL i.1 i.2.1 i.2.2,hαA i.1 i.2.1 i.2.2⟩
  let G : Set X := ⋃ i, Set.range (γ i)
  have hGc (i : FullGraphCode) : IsCompact (Set.range (γ i)) := by
    let : CompactSpace (D i) := isCompact_iff_compactSpace.mp (hD i)
    exact isCompact_range (hγ i).choose_spec.choose_spec.1.continuous
  have hG : MeasurableSet G := MeasurableSet.iUnion fun i => (hGc i).measurableSet
  have hrest : restrictCurrent h.metric Gᶜ = fun _ _ => 0 := by
    apply htests _ _ (restrictCurrent_isMetricCurrent h.metric hG.compl) (isMetricCurrent_zero (k+1))
    intro a j
    let q : ℕ × ℕ := (a,j)
    let f : X → ℝ := Gᶜ.indicator (b a j)
    have hf : Measurable f := (hadm a j).1.continuous.measurable.indicator hG.compl
    obtain ⟨B,hBb⟩ := (hadm a j).1.2
    let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
    have hBf (x : X) : |f x| ≤ B' := by
      by_cases hx : x ∈ Gᶜ
      · dsimp only [f]
        rw [indicator_of_mem hx]
        exact (hBb x).trans (le_max_left B 0)
      · simp only [f,indicator_of_notMem hx,abs_zero]
        exact B'.coe_nonneg
    have hslice : ∀ᵐ t : Euc (k+1),
        currentBorelAction (fullSlice h (p q) t) f (fun z => Fin.elim0 z) = 0 := by
      filter_upwards [hEae q] with t ht
      obtain ⟨i,hti⟩ := mem_iUnion.mp ht
      apply (hαrep q i ⟨t,hti⟩).borelAction_zero (fullSlice_integral h (p q) t).1 hf
      intro v
      have hx : α q i ⟨t,hti⟩ v ∈ G := by
        refine mem_iUnion.mpr ⟨⟨q,i,v⟩,?_⟩
        exact ⟨⟨t,hti⟩,rfl⟩
      exact indicator_of_notMem (by simpa only [mem_compl_iff,not_not] using hx) _
    have hagr := fullSlice_borel_integral h hX (p q) (hpb q) hf B' hBf
    dsimp only [ActionIntegralAgreement] at hagr
    rw [integral_eq_zero_of_ae hslice] at hagr
    rw [restrictCurrent_apply h.metric Gᶜ (hadm a j)]
    exact (currentBorelAction_eq h.metric f (π a j)).symm.trans hagr.2
  let C (i : FullGraphCode) : IntegerChart X (k+1) :=
    jointGraphChart (hD i) (γ i) (hγ i) (i.2.1.2.weights i.2.2)
  have hCi (i : FullGraphCode) : (C i).image = Set.range (γ i) := rfl
  refine ⟨C,?_,?_⟩
  · intro i
    rw [hCi]
    exact (joint_graph_restriction_eq_chart h hX (p i.1) (hpb i.1)
      (hEc i.1 i.2.1) (α i.1 i.2.1)
      (fun j => ⟨L i.1 i.2.1,U i.1 i.2.1,hαL i.1 i.2.1 j,hαA i.1 i.2.1 j⟩)
      i.2.1.2.weights (hαu i.1 i.2.1) (hαinj i.1 i.2.1)
      (hαrep i.1 i.2.1) i.2.2).symm
  simp only [hCi]
  have hz : Controls (restrictCurrent h.metric Gᶜ) (0 : Measure X) := by
    rw [hrest]
    intro b π _ _
    simp
  have hm := currentMassMeasure_le (restrictCurrent_isMetricCurrent h.metric hG.compl) hz Set.univ
  rw [restriction_massMeasure h.metric hG.compl,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hm
  exact le_antisymm (by simpa [G] using hm) bot_le

theorem integerRectifiable_succ_of_normalApprox {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X) : IntegerRectifiable T := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_joint_chart_mass_cover h hX
  let : Nonempty FullGraphCode := ⟨⟨(0,0),
    ((0,0,0,0),⟨1,(fun _ => 1),(fun _ => 0),1⟩),0⟩⟩
  obtain ⟨e,he⟩ := exists_surjective_nat FullGraphCode
  apply integerRectifiable_of_chart_restrictions h.metric (C ∘ e) (fun i => hC (e i))
  have hu : (⋃ i, (C (e i)).image) = ⋃ j, (C j).image := by
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i,hi⟩ => ⟨e i,hi⟩,fun ⟨j,hj⟩ => by
      obtain ⟨i,rfl⟩ := he j
      exact ⟨i,hj⟩⟩
  simpa only [Function.comp_apply,hu] using hcover

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Attainment
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations SliceReconstruction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.boundarySucc {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) : NormalApprox k (boundarySucc T) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  refine ⟨C,fun j => CAT0Fillings.boundarySucc (Ts j),fun j => (hTs j).boundarySucc,hN,?_,
    boundarySucc_weak_limit hlim⟩
  intro j
  cases k with
  | zero => simp only [boundary,mass_zero];positivity
  | succ k =>
    change mass (CAT0Fillings.boundarySucc (CAT0Fillings.boundarySucc (Ts j))) ≤ C
    rw [Foundations.boundarySucc_boundarySucc (hTs j).1,mass_zero]
    positivity

lemma NormalApprox.integerRectifiable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X) : IntegerRectifiable T := by
  cases k with
  | zero => exact h.integral_zero.2
  | succ k => exact integerRectifiable_succ_of_normalApprox h hX

theorem NormalApprox.integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X) : IsIntegral k T := by
  cases k with
  | zero => exact h.integral_zero
  | succ k => exact ⟨h.metric,h.integerRectifiable hX,
      h.boundarySucc.metric,h.boundarySucc.integerRectifiable hX⟩

theorem integral_weak_closed {k : ℕ} {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) : IsIntegral k T :=
  (normalApprox_of_weak_limit hTs M N hM hN hlim).integral hX

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_integral_weak_subsequence_oai {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
    (hTs : ∀ j, IsIntegral (k+1+1) (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hX : IsCAT0 X) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ ∃ T : Functional X (k+1+1),
      IsIntegral (k+1+1) T ∧ mass T ≤ M ∧ mass (boundarySucc T) ≤ N ∧
      ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π)) := by
  obtain ⟨ψ,hψ,T,_,_,hTM,hTN,hlim⟩ := exists_normal_weak_subsequence_of_integral_mass_bound hTs M N hM hN
  exact ⟨ψ,hψ,T,integral_weak_closed (fun j => hTs (ψ j)) M N
    (fun j => hM (ψ j)) (fun j => hN (ψ j)) hlim hX,hTM,hTN,hlim⟩

end CAT0Fillings.Slicing
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence_oai.{u_1} := @OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence_oai.{u_1}
