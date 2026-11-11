-- Prove2me | solution 1 for OAI.CKSSchwarzschild.source_minimum_area
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:47:57.142013+00:00
-- url     : https://prove2.me/submissions/0ba0b1dd-31de-4e6b-a1ba-fd97a219352d

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_Q227CKS002

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereCalculus
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FullSphereHeat
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_EmbeddingDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSEmbeddingDerivative
attribute [local instance] halfSpaceDimension_neZero

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [IsManifold I ∞ M] in
lemma extended_chart_derivative_injective [IsManifold I ∞ M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    Injective (mfderiv I 𝓘(ℝ,E) (e.extend I) x) := by
  have hed : e.MDifferentiable I I := ⟨
    (contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp := mfderiv_comp x I.mdifferentiableAt ((hed.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx))
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = _ at hcomp
  rw [I.hasMFDerivAt.mfderiv] at hcomp
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = mfderiv I I e x at hcomp
  rw [hcomp]
  exact hed.mfderiv_injective hx

omit [IsManifold I ∞ N] in
lemma immersion_derivative_injective [IsManifold I ∞ N] {f : M → N} {x : M}
    (h : IsImmersionAt I I ∞ f x) : Injective (mfderiv I I f x) := by
  let A : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E h.complement).comp
    h.equiv.symm.toContinuousLinearMap
  let L : N → E := A ∘ (h.codChart.extend I)
  have hL : ContMDiffAt I 𝓘(ℝ,E) ∞ L (f x) :=
    A.contMDiff.contMDiffAt.comp _
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
  have heq : (L ∘ f) =ᶠ[𝓝 x] h.domChart.extend I := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    dsimp only [Function.comp_apply] at hw
    rw [(h.domChart.extend I).left_inv hy'] at hw
    change A ((h.codChart.extend I) (f y)) = _
    rw [hw]
    simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply ]
    rfl
  have hdL := hL.mdifferentiableAt (by simp)
  have hdf := h.contMDiffAt.mdifferentiableAt (by simp)
  have hder := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ,E))
  rw [mfderiv_comp x hdL hdf] at hder
  change _ = mfderiv I 𝓘(ℝ,E) (h.domChart.extend I) x at hder
  have hinj := extended_chart_derivative_injective h.domChart h.domChart_mem_maximalAtlas
    h.mem_domChart_source
  rw [← hder] at hinj
  have hi' : Injective ((mfderiv I 𝓘(ℝ,E) L (f x)) ∘ (mfderiv I I f x)) := hinj
  exact hi'.of_comp

lemma smooth_embedding_derivative_injective {f : M → N} (h : IsSmoothEmbedding I I ∞ f) :
    ∀ x, Injective (mfderiv I I f x) := fun x =>
  immersion_derivative_injective (h.isImmersion.isImmersionAt x)

end CKSEmbeddingDerivative

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceVolume
attribute [-simp] _root_.OAI.CKSSurfaceVolume.scaledMetric_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartFrame_eq_symmL (x : M) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartFrame x y = (trivializationAt E (TangentSpace I) x).symmL ℝ
      ((extChartAt I x).symm y) := by
  have hs : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hy
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt I x).right_inv hy]
  rfl

lemma chartFrame_continuousOn (x : M) (v : E) :
    ContinuousOn (fun y => (⟨(extChartAt I x).symm y, chartFrame x y v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target := by
  let e := trivializationAt E (TangentSpace I) x
  have h : ContinuousOn (fun y =>
      (⟨(extChartAt I x).symm y, e.symm ((extChartAt I x).symm y) v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target :=
    e.continuousOn_symm.comp
      ((continuousOn_extChartAt_symm x).prodMk continuousOn_const)
      (fun y hy => ⟨by simpa [e] using (extChartAt I x).map_target hy, mem_univ _⟩)
  apply h.congr
  intro y hy
  dsimp only
  congr 1
  rw [chartFrame_eq_symmL x hy, Trivialization.symmL_apply]
  simpa using (extChartAt I x).map_target hy

lemma chartMatrix_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartMatrix g x) (extChartAt I x).target := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact (chartFrame_continuousOn x (basis i)).inner_bundle
    (chartFrame_continuousOn x (basis j))

lemma chartDensity_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartDensity g x) (extChartAt I x).target := by
  exact ((continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ)).comp_continuousOn (chartMatrix_continuousOn g x)).sqrt

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma sqrt_gram_det_comp (B : LinearMap.BilinForm ℝ E) (L : E →L[ℝ] E) :
    Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis
      (B.comp L.toLinearMap L.toLinearMap)).det =
      |L.det| * Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis B).det := by
  rw [LinearMap.BilinForm.toMatrix_comp stdBasis stdBasis,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  change Real.sqrt (L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det) = _
  rw [show L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det =
    L.det ^ 2 * (LinearMap.BilinForm.toMatrix stdBasis B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartMatrix_eq_toMatrix (g : Metric (M := M)) (x : M) (y : E) :
    chartMatrix g x y = LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x y) := by
  rfl

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

attribute [local instance] real_id_compTriple

lemma hasFDerivWithinAt_chartTransition (x z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target)
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y) (range I) y := by
  have hxs : (extChartAt I z).symm y ∈ (chartAt H x).source := by simpa using hx
  exact ((mdifferentiableAt_extChartAt hxs).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt).hasFDerivWithinAt

lemma chartFrame_comp_transitionDeriv (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    (chartFrame x (chartTransition x z y)).comp (transitionDeriv x z y) = chartFrame z y := by
  unfold transitionDeriv
  change (mfderivWithin 𝓘(ℝ,E) I (extChartAt I x).symm (range I)
    (extChartAt I x ((extChartAt I z).symm y))).comp
    ((mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp
    (chartFrame z y)) = chartFrame z y
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx]
  rfl

lemma pullbackInner_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    pullbackInner g z y = (pullbackInner g x (chartTransition x z y)).comp
      (transitionDeriv x z y).toLinearMap (transitionDeriv x z y).toLinearMap := by
  ext v w
  change g.inner ((extChartAt I z).symm y) (chartFrame z y v) (chartFrame z y w) =
    g.inner ((extChartAt I x).symm (chartTransition x z y))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y v))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (chartFrame_comp_transitionDeriv x z hx)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (chartFrame_comp_transitionDeriv x z hx)
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y v) = _ at hv
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y w) = _ at hw
  rw [hv, hw]
  have heq : (extChartAt I x).symm (chartTransition x z y) = (extChartAt I z).symm y :=
    (extChartAt I x).left_inv hx
  rw [heq]
  rfl

lemma chartDensity_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    chartDensity g z y = |(transitionDeriv x z y).det| *
      chartDensity g x (chartTransition x z y) := by
  simp only [chartDensity, chartMatrix_eq_toMatrix]
  rw [pullbackInner_transition g x z hx, sqrt_gram_det_comp]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

omit [IsManifold I 1 M] in
lemma chart_target_measurable [IsManifold I 1 M] (x : M) :
    MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

variable [MeasurableSpace M] [BorelSpace M]

lemma chartPreimage_measurable (x : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage x s) := by
  have h : Measurable ((extChartAt I x).target.domRestrict (extChartAt I x).symm) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)).measurable
  have hm := (chart_target_measurable x).subtype_image (hs.preimage h)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp [chartPreimage]

lemma localVolume_apply (g : Metric (M := M)) (x : M) {s : Set M} (hs : MeasurableSet s) :
    localVolume g x s = ∫⁻ y in chartPreimage x s, ENNReal.ofReal (chartDensity g x y) := by
  have hf := (continuousOn_extChartAt_symm x).aemeasurable
    (μ := (volume : Measure E)) (chart_target_measurable x)
  rw [localVolume, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm (chart_target_measurable x),
    Measure.restrict_restrict (chart_target_measurable x)]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    chartTransition x z '' chartPreimage z (s ∩ (extChartAt I x).source) =
      chartPreimage x (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u, ⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : (extChartAt I x).symm (chartTransition x z u) = (extChartAt I z).symm u :=
      (extChartAt I x).left_inv hx
    refine ⟨?_, (extChartAt I x).map_source hx⟩
    change (extChartAt I x).symm (chartTransition x z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs, (extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z ((extChartAt I x).symm y), ?_, ?_⟩
    · refine ⟨?_, (extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z ((extChartAt I x).symm y)) ∈
        s ∩ (extChartAt I x).source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs, (extChartAt I x).map_target hy⟩
    · change extChartAt I x ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x).symm y))) = y
      rw [(extChartAt I z).left_inv hz, (extChartAt I x).right_inv hy]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    InjOn (chartTransition x z) (chartPreimage z (s ∩ (extChartAt I x).source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact (extChartAt I x).injOn hu.1.2 hv.1.2 heq

lemma localVolume_compatible (g : Metric (M := M)) (x z : M) :
    (localVolume g x).restrict (extChartAt I z).source =
      (localVolume g z).restrict (extChartAt I x).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    localVolume_apply g x (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter (isOpen_extChartAt_source x).measurableSet),
    ← chartTransition_image x z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ (extChartAt I x).source),
      HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y)
        (chartPreimage z (s ∩ (extChartAt I x).source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_chartTransition x z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
    hd (chartTransition_injOn x z s)]
  apply setLIntegral_congr_fun
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_transition g x z hy.1.2, ENNReal.ofReal_mul (abs_nonneg _)]

end CKSSurfaceVolume

end

noncomputable section
open Set MeasureTheory
namespace CKSSurfaceVolume

lemma exists_measure_of_compatible {X ι : Type*} [MeasurableSpace X]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (μ : ι → Measure X)
    (hc : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (f : ℕ → ι) (hf : ⋃ n, U (f n) = univ) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  let D := disjointed (U ∘ f)
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => hU (f n))
  refine ⟨Measure.sum (fun n => (μ (f n)).restrict (D n)), fun i => ?_⟩
  rw [Measure.restrict_sum _ (hU i)]
  have heq : ∀ n, ((μ (f n)).restrict (D n)).restrict (U i) = (μ i).restrict (D n) := by
    intro n
    rw [Measure.restrict_comm (hU i), hc (f n) i]
    exact Measure.restrict_restrict_of_subset (disjointed_subset (U ∘ f) n)
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed (U ∘ f)) hD,
    show (⋃ n, D n) = univ from (iUnion_disjointed.trans hf), Measure.restrict_univ]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem exists_volume (g : Metric (M := M)) : ∃ ν : Measure M, IsVolume g ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact exists_measure_of_compatible (fun x : M => (extChartAt I x).source)
      (fun x => (isOpen_extChartAt_source x).measurableSet) (localVolume g)
      (localVolume_compatible g) f (eq_univ_of_univ_subset hf)

omit [SecondCountableTopology M] in
lemma volume_on_subset [SecondCountableTopology M] (g : Metric (M := M))
    {ν : Measure M} (hν : IsVolume g ν)
    (x : M) {s : Set M} (hs : s ⊆ (extChartAt I x).source) :
    ν s = (localVolume g x) s := by
  rw [← hν x, Measure.restrict_apply' (isOpen_extChartAt_source x).measurableSet,
    inter_eq_left.mpr hs]

lemma volume_locallyFinite (g : Metric (M := M)) {ν : Measure M} (hν : IsVolume g ν) :
    IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨δ,hδ,hbound⟩ := (Metric.continuousWithinAt_iff.mp
    (chartDensity_continuousOn g x _ hx)) 1 zero_lt_one
  let V := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) δ
  have hVo : IsOpen V := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, by simpa using hδ⟩
  refine ⟨V, hVo.mem_nhds hxV, ?_⟩
  rw [volume_on_subset g hν x (inter_subset_left), localVolume_apply g x hVo.measurableSet]
  let C := chartDensity g x (extChartAt I x x) + 1
  have hpre : chartPreimage x V ⊆ Metric.ball (extChartAt I x x) δ := by
    intro y hy
    have he : extChartAt I x ((extChartAt I x).symm y) = y := (extChartAt I x).right_inv hy.2
    simpa only [mem_preimage,he] using hy.1.2
  have hden : ∀ y ∈ chartPreimage x V, chartDensity g x y ≤ C := by
    intro y hy
    have hb := hbound hy.2 (hpre hy)
    rw [Real.dist_eq] at hb
    exact le_of_lt (by linarith [(abs_lt.mp hb).2])
  calc
    ∫⁻ y in chartPreimage x V, ENNReal.ofReal (chartDensity g x y) ≤
        ∫⁻ _y in chartPreimage x V, ENNReal.ofReal C :=
      setLIntegral_mono measurable_const (fun y hy => ENNReal.ofReal_le_ofReal (hden y hy))
    _ = ENNReal.ofReal C * volume (chartPreimage x V) := by simp
    _ ≤ ENNReal.ofReal C * volume (Metric.ball (extChartAt I x x) δ) :=
      mul_le_mul_right (measure_mono hpre) _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Metric.isBounded_ball.measure_lt_top)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma measure_eq_of_restrict_cover {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ⋃ n, U n = univ) (heq : ∀ n, μ.restrict (U n) = ν.restrict (U n)) : μ = ν := by
  let D := disjointed U
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hU
  have hDc : ⋃ n, D n = univ := iUnion_disjointed.trans hcover
  have hrestr : ∀ n, μ.restrict (D n) = ν.restrict (D n) := by
    intro n
    rw [← Measure.restrict_restrict_of_subset (disjointed_subset U n),heq n,
      Measure.restrict_restrict_of_subset (disjointed_subset U n)]
  calc
    μ = μ.restrict (⋃ n, D n) := by rw [hDc,Measure.restrict_univ]
    _ = Measure.sum (fun n => μ.restrict (D n)) :=
      Measure.restrict_iUnion (disjoint_disjointed U) hD
    _ = Measure.sum (fun n => ν.restrict (D n)) := by simp_rw [hrestr]
    _ = ν.restrict (⋃ n, D n) := (Measure.restrict_iUnion (disjoint_disjointed U) hD).symm
    _ = ν := by rw [hDc,Measure.restrict_univ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [IsManifold I 1 M] in
lemma measure_eq_of_chart_restrict [IsManifold I 1 M] {μ ν : Measure M}
    (heq : ∀ x : M, μ.restrict (extChartAt I x).source = ν.restrict (extChartAt I x).source) :
    μ = ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact measure_eq_of_restrict_cover μ ν (fun n => (extChartAt I (f n)).source)
      (fun n => (isOpen_extChartAt_source (f n)).measurableSet)
      (eq_univ_of_univ_subset hf) (fun n => heq (f n))

lemma volume_unique (g : Metric (M := M)) {μ ν : Measure M}
    (hμ : IsVolume g μ) (hν : IsVolume g ν) : μ = ν :=
  measure_eq_of_chart_restrict (fun x => (hμ x).trans (hν x).symm)

lemma riemannianVolume_isVolume (g : Metric (M := M)) : IsVolume g (riemannianVolume g) :=
  Classical.epsilon_spec (exists_volume g)
instance riemannianVolume_locallyFinite (g : Metric (M := M)) :
    IsLocallyFiniteMeasure (riemannianVolume g) := volume_locallyFinite g (riemannianVolume_isVolume g)

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_CutSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Function
open scoped ContDiff Topology
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

lemma cutInclusion_smooth [IsManifold I3 ∞ N] (D : OuterDomain N) :
    ContMDiff I2 I3 ∞ (cutInclusion D) :=
  D.embedding.isImmersion.contMDiff.comp CKSBoundarySurface.inclusion_smooth

lemma cutInclusion_embedding [IsManifold I3 ∞ N] (D : OuterDomain N) :
    Topology.IsEmbedding (cutInclusion D) :=
  D.embedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal

variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

instance surfaceT2 [T2Space N] (D : OuterDomain N) : T2Space (Surface D) :=
  (cutInclusion_embedding D).t2Space

end CKSFullCutArea

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma det_two_add_smul_lower (A D : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    c^2 * A.det ≤ (c • A + D).det := by
  have hAs : A 1 0 = A 0 1 := by simpa using hA.1.apply 0 1
  have hDs : D 1 0 = D 0 1 := by simpa using hD.1.apply 0 1
  have hA0 : 0 ≤ A 0 0 := hA.diag_nonneg
  have hA1 : 0 ≤ A 1 1 := hA.diag_nonneg
  have hD0 : 0 ≤ D 0 0 := hD.diag_nonneg
  have hD1 : 0 ≤ D 1 1 := hD.diag_nonneg
  have ha : (A 0 1)^2 ≤ A 0 0 * A 1 1 := by
    have h := hA.det_nonneg
    rw [Matrix.det_fin_two,hAs] at h
    nlinarith
  have hd : (D 0 1)^2 ≤ D 0 0 * D 1 1 := by
    have h := hD.det_nonneg
    rw [Matrix.det_fin_two,hDs] at h
    nlinarith
  have hp : (A 0 1 * D 0 1)^2 ≤ (A 0 0 * D 1 1) * (A 1 1 * D 0 0) := by
    have h := mul_le_mul ha hd (sq_nonneg (D 0 1)) (mul_nonneg hA0 hA1)
    nlinarith only [h]
  have hcross := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hA0 hD1) (mul_nonneg hA1 hD0) hp
  have hcross' : 0 ≤ A 0 0 * D 1 1 + A 1 1 * D 0 0 - 2*A 0 1*D 0 1 := by
    linarith
  have hfinal := mul_nonneg hc hcross'
  have hdd := hD.det_nonneg
  simp only [Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hAs,hDs] at hdd ⊢
  nlinarith only [hfinal,hdd]

lemma sqrt_det_two_lower (A G : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (hlow : (G-c•A).PosSemidef) :
    c * Real.sqrt A.det ≤ Real.sqrt G.det := by
  have h := det_two_add_smul_lower A (G-c•A) hA hlow hc
  rw [add_sub_cancel] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc] at hs
  exact hs

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceVolumeLower
attribute [-simp] _root_.OAI.CKSSurfaceVolume.scaledMetric_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma metric_nonneg (g : Metric (M := M)) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_CutArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [SecondCountableTopology N]

theorem area_finite (g : SmoothMetric (N := N)) (D : OuterDomain N) : area g D < ⊤ := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  exact isCompact_univ.measure_lt_top

end CKSFullCutArea

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_EmbeddingOpenInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Function
open scoped ContDiff Topology
namespace CKSEmbeddingDerivative
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

lemma image_interior_mem_nhds {f : M → N} (hf : IsSmoothEmbedding I I ∞ f)
    {x : M} (hx : x ∈ I.interior M) : f '' I.interior M ∈ 𝓝 (f x) := by
  have hmd := (hf.isImmersion.contMDiff x).mdifferentiableAt (by simp)
  let A : E →L[ℝ] E := mfderiv I I f x
  have hA : Injective A := smooth_embedding_derivative_injective hf x
  have hb : Bijective (mfderiv I I f x) :=
    ⟨hA, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hA⟩
  let F := writtenInExtChartAt I I x f
  let z := extChartAt I x x
  have hrange : range I ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hx
  have hF : ContDiffAt ℝ ∞ F z :=
    (contMDiffAt_iff.mp (hf.isImmersion.contMDiff x)).2.contDiffAt hrange
  have hbF : Bijective (fderiv ℝ F z) := by
    simp only [mfderiv,hmd,ite_true, if_true] at hb
    rwa [fderivWithin_eq_fderiv (I.uniqueDiffOn _ (mem_of_mem_nhds hrange))
      (hF.differentiableAt (by simp))] at hb
  let L : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F z).toLinearMap hbF).toContinuousLinearEquiv
  have hL : L.toContinuousLinearMap = fderiv ℝ F z := by ext v; rfl
  have hd : HasFDerivAt F (L : E →L[ℝ] E) z := by
    rw [hL]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  let e := hF.toOpenPartialHomeomorph F hd (by simp)
  have he : z ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : I.interior M ∈ 𝓝 x := (I.isOpen_interior (by simp : (∞ : ℕ∞ω) ≠ 0)).mem_nhds hx
  have hs : f ⁻¹' (extChartAt I (f x)).source ∈ 𝓝 x :=
    hmd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x))
  let V := (extChartAt I x).symm ⁻¹' (I.interior M ∩ f ⁻¹' (extChartAt I (f x)).source)
  have hV : V ∈ 𝓝 z := extChartAt_preimage_mem_nhds (inter_mem hi hs)
  have hFz : e z = extChartAt I (f x) (f x) := by
    change extChartAt I (f x) (f ((extChartAt I x).symm (extChartAt I x x))) = _
    rw [extChartAt_to_inv]
  have him : e '' V ∈ 𝓝 (extChartAt I (f x) (f x)) := hFz ▸ e.image_mem_nhds he hV
  have hp := (continuousAt_extChartAt (I := I) (f x)).preimage_mem_nhds him
  apply mem_of_superset (inter_mem (extChartAt_source_mem_nhds (I := I) (f x)) hp)
  rintro y ⟨hy, w, hw, hew⟩
  refine ⟨(extChartAt I x).symm w,hw.1,?_⟩
  have heq : extChartAt I (f x) (f ((extChartAt I x).symm w)) = extChartAt I (f x) y := hew
  exact (extChartAt I (f x)).injOn hw.2 hy heq

lemma image_interior_isOpen {f : M → N} (hf : IsSmoothEmbedding I I ∞ f) :
    IsOpen (f '' I.interior M) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x,hx,rfl⟩
  exact image_interior_mem_nhds hf hx

end CKSEmbeddingDerivative

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildRoundMetric
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact _root_.OAI.CKSFullCutArea.surfaceT2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] OAI.CKSSchwarzschild.schwarzschildRoundMetricFinrank
lemma sphereMetric_apply (n : Sphere) (v w : E2) :
    sphereMetric.inner n v w = ⟪sphereDerivative n v,sphereDerivative n w⟫_ℝ := rfl

lemma metricInner_quad {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    metricInner m p v v = (v 0)^2 / lapseSquared m (radius m p) +
      (radius m p)^2 * ‖ambientDerivative directionAmbient p v‖^2 := by
  change cartMetric m (position m p) (ambientDerivative (position m) p v)
    (ambientDerivative (position m) p v) = _
  rw [cartMetric_apply,position_radial_inner hm,norm_position hm]
  have ho : ⟪ambientDerivative directionAmbient p v,directionAmbient p⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact directionAmbient_orthogonal p v
  rw [mfderiv_position,inner_add_left,inner_add_right,inner_add_right]
  have ho' : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 :=
    directionAmbient_orthogonal p v
  simp only [inner_smul_left,inner_smul_right,ho,ho',starRingEnd_apply,star_trivial,
    real_inner_self_eq_norm_sq,norm_direction]
  ring

lemma angular_metric_bound {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    (2*m)^2 * sphereMetric.inner (angular p) (mfderiv I3 I2 angular p v)
      (mfderiv I3 I2 angular p v) ≤ metricInner m p v v := by
  have hs : sphereMetric.inner (angular p) (mfderiv I3 I2 angular p v)
      (mfderiv I3 I2 angular p v) = ‖ambientDerivative directionAmbient p v‖^2 := by
    have ha : (mfderiv I3 I2 angular p : E3 →L[ℝ] E2) = dropPlane := mfderiv_angular p
    have hd : ambientDerivative directionAmbient p = (sphereDerivative p.2).comp dropPlane :=
      mfderiv_directionAmbient p
    change ⟪sphereDerivative p.2 ((mfderiv I3 I2 angular p : E3 →L[ℝ] E2) v),
      sphereDerivative p.2 ((mfderiv I3 I2 angular p : E3 →L[ℝ] E2) v)⟫_ℝ = _
    rw [ha,hd,ContinuousLinearMap.comp_apply,real_inner_self_eq_norm_sq]
    rfl
  rw [hs,metricInner_quad hm]
  have hr := radius_ge m p
  have hm' : 0 ≤ 2*m := by positivity
  have hrad : (2*m)^2 ≤ (radius m p)^2 := sq_le_sq₀ hm' (radius_pos hm p).le |>.mpr hr
  have hmul := mul_le_mul_of_nonneg_right hrad (sq_nonneg ‖ambientDerivative directionAmbient p v‖)
  have hnn := div_nonneg (sq_nonneg (v 0)) (lapseSquared_pos hm (radius_ge m p)).le
  linarith

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] OAI.CKSSurfaceVolume.instNormedAddCommGroupContinuousLinearMapRealIdE
attribute [local instance] OAI.CKSSurfaceVolume.instNormedSpaceRealContinuousLinearMapIdE
local instance instNormedAddCommGroupContinuousLinearMapRealIdE_1_reb0ef2_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance instNormedSpaceRealContinuousLinearMapIdE_1_reb0ef2_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma chartDensity_scaled (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) (x : M) (y : E) :
    chartDensity (scaledMetric g c hc).toContinuousRiemannianMetric x y =
      c * chartDensity g.toContinuousRiemannianMetric x y := by
  have hM : chartMatrix (scaledMetric g c hc).toContinuousRiemannianMetric x y =
      c • chartMatrix g.toContinuousRiemannianMetric x y := by ext i j; rfl
  rw [chartDensity,hM,Matrix.det_smul, Fintype.card_fin,Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc.le]
  rfl

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
lemma riemannianVolume_scaled (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) :
    riemannianVolume (scaledMetric g c hc).toContinuousRiemannianMetric =
      ENNReal.ofReal c • riemannianVolume g.toContinuousRiemannianMetric := by
  apply volume_unique _ (riemannianVolume_isVolume _)
  intro x
  rw [Measure.restrict_smul,(riemannianVolume_isVolume g.toContinuousRiemannianMetric) x]
  apply Measure.ext
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,localVolume_apply _ _ hs,localVolume_apply _ _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [chartDensity_scaled,ENNReal.ofReal_mul hc.le]

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildBoundary
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact _root_.OAI.CKSFullCutArea.surfaceT2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma boundarySphere_symm_chart (p : Sphere) :
    writtenInExtChartAt I2 I2 p boundarySphere.symm =ᶠ[𝓝 (extChartAt I2 p p)] id := by
  filter_upwards [extChartAt_target_mem_nhds p] with z hz
  change dropPlane (I3 (chartAt H3 (boundarySphere.symm p).val
    (boundarySphere.symm ((extChartAt I2 p).symm z)).val)) = z
  change dropPlane (join (0, chartAt E2 p ((extChartAt I2 p).symm z))) = z
  rw [drop_join]
  exact (extChartAt I2 p).right_inv hz

lemma boundarySphere_symm_smooth : ContMDiff I2 I2 ∞ boundarySphere.symm := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨boundarySphere.symm.continuous.continuousAt,?_⟩
  apply contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
    ((boundarySphere_symm_chart p).filter_mono nhdsWithin_le_nhds)
  exact (boundarySphere_symm_chart p).self_of_nhds

lemma mfderiv_boundarySphere_symm (p : Sphere) :
    mfderiv I2 I2 boundarySphere.symm p = ContinuousLinearMap.id ℝ E2 := by
  have h : HasMFDerivAt I2 I2 boundarySphere.symm p (ContinuousLinearMap.id ℝ E2) := by
    refine ⟨boundarySphere.symm.continuous.continuousAt,?_⟩
    exact (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
      ((boundarySphere_symm_chart p).filter_mono nhdsWithin_le_nhds)
      ((boundarySphere_symm_chart p).self_of_nhds)
  exact h.mfderiv

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

theorem full_cut_radial_projection_surjective (D : CKSGeometricCuts.OuterDomain Exterior) :
    Function.Surjective (fun z : CKSFullCutArea.Surface D => (CKSFullCutArea.cutInclusion D z).2) := by
  intro n
  by_contra hnone
  have hnone' : ∀ x ∈ I3.boundary D.Carrier, (D.inclusion x).2 ≠ n := by
    intro x hx he
    exact hnone ⟨⟨x,hx⟩,he⟩
  have hinner : ∀ t : Radial, (t,n) ∈ range D.inclusion ↔
      (t,n) ∈ D.inclusion '' I3.interior D.Carrier := by
    intro t
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨x,?_,hx⟩
      by_contra hxi
      have hxb : x ∈ I3.boundary D.Carrier :=
        (I3.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hxi
      exact hnone' x hxb (congrArg Prod.snd hx)
    · rintro ⟨x,_,hx⟩
      exact ⟨x,hx⟩
  let s : Set Radial := (fun t => (t,n)) ⁻¹' range D.inclusion
  have hseq : s = (fun t : Radial => (t,n)) ⁻¹' (D.inclusion '' I3.interior D.Carrier) := by
    ext t; exact hinner t
  have hsc : IsClosed s := D.closed.preimage (continuous_id.prodMk continuous_const)
  have hso : IsOpen s := by
    rw [hseq]
    exact (CKSEmbeddingDerivative.image_interior_isOpen D.embedding).preimage
      (continuous_id.prodMk continuous_const)
  have hsne : s.Nonempty := by
    obtain ⟨K,hK,hfar⟩ := D.contains_distant_end
    have hc : Continuous (fun p : Exterior => p.1.val) := continuous_subtype_val.comp continuous_fst
    obtain ⟨B,hB⟩ := (hK.image hc).bddAbove
    let t : Radial := ⟨max 0 B + 1,by positivity⟩
    refine ⟨t,hfar ?_⟩
    intro hmem
    have hb := hB (mem_image_of_mem (fun p : Exterior => p.1.val) hmem)
    have hm := le_max_right (0 : ℝ) B
    change max 0 B + 1 ≤ B at hb
    linarith
  let : ConnectedSpace Radial := isConnected_iff_connectedSpace.mp isConnected_Ici
  have hsall : s = univ := (IsClopen.eq_univ ⟨hsc,hso⟩ hsne)
  have hz : ((⟨0,le_rfl⟩ : Radial),n) ∈ D.inclusion '' I3.interior D.Carrier :=
    (hinner _).mp (by change (⟨0,le_rfl⟩ : Radial) ∈ s; rw [hsall]; trivial)
  have hout := D.interior_into hz
  have hpos := (interior_iff ((⟨0,le_rfl⟩ : Radial),n)).mp hout
  exact (lt_irrefl (0 : ℝ)) hpos

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeAlgebra
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceT2
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma coneLinear_basis_zero (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) :
    coneLinear r n A (EuclideanSpace.basisFun (Fin 3) ℝ 0) = n := by
  have hd : dropPlane (EuclideanSpace.basisFun (Fin 3) ℝ 0) = 0 := by
    ext index; simp
  rw [coneLinear_apply,hd,map_zero A,smul_zero,add_zero]
  have h0 : (EuclideanSpace.basisFun (Fin 3) ℝ 0) 0 = 1 := by simp
  rw [h0,one_smul]
lemma coneLinear_basis_succ (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3) (i : Fin 2) :
    coneLinear r n A (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      r • A (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  rw [coneLinear_apply]
  have h0 : (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) 0 = 0 := by simp
  have hd : dropPlane (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext j
    simp [EuclideanSpace.basisFun_apply,EuclideanSpace.single]
  rw [h0,hd,zero_smul,zero_add]

lemma abs_det_coneLinear (r : ℝ) (n : E3) (A : E2 →L[ℝ] E3)
    (hn : ‖n‖ = 1) (hA : ∀ v, ⟪n,A v⟫_ℝ = 0) :
    |(coneLinear r n A).det| = r^2 * Real.sqrt
      (Matrix.gram ℝ (fun i : Fin 2 => A (EuclideanSpace.basisFun (Fin 2) ℝ i))).det := by
  let B := EuclideanSpace.basisFun (Fin 3) ℝ
  let C := EuclideanSpace.basisFun (Fin 2) ℝ
  have hnorm := (coneLinear r n A).toLinearMap.normDet_sq_eq_det_gram B
  rw [LinearMap.normDet_eq_norm_det,Real.norm_eq_abs] at hnorm
  have hGram : (Matrix.gram ℝ (fun i : Fin 3 => coneLinear r n A (B i))).det =
      r^4 * (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det := by
    have hAn : ∀ v, ⟪A v,n⟫_ℝ = 0 := fun v => (real_inner_comm _ _).trans (hA v)
    simp only [Matrix.det_fin_three,Matrix.det_fin_two,Matrix.gram_apply,B,C]
    simp only [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
      show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
      coneLinear_basis_zero,coneLinear_basis_succ,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial,hA,hAn,real_inner_self_eq_norm_sq,hn]
    ring
  change |(coneLinear r n A).det| ^ 2 =
    (Matrix.gram ℝ (fun i : Fin 3 => coneLinear r n A (B i))).det at hnorm
  rw [hGram] at hnorm
  have hnn : 0 ≤ (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs := Real.sq_sqrt hnn
  have hpos : 0 ≤ r^2 * Real.sqrt (Matrix.gram ℝ (fun i : Fin 2 => A (C i))).det := by positivity
  apply (sq_eq_sq₀ (abs_nonneg _) hpos).mp
  rw [mul_pow,Real.sq_sqrt hnn,← pow_mul]
  exact hnorm

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeChart
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceT2
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance sphereConeChartFinrank : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

lemma sphereParam_norm (p : Sphere) (y : E2) : ‖sphereParam p y‖ = 1 := by
  simpa only [sphereParam,Metric.mem_sphere,dist_zero_right] using ((extChartAt I2 p).symm y).property
lemma sphereParamDeriv_orthogonal (p : Sphere) (y : E2) (v : E2) :
    ⟪sphereParam p y,sphereParamDeriv p y v⟫_ℝ = 0 := by
  have orthogonalRange : (sphereDerivative ((extChartAt I2 p).symm y)).range =
      (ℝ ∙ (((extChartAt I2 p).symm y).val : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal (n := 2) ((extChartAt I2 p).symm y)
  have hv : sphereParamDeriv p y v ∈ (ℝ ∙ sphereParam p y)ᗮ := by
    change sphereParamDeriv p y v ∈ (ℝ ∙ (((extChartAt I2 p).symm y).val : E3))ᗮ
    rw [← orthogonalRange]
    exact ⟨CKSSurfaceVolume.chartFrame p y v,rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv
lemma sphereParam_hasFDerivAt (p : Sphere) {y : E2}
    (hy : y ∈ (extChartAt I2 p).target) : HasFDerivAt (sphereParam p) (sphereParamDeriv p y) y := by
  have hi := (mdifferentiableWithinAt_extChartAt_symm (I := I2) hy).hasMFDerivWithinAt
  have hc := ((contMDiff_coe_sphere (n := 2) (m := ∞) ((extChartAt I2 p).symm y)).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have h := hc.comp_hasMFDerivWithinAt y hi
  have hh : HasFDerivWithinAt (sphereParam p) (sphereParamDeriv p y) univ y := by
    have hh := h.hasFDerivWithinAt
    change HasFDerivWithinAt (sphereParam p) (sphereParamDeriv p y) (range (id : E2 → E2)) y at hh
    simpa only [range_id] using hh
  exact hh.hasFDerivAt (by simp)

lemma sphereParamDeriv_density (p : Sphere) (y : E2) :
    Real.sqrt (Matrix.gram ℝ (fun i : Fin 2 => sphereParamDeriv p y
      (EuclideanSpace.basisFun (Fin 2) ℝ i))).det =
      CKSSurfaceVolume.chartDensity sphereMetric.toContinuousRiemannianMetric p y := by
  congr 2
  ext i j
  simp only [CKSSurfaceVolume.chartMatrix,Matrix.gram_apply,EuclideanSpace.basisFun_apply]
  rfl

lemma sphereCone_hasFDerivAt (p : Sphere) {z : E3}
    (hz : dropPlane z ∈ (extChartAt I2 p).target) :
    HasFDerivAt (sphereCone p) (sphereConeDeriv p z) z := by
  have h := firstCoordinate.hasFDerivAt.smul
    ((sphereParam_hasFDerivAt p hz).comp z dropPlane.hasFDerivAt)
  change HasFDerivAt (sphereCone p)
    ((z 0) • (sphereParamDeriv p (dropPlane z)).comp dropPlane +
      firstCoordinate.smulRight (sphereParam p (dropPlane z))) z at h
  have he : ((z 0) • (sphereParamDeriv p (dropPlane z)).comp dropPlane +
      firstCoordinate.smulRight (sphereParam p (dropPlane z))) = sphereConeDeriv p z := by
    apply ContinuousLinearMap.ext
    intro v
    change (z 0) • sphereParamDeriv p (dropPlane z) (dropPlane v) +
      (v 0) • sphereParam p (dropPlane z) =
      (v 0) • sphereParam p (dropPlane z) + (z 0) • sphereParamDeriv p (dropPlane z) (dropPlane v)
    exact add_comm _ _
  rw [he] at h
  exact h
lemma sphereCone_det (p : Sphere) (z : E3) :
    |(sphereConeDeriv p z).det| = (z 0)^2 *
      CKSSurfaceVolume.chartDensity sphereMetric.toContinuousRiemannianMetric p (dropPlane z) := by
  rw [sphereConeDeriv,abs_det_coneLinear _ _ _ (sphereParam_norm _ _) (sphereParamDeriv_orthogonal _ _),
    sphereParamDeriv_density]

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeMeasure
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceT2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma splitEuclidean_preserves_volume : MeasurePreserving splitEuclidean volume volume := by
  have ha := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hb := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 2))
  have h := hb.comp ha
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals rfl
lemma join_preserves_volume : MeasurePreserving join volume volume :=
  splitEuclidean_preserves_volume.symm splitEuclidean.toMeasurableEquiv

lemma lintegral_radial_square : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r^2) = ENNReal.ofReal (1/3 : ℝ) := by
  have hn : ∀ᵐ r ∂(volume.restrict (Ioo (0:ℝ) 1)), 0 ≤ r^2 := Filter.Eventually.of_forall sq_nonneg
  have hi : IntegrableOn (fun r : ℝ => r^2) (Ioo 0 1) :=
    ((continuous_id.pow 2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [integral_pow]

lemma lintegral_join_product (s : Set E2) (f : E2 → ℝ)
    (hf : AEMeasurable f (volume.restrict s)) :
    ∫⁻ z in join '' (Ioo (0 : ℝ) 1 ×ˢ s), ENNReal.ofReal ((z 0)^2 * f (dropPlane z)) =
      ENNReal.ofReal (1/3 : ℝ) * ∫⁻ y in s, ENNReal.ofReal (f y) := by
  rw [← join_preserves_volume.setLIntegral_comp_emb splitEuclidean.symm.measurableEmbedding]
  simp only [join_zero,drop_join]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r^2))
    (g := fun y : E2 => ENNReal.ofReal (f y)) (by fun_prop)
    (ENNReal.measurable_ofReal.comp_aemeasurable hf)]
  rw [lintegral_radial_square]

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereVolume
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceT2
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSurfaceVolume.scaledMetric_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Pointwise
namespace CKSSchwarzschild
open CKSBoundarySurface CKSSurfaceVolume

local instance sphereVolumeFinrank_reb0ef2_1 : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩
lemma sphereCone_injOn (p : Sphere) {s : Set E2} (hs : s ⊆ (extChartAt I2 p).target) :
    InjOn (sphereCone p) (join '' (Ioo (0 : ℝ) 1 ×ˢ s)) := by
  rintro z ⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩ w ⟨⟨t,x⟩,⟨ht,hx⟩,rfl⟩ he
  simp only [sphereCone,join_zero,drop_join] at he
  have hn := congrArg norm he
  simp only [norm_smul,sphereParam_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr.1,abs_of_pos ht.1] at hn
  subst t
  have hparam : sphereParam p y = sphereParam p x :=
    (smul_right_injective E3 (ne_of_gt hr.1)) he
  have hinv : (extChartAt I2 p).symm y = (extChartAt I2 p).symm x := Subtype.ext hparam
  have heq : y=x := (extChartAt I2 p).symm.injOn (hs hy) (hs hx) hinv
  rw [heq]

lemma sphereCone_image (p : Sphere) (s : Set Sphere) :
    sphereCone p '' (join '' (Ioo (0 : ℝ) 1 ×ˢ chartPreimage p s)) =
      Ioo (0 : ℝ) 1 • ((Subtype.val : Sphere → E3) '' (s ∩ (extChartAt I2 p).source)) := by
  ext z
  constructor
  · rintro ⟨w,⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩,rfl⟩
    refine ⟨r,hr,sphereParam p y,?_,?_⟩
    · exact ⟨(extChartAt I2 p).symm y,⟨hy.1,(extChartAt I2 p).map_target hy.2⟩,rfl⟩
    · simp [sphereCone]
  · rintro ⟨r,hr,n,⟨q,⟨hqs,hqp⟩,rfl⟩,rfl⟩
    refine ⟨join (r,extChartAt I2 p q),?_,?_⟩
    · refine ⟨(r,extChartAt I2 p q),⟨hr,?_,(extChartAt I2 p).map_source hqp⟩,rfl⟩
      change (extChartAt I2 p).symm (extChartAt I2 p q) ∈ s
      rwa [(extChartAt I2 p).left_inv hqp]
    · simp only [sphereCone,join_zero,drop_join,sphereParam,(extChartAt I2 p).left_inv hqp]

lemma sphere_toSphere_local (p : Sphere) {s : Set Sphere} (hs : MeasurableSet s) :
    (volume : Measure E3).toSphere (s ∩ (extChartAt I2 p).source) =
      localVolume sphereMetric.toContinuousRiemannianMetric p s := by
  let D := chartPreimage p s
  let U := join '' (Ioo (0:ℝ) 1 ×ˢ D)
  have hD : MeasurableSet D := chartPreimage_measurable p hs
  have hU : MeasurableSet U := splitEuclidean.symm.measurableEmbedding.measurableSet_image.mpr
    (measurableSet_Ioo.prod hD)
  have hd : ∀ z ∈ U, HasFDerivWithinAt (sphereCone p) (sphereConeDeriv p z) U z := by
    rintro z ⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩
    apply (sphereCone_hasFDerivAt p ?_).hasFDerivWithinAt
    simpa only [drop_join] using hy.2
  have hJ := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure E3) hU hd
    (sphereCone_injOn p (fun y hy => hy.2))
  have hf : AEMeasurable (chartDensity sphereMetric.toContinuousRiemannianMetric p) (volume.restrict D) :=
    ((chartDensity_continuousOn sphereMetric.toContinuousRiemannianMetric p).mono
      (fun y hy => hy.2)).aemeasurable hD
  calc
    (volume : Measure E3).toSphere (s ∩ (extChartAt I2 p).source) =
        3 * volume (sphereCone p '' U) := by
      rw [Measure.toSphere_apply' _ (hs.inter (isOpen_extChartAt_source p).measurableSet)]
      simp only [E3,finrank_euclideanSpace, Fintype.card_fin,Nat.cast_ofNat]
      rw [sphereCone_image]
    _ = 3 * ∫⁻ z in U, ENNReal.ofReal |(sphereConeDeriv p z).det| := by rw [hJ]
    _ = 3 * (ENNReal.ofReal (1/3:ℝ) * ∫⁻ y in D,
        ENNReal.ofReal (chartDensity sphereMetric.toContinuousRiemannianMetric p y)) := by
      simp_rw [sphereCone_det]
      rw [lintegral_join_product D _ hf]
    _ = localVolume sphereMetric.toContinuousRiemannianMetric p s := by
      rw [localVolume_apply _ _ hs,← mul_assoc]
      have hnum : (3 : ℝ≥0∞) * ENNReal.ofReal (1/3 : ℝ) = 1 := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rw [hnum,one_mul]

theorem sphere_induced_volume :
    CKSSurfaceVolume.riemannianVolume sphereMetric.toContinuousRiemannianMetric =
      (volume : Measure CKSBoundarySurface.E3).toSphere := by
  apply volume_unique sphereMetric.toContinuousRiemannianMetric
    (riemannianVolume_isVolume _)
  intro p
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  exact sphere_toSphere_local p hs

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceImageMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold
namespace CKSSurfaceVolume
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma sigmaCompact_open [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  simpa using IsSigmaCompact.image (f := (Subtype.val : U → X)) continuous_subtype_val isSigmaCompact_univ

lemma sigmaCompact_inter_closed {s t : Set X} (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K,hK,hcov⟩ := hs
  refine ⟨fun n => K n ∩ t,fun n => (hK n).inter_right ht,?_⟩
  rw [← iUnion_inter,hcov]

lemma sigmaCompact_measurable [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K,hK,rfl⟩ := hs
  exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)

lemma sigmaCompact_disjointed_open [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) (n : ℕ) : IsSigmaCompact (disjointed U n) := by
  rw [disjointed_eq_inter_compl]
  exact sigmaCompact_inter_closed (sigmaCompact_open (hU n)) (isClosed_iInter (fun j => isClosed_iInter (fun _ => (hU j).isClosed_compl)))

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceMapDerivative
attribute [-simp] _root_.OAI.CKSSurfaceVolume.scaledMetric_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff
namespace CKSSurfaceVolume
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]

lemma hasFDerivWithinAt_mapChart (f : M → N) (hf : ContMDiff I I 1 f)
    (x : M) (y : N) {z : E} (hz : z ∈ (extChartAt I x).target)
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    HasFDerivWithinAt (mapChart f x y) (mapChartDeriv f x y z) (range I) z := by
  exact ((mdifferentiableAt_extChartAt (by simpa using hy)).hasMFDerivAt.comp_hasMFDerivWithinAt z
    (((hf.mdifferentiable (by norm_num)) _).hasMFDerivAt.comp_hasMFDerivWithinAt z
      (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt)).hasFDerivWithinAt

lemma mapChart_frame {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    (f : M → N) (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    (chartFrame y (mapChart f x y z)).comp (mapChartDeriv f x y z) =
      (mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z) := by
  unfold mapChartDeriv
  change (mfderivWithin I I (extChartAt I y).symm (range I)
    (extChartAt I y (f ((extChartAt I x).symm z)))).comp
      ((mfderiv I I (extChartAt I y) (f ((extChartAt I x).symm z))).comp _) = _
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy]
  rfl

lemma mapPullbackInner_eq (h : Metric (M := N)) (f : M → N) (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    mapPullbackInner h f x z = (pullbackInner h y (mapChart f x y z)).comp
      (mapChartDeriv f x y z).toLinearMap (mapChartDeriv f x y z).toLinearMap := by
  ext v w
  change h.inner (f ((extChartAt I x).symm z))
    ((mfderiv I I f ((extChartAt I x).symm z)) (chartFrame x z v))
    ((mfderiv I I f ((extChartAt I x).symm z)) (chartFrame x z w)) =
    h.inner ((extChartAt I y).symm (mapChart f x y z))
      (chartFrame y (mapChart f x y z) (mapChartDeriv f x y z v))
      (chartFrame y (mapChart f x y z) (mapChartDeriv f x y z w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (mapChart_frame f x y hy)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (mapChart_frame f x y hy)
  change chartFrame y (mapChart f x y z) (mapChartDeriv f x y z v) = _ at hv
  change chartFrame y (mapChart f x y z) (mapChartDeriv f x y z w) = _ at hw
  rw [hv,hw]
  have heq : (extChartAt I y).symm (mapChart f x y z) = f ((extChartAt I x).symm z) :=
    (extChartAt I y).left_inv hy
  rw [heq]
  rfl

lemma mapPullbackInner_posSemidef {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    (h : Metric (M := N)) (f : M → N) (x : M) (z : E) :
    LinearMap.IsPosSemidef (mapPullbackInner h f x z) := by
  constructor
  · constructor
    intro v w
    exact h.symm _ _ _
  · constructor
    intro v
    exact metric_nonneg h _ _

lemma mapChart_density_le (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤ g.inner x v v)
    (x : M) (y : N) {z : E}
    (hy : f ((extChartAt I x).symm z) ∈ (extChartAt I y).source) :
    |(mapChartDeriv f x y z).det| * chartDensity h y (mapChart f x y z) ≤ chartDensity g x z := by
  have hp := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp
    (mapPullbackInner_posSemidef h f x z)
  have hd : LinearMap.IsPosSemidef (pullbackInner g x z - mapPullbackInner h f x z) := by
    constructor
    · constructor
      intro v w
      exact congrArg₂ (fun a b : ℝ => a-b) (g.symm _ _ _) (h.symm _ _ _)
    · constructor
      intro v
      exact sub_nonneg.mpr (hshort _ _)
  have hdm := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp hd
  have heq : LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x z - mapPullbackInner h f x z) =
      chartMatrix g x z - (1 : ℝ) • LinearMap.BilinForm.toMatrix stdBasis (mapPullbackInner h f x z) := by
    ext i j
    simp [chartMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply]
  change (LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x z - mapPullbackInner h f x z)).PosSemidef at hdm
  change (LinearMap.BilinForm.toMatrix stdBasis (mapPullbackInner h f x z)).PosSemidef at hp
  rw [heq] at hdm
  have hb := sqrt_det_two_lower _ _ hp (by norm_num : (0:ℝ) ≤ 1) hdm
  simpa only [one_mul,mapPullbackInner_eq h f x y hy,sqrt_gram_det_comp,
    ← chartMatrix_eq_toMatrix, chartDensity] using hb

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_WeightedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CKSSurfaceVolume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma restrict_image_le_map_jacobian {s : Set E} (hs : MeasurableSet s)
    {f : E → E} (hm : Measurable f) {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    volume.restrict (f '' s) ≤
      Measure.map f ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)) := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.restrict_apply ht, Measure.map_apply hm ht, withDensity_apply _ (ht.preimage hm),
    Measure.restrict_restrict (ht.preimage hm)]
  rw [← image_preimage_inter]
  exact addHaar_image_le_lintegral_abs_det_fderiv volume ((ht.preimage hm).inter hs)
    (fun x hx => (hd x hx.2).mono inter_subset_right)

lemma lintegral_image_le_jacobian {s : Set E} (hs : MeasurableSet s)
    {f : E → E} (hm : Measurable f) {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (w : E → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ y in f '' s, w y ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * w (f x) := by
  calc
    _ ≤ ∫⁻ y, w y ∂Measure.map f
        ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)) :=
      lintegral_mono' (restrict_image_le_map_jacobian hs hm hd) le_rfl
    _ = ∫⁻ x, w (f x) ∂(volume.restrict s).withDensity
        (fun x => ENNReal.ofReal |(f' x).det|) := lintegral_map hw hm
    _ = _ := lintegral_withDensity_eq_lintegral_mul₀
      (aemeasurable_ofReal_abs_det_fderivWithin volume hs hd) (hw.comp hm).aemeasurable

lemma lintegral_image_le_jacobian_on {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (w : E → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ y in f '' s, w y ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * w (f x) := by
  classical
  let F := s.piecewise f (fun _ => 0)
  have hcont : ContinuousOn f s := fun x hx => (hd x hx).continuousWithinAt
  have hm : Measurable F := hcont.measurable_piecewise continuous_const.continuousOn hs
  have heq : EqOn F f s := piecewise_eqOn _ _ _
  have hdiff : ∀ x ∈ s, HasFDerivWithinAt F (f' x) s x := fun x hx =>
    (hd x hx).congr (fun z hz => heq hz) (heq hx)
  have h := lintegral_image_le_jacobian hs hm hdiff w hw
  have him : F '' s = f '' s := image_congr heq
  rw [him] at h
  refine h.trans_eq ?_
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [heq hx]

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceLocalImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

lemma mapChart_image {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (f : M → N) (x : M) (y : N) {s : Set M}
    (hx : s ⊆ (extChartAt I x).source) (hy : MapsTo f s (extChartAt I y).source) :
    mapChart f x y '' chartPreimage x s = chartPreimage y (f '' s) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hfy := hy hw.1
    have heq : (extChartAt I y).symm (mapChart f x y w) = f ((extChartAt I x).symm w) :=
      (extChartAt I y).left_inv hfy
    refine ⟨?_,(extChartAt I y).map_source hfy⟩
    change (extChartAt I y).symm (mapChart f x y w) ∈ f '' s
    rw [heq]
    exact mem_image_of_mem f hw.1
  · rintro ⟨⟨p,hps,hpf⟩,hz⟩
    refine ⟨extChartAt I x p,?_,?_⟩
    · exact ⟨by change (extChartAt I x).symm (extChartAt I x p) ∈ s;
                   rwa [(extChartAt I x).left_inv (hx hps)], (extChartAt I x).map_source (hx hps)⟩
    · change extChartAt I y (f ((extChartAt I x).symm (extChartAt I x p))) = z
      rw [(extChartAt I x).left_inv (hx hps),hpf,(extChartAt I y).right_inv hz]

lemma localVolume_image_le (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hf : ContMDiff I I 1 f)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤ g.inner x v v)
    (x : M) (y : N) {s : Set M} (hs : MeasurableSet s) (hfs : MeasurableSet (f '' s))
    (hx : s ⊆ (extChartAt I x).source) (hy : MapsTo f s (extChartAt I y).source) :
    localVolume h y (f '' s) ≤ localVolume g x s := by
  classical
  let w := (extChartAt I y).target.piecewise (fun z => ENNReal.ofReal (chartDensity h y z))
    (fun _ => 0)
  have hwm : Measurable w :=
    (ENNReal.continuous_ofReal.comp_continuousOn (chartDensity_continuousOn h y)).measurable_piecewise
      continuous_const.continuousOn (chart_target_measurable y)
  have hB : MeasurableSet (chartPreimage x s) := chartPreimage_measurable x hs
  have hd : ∀ z ∈ chartPreimage x s, HasFDerivWithinAt (mapChart f x y) (mapChartDeriv f x y z)
      (chartPreimage x s) z := by
    intro z hz
    exact (hasFDerivWithinAt_mapChart f hf x y hz.2 (hy hz.1)).mono
      (fun a ha => extChartAt_target_subset_range x ha.2)
  have hwz : ∀ z ∈ chartPreimage x s, w (mapChart f x y z) =
      ENNReal.ofReal (chartDensity h y (mapChart f x y z)) := by
    intro z hz
    exact piecewise_eq_of_mem _ _ _ ((extChartAt I y).map_source (hy hz.1))
  have hn : ∫⁻ z in chartPreimage y (f '' s), w z = localVolume h y (f '' s) := by
    rw [localVolume_apply h y hfs]
    apply setLIntegral_congr_fun (chartPreimage_measurable y hfs)
    intro z hz
    exact piecewise_eq_of_mem _ _ _ hz.2
  rw [localVolume_apply g x hs,← hn,← mapChart_image f x y hx hy]
  calc
    _ ≤ ∫⁻ z in chartPreimage x s, ENNReal.ofReal |(mapChartDeriv f x y z).det| *
        w (mapChart f x y z) := lintegral_image_le_jacobian_on hB hd w hwm
    _ ≤ ∫⁻ z in chartPreimage x s, ENNReal.ofReal (chartDensity g x z) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict hB] with z hz
      rw [hwz z hz,← ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mapChart_density_le g h f hshort x y (hy hz.1))

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSurfaceVolume
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [CompactSpace M]

theorem volume_le_of_surjective_nonexpanding
    (g : Metric (M := M)) (h : Metric (M := N)) (f : M → N)
    (hf : ContMDiff I I 1 f) (hsurj : Function.Surjective f)
    (hshort : ∀ x v, h.inner (f x) (mfderiv I I f x v) (mfderiv I I f x v) ≤
      g.inner x v v) : riemannianVolume h univ ≤ riemannianVolume g univ := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hm =>
    let := hm
    have : IsEmpty N := ⟨fun y => (hsurj y).elim (fun x _ => isEmptyElim x)⟩
    have hu : (univ : Set N) = ∅ := by ext x; exact isEmptyElim x
    rw [hu,measure_empty]
    exact zero_le
  | inr hm =>
    let := hm
    let U : M → Set M := fun x => (extChartAt I x).source ∩ f ⁻¹' (extChartAt I (f x)).source
    have hU : ∀ x, IsOpen (U x) := fun x =>
      (isOpen_extChartAt_source x).inter ((isOpen_extChartAt_source (f x)).preimage hf.continuous)
    have hUx : ∀ x, x ∈ U x := fun x => ⟨mem_extChartAt_source x,mem_extChartAt_source (f x)⟩
    obtain ⟨a,ha⟩ := isLindelof_univ.indexed_countable_subcover U hU
      (fun x _ => mem_iUnion.mpr ⟨x,hUx x⟩)
    let D := disjointed (U ∘ a)
    have hcover : ⋃ n, D n = univ := iUnion_disjointed.trans (eq_univ_of_univ_subset ha)
    have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => (hU (a n)).measurableSet)
    have hDf : ∀ n, MeasurableSet (f '' D n) := fun n => sigmaCompact_measurable
      ((sigmaCompact_disjointed_open (U ∘ a) (fun n => hU (a n)) n).image hf.continuous)
    have hDn : ∀ n, D n ⊆ U (a n) := fun n => disjointed_subset (U ∘ a) n
    have hle : ∀ n, riemannianVolume h (f '' D n) ≤ riemannianVolume g (D n) := by
      intro n
      have hx : D n ⊆ (extChartAt I (a n)).source := fun x hx => (hDn n hx).1
      have hy : MapsTo f (D n) (extChartAt I (f (a n))).source := fun x hx => (hDn n hx).2
      rw [volume_on_subset h (riemannianVolume_isVolume h) (f (a n)) (by rintro y ⟨x,hx,rfl⟩; exact hy hx),
        volume_on_subset g (riemannianVolume_isVolume g) (a n) hx]
      exact localVolume_image_le g h f hf hshort _ _ (hD n) (hDf n) hx hy
    calc
      riemannianVolume h univ = riemannianVolume h (⋃ n, f '' D n) := by
        rw [← image_iUnion,hcover,image_univ,hsurj.range_eq]
      _ ≤ ∑' n, riemannianVolume h (f '' D n) := measure_iUnion_le _
      _ ≤ ∑' n, riemannianVolume g (D n) := ENNReal.tsum_le_tsum hle
      _ = riemannianVolume g (⋃ n, D n) := (measure_iUnion (disjoint_disjointed _) hD).symm
      _ = riemannianVolume g univ := by rw [hcover]
end
end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface CKSFullCutArea CKSSurfaceVolume

lemma sphere_area : riemannianVolume sphereMetric.toContinuousRiemannianMetric univ =
    ENNReal.ofReal (4 * Real.pi) := by
  rw [sphere_induced_volume,Measure.toSphere_apply_univ,EuclideanSpace.volume_ball_fin_three]
  simp only [E3,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat,ENNReal.ofReal_one,one_pow,one_mul]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

lemma scaled_sphere_area {m : ℝ} (hm : 0 < m) :
    riemannianVolume (boundaryScaledMetric hm).toContinuousRiemannianMetric univ =
      ENNReal.ofReal (16 * Real.pi * m^2) := by
  rw [boundaryScaledMetric,riemannianVolume_scaled,Measure.smul_apply,smul_eq_mul,sphere_area,
    ← ENNReal.ofReal_mul (sq_nonneg (2*m))]
  congr 1
  ring

lemma full_cut_area_lower {m : ℝ} (hm : 0 < m) (D : CKSGeometricCuts.OuterDomain Exterior) :
    ENNReal.ofReal (16*Real.pi*m^2) ≤ area (smoothMetric hm) D := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  rw [← scaled_sphere_area hm]
  apply volume_le_of_surjective_nonexpanding
    (cutMetric (smoothMetric hm) D).toContinuousRiemannianMetric
    (boundaryScaledMetric hm).toContinuousRiemannianMetric (angular ∘ cutInclusion D)
    ((angular_smooth.comp (cutInclusion_smooth D)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (full_cut_radial_projection_surjective D)
  intro x v
  rw [mfderiv_comp x (angular_smooth.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    ((cutInclusion_smooth D).mdifferentiable (by simp) _)]
  exact angular_metric_bound hm (cutInclusion D x) (mfderiv I2 I3 (cutInclusion D) x v)

lemma boundary_metric_formula {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) (v : E2) :
    metricInner m p.val (liftPlane v) (liftPlane v) =
      (2*m)^2 * sphereMetric.inner (boundarySphere p) v v := by
  rw [metricInner_quad hm]
  have hh : radius m p.val = 2*m := by simp [radius,boundary_height p]
  rw [hh,liftPlane_zero,zero_pow (by decide : 2 ≠ 0),zero_div,zero_add]
  rw [sphereMetric_apply,real_inner_self_eq_norm_sq]
  congr 2
  have hd : ambientDerivative directionAmbient p.val (liftPlane v) =
      sphereDerivative (boundarySphere p) v := by
    change mfderiv I3 𝓘(ℝ,E3) directionAmbient p.val (liftPlane v) = _
    rw [mfderiv_directionAmbient]
    rfl
  exact congrArg norm hd

lemma boundary_area_upper {m : ℝ} (hm : 0 < m) :
    area (smoothMetric hm) (CKSGeometricCuts.identityOuterDomain boundary_compact) ≤
      ENNReal.ofReal (16*Real.pi*m^2) := by
  let D := CKSGeometricCuts.identityOuterDomain boundary_compact
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  rw [← scaled_sphere_area hm]
  apply volume_le_of_surjective_nonexpanding
    (boundaryScaledMetric hm).toContinuousRiemannianMetric
    (cutMetric (smoothMetric hm) D).toContinuousRiemannianMetric boundarySphere.symm
    (boundarySphere_symm_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) boundarySphere.symm.surjective
  intro x v
  change E2 at v
  change metricInner m (boundarySphere.symm x).val
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x)
      (mfderiv I2 I2 boundarySphere.symm x v))
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x)
      (mfderiv I2 I2 boundarySphere.symm x v)) ≤ _
  rw [mfderiv_boundarySphere_symm]
  change metricInner m (boundarySphere.symm x).val
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x) v)
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x) v) ≤ _
  rw [(CKSBoundarySurface.inclusion_hasMFDeriv _).mfderiv]
  change metricInner m (boundarySphere.symm x).val (liftPlane v) (liftPlane v) ≤
    (2*m)^2 * sphereMetric.inner x v v
  rw [boundary_metric_formula hm, boundarySphere.apply_symm_apply]

theorem full_minimum_enclosing_area {m : ℝ} (hm : 0 < m) :
    CKSFullCutArea.minEnclosingArea (smoothMetric hm) = ENNReal.ofReal (16 * Real.pi * m^2) := by
  apply le_antisymm
  · exact (iInf_le _ (CKSGeometricCuts.identityOuterDomain boundary_compact)).trans (boundary_area_upper hm)
  · exact le_iInf (full_cut_area_lower hm)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SourceReplacementDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle MeasureTheory CKSGeometricCuts CKSMetricGluing
open scoped ContDiff
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSGeometricCuts.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

lemma minimumEnclosingArea_eq_toReal (g : SmoothMetric I3 (M := N)) :
    minimumEnclosingArea g = (CKSFullCutArea.minEnclosingArea g).toReal := by
  exact (ENNReal.toReal_iInf (fun D => ne_of_lt (CKSFullCutArea.area_finite g D))).symm

end
end CKSSourceExterior

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma source_minimum_area_oai {m : ℝ} (hm : 0 < m) :
    CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) = 16*Real.pi*m^2 := by
  rw [CKSSourceExterior.minimumEnclosingArea_eq_toReal,full_minimum_enclosing_area hm,ENNReal.toReal_ofReal (by positivity)]

end CKSSchwarzschild

end

end OAI
end

theorem solution : type_of% @OAI.CKSSchwarzschild.source_minimum_area_oai := @OAI.CKSSchwarzschild.source_minimum_area_oai
