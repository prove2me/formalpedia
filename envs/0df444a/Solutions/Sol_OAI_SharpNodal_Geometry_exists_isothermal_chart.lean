-- Prove2me | solution 1 for OAI.SharpNodal.Geometry.exists_isothermal_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:13:58.669628+00:00
-- url     : https://prove2.me/submissions/9cd36fe9-ee48-4da8-a05d-6064e4a20747

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Geometry_conjugate_chart_conformal
import Theorems.Thm_OAI_SharpNodal_Profiles_Elliptic_normalized_metric_coordinates

section
-- module Solutions.OAIQ4_Nl.NodalLength_NormalizedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma smoothOn_pullback_metric {f : Plane → M} {s : Set Plane} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ f s) (v w : Plane) :
    ContDiffOn ℝ ∞ (fun y=>inner ℝ
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y w)) s := by
  have hc (a : Plane) : ContMDiff 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) := by
    intro y
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have ht:=hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have hv (a : Plane) : ContMDiffOn 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y=> (⟨f y,mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y a⟩ : TangentBundle 𝓘(ℝ,Plane) M)) s := by
    have hh:=ht.comp (hc a).contMDiffOn (show MapsTo (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) s (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy=>hy)
    apply hh.congr
    intro y hy
    simp only [Function.comp_apply,tangentMapWithin,
      mfderivWithin_of_mem_nhds (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane)) (f:=f) (hs.mem_nhds hy)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

lemma gram_two_positive {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : Plane →L[ℝ] F) (hi : Function.Injective D) :
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1)) ∧
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1))*
      inner ℝ (D (EuclideanSpace.single 1 1)) (D (EuclideanSpace.single 1 1))-
      (inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 1 1)))^2 := by
  let v:=D (EuclideanSpace.single 0 1)
  let w:=D (EuclideanSpace.single 1 1)
  let a:=inner ℝ v v
  let b:=inner ℝ v w
  let c:=inner ℝ w w
  have hv : v≠0 := by
    intro hz
    have hh:=hi (hz.trans D.map_zero.symm)
    have := congrArg (fun z:Plane=>z 0) hh
    norm_num at this
  have ha : 0<a:=real_inner_self_pos.mpr hv
  have hw : a • w-b • v≠0 := by
    intro hz
    have he : D (a • EuclideanSpace.single 1 1-b • EuclideanSpace.single 0 1)=D 0 := by
      simpa only [map_sub,map_smul,map_zero] using hz
    have hh:=congrArg (fun z:Plane=>z 1) (hi he)
    norm_num at hh
    exact ha.ne' hh
  have hp:=real_inner_self_pos.mpr hw
  have hab : inner ℝ w v=b:=real_inner_comm _ _
  have he : inner ℝ (a • w-b • v) (a • w-b • v)=a*(a*c-b^2) := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
      RCLike.conj_to_real,hab]
    dsimp [a,b,c]; ring
  rw [he] at hp
  exact ⟨ha,(mul_pos_iff.mp hp).resolve_right (fun h=>not_lt_of_ge ha.le h.1) |>.2⟩

omit [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma chartSmooth_chartAt (x : M) : ChartSmooth (chartAt Plane x) :=
  ⟨contMDiffOn_chart,contMDiffOn_chart_symm⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.mdiff {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) :
    e.MDifferentiable 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) :=
  ⟨he.1.mdifferentiableOn (by simp),he.2.mdifferentiableOn (by simp)⟩

lemma ChartSmooth.metric_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y=>pullMetric (e.symm : Plane → M) y i j) e.target :=
  smoothOn_pullback_metric e.open_target he.2 _ _

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.metric_positive {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    {y : Plane} (hy : y∈e.target) : 0<pullMetric (e.symm : Plane → M) y 0 0 ∧
      0<(pullMetric (e.symm : Plane → M) y).det := by
  have hh:=gram_two_positive (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) e.symm y)
    (he.mdiff.symm.mfderiv_injective hy)
  refine ⟨hh.1,?_⟩
  have hp : 0<pullMetric (e.symm : Plane → M) y 0 0*pullMetric (e.symm : Plane → M) y 1 1-
      (pullMetric (e.symm : Plane → M) y 0 1)^2:=hh.2
  have hc : pullMetric (e.symm : Plane → M) y 1 0=pullMetric (e.symm : Plane → M) y 0 1 :=
    real_inner_comm _ _
  rw [Matrix.det_fin_two,hc]
  nlinarith [hp]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma exists_normalized_chart (x : M) : ∃e : OpenPartialHomeomorph M Plane,
    x∈e.source ∧ e x=0 ∧ ChartSmooth e ∧ pullMetric (e.symm : Plane → M) 0=1 := by
  let c:=chartAt Plane x
  have hx : x∈c.source:=mem_chart_source Plane x
  let y₀:=c x
  have hy : y₀∈c.target:=c.map_source hx
  let D : Plane ≃L[ℝ] TangentSpace 𝓘(ℝ,Plane) (c.symm y₀):=
    (mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).symm.mfderiv hy
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀)):=D.toLinearEquiv.finiteDimensional
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀))=2 := by
    rw [← D.toLinearEquiv.finrank_eq]
    simp [Plane]
  let B : OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀)):=
    (stdOrthonormalBasis ℝ _).reindex (finCongr hdim)
  let L : Plane ≃L[ℝ] Plane:=B.repr.symm.toContinuousLinearEquiv.trans D.symm
  let a : Plane ≃ₜ Plane:=L.toHomeomorph.trans (Homeomorph.addLeft y₀)
  have ha (y : Plane) : a y=y₀+L y:=rfl
  have hai (y : Plane) : a.symm y=L.symm (y-y₀):=by
    change L.symm (-y₀+y)=L.symm (y-y₀)
    congr 1; abel
  have haC : ContDiff ℝ ∞ (a : Plane → Plane):=contDiff_const.add L.contDiff
  have haiC : ContDiff ℝ ∞ (a.symm : Plane → Plane):=by
    have hh : ContDiff ℝ ∞ (fun y:Plane=>L.symm (y-y₀)):=
      L.symm.contDiff.comp (contDiff_id.sub contDiff_const)
    rw [show (a.symm : Plane → Plane)=(fun y=>L.symm (y-y₀)) from funext hai]
    exact hh
  have haiM : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (a.symm : Plane → Plane):=haiC.contMDiff
  have haM : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (a : Plane → Plane):=haC.contMDiff
  let e:=c.trans a.symm.toOpenPartialHomeomorph
  have he (z : M) : e z=a.symm (c z):=rfl
  have hei (y : Plane) : e.symm y=c.symm (a y):=rfl
  have heS : e.source=c.source:=by simp [e]
  have heT : e.target=a ⁻¹' c.target:=by simp [e]
  refine ⟨e,by rwa [heS],?_,?_,?_⟩
  · simp only [he,hai,y₀,sub_self,map_zero]
  · constructor
    · rw [heS]
      exact haiM.comp_contMDiffOn (chartSmooth_chartAt x).1
    · have hh := (chartSmooth_chartAt x).2.comp haM.contMDiffOn
        (show MapsTo (a : Plane → Plane) e.target c.target from fun _ hy=>by rwa [heT] at hy)
      exact hh
  · have hdc : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0) := by
      simpa only [ha,map_zero,add_zero] using (mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).mdifferentiableAt_symm hy
    have hda : HasFDerivAt (a : Plane → Plane) (L : Plane →L[ℝ] Plane) 0 :=
      L.hasFDerivAt.const_add y₀
    have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (e.symm : Plane → M) 0=
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)).comp (L : Plane →L[ℝ] Plane) := by
      change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ((c.symm : Plane → M) ∘ (a : Plane → Plane)) 0=_
      have hh:=mfderiv_comp 0 hdc ((haM.mdifferentiable (by simp)).mdifferentiableAt)
      rw [mfderiv_eq_fderiv,hda.fderiv] at hh
      exact hh
    ext i j
    unfold pullMetric
    rw [hd]
    change inner ℝ ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)) (L (EuclideanSpace.single i 1)))
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)) (L (EuclideanSpace.single j 1)))=_
    erw [ha,map_zero,add_zero]
    change inner ℝ (D (L (EuclideanSpace.single i 1))) (D (L (EuclideanSpace.single j 1)))= _
    have hh (v : Plane) : D (L v)=B.repr.symm v:=by simp [L]
    rw [hh,hh]
    calc
      _ = inner ℝ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
        B.repr.symm.inner_map_map _ _
      _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by simp [EuclideanSpace.inner_single_left,Matrix.one_apply]

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_symm (F : Plane → M) (y : Plane) (i j : Fin 2) :
    pullMetric F y i j=pullMetric F y j i := real_inner_comm _ _

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff
open Filter Set Metric
namespace SharpNodal.Geometry

lemma smooth_mul_of_support {f a : Plane → ℝ} {s : Set Plane} (hs : IsOpen s)
    (hf : ContDiff ℝ ∞ f) (ha : ContDiffOn ℝ ∞ a s) (hsupp : tsupport f⊆s) :
    ContDiff ℝ ∞ (fun y=>f y*a y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈tsupport f
  · exact hf.contDiffAt.mul (ha.contDiffAt (hs.mem_nhds (hsupp hx)))
  · apply (show ContDiffAt ℝ ∞ (fun _ : Plane => (0:ℝ)) x from contDiffAt_const).congr_of_eventuallyEq
    have hh : ∀ᶠy in 𝓝 x,y∉tsupport f:=(isClosed_tsupport f).isOpen_compl.mem_nhds hx
    filter_upwards [hh] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

lemma exists_smooth_local_extension {ι : Type*} (a : ι → Plane → ℝ) {s : Set Plane}
    (hs : IsOpen s) (h0 : (0:Plane)∈s) (ha : ∀i,ContDiffOn ℝ ∞ (a i) s) :
    ∃r : ℝ,∃A : ι → Plane → ℝ,0 < r ∧ r<1 ∧ closedBall (0:Plane) r⊆s ∧
      (∀i,ContDiff ℝ ∞ (A i)) ∧ (∀i,EqOn (A i) (a i) (closedBall (0:Plane) r)) := by
  obtain ⟨d,hd,hdsub⟩:=Metric.mem_nhds_iff.mp (hs.mem_nhds h0)
  let R:=min (d/2) (1/2)
  have hR : 0<R:=lt_min (half_pos hd) (by norm_num)
  let χ : ContDiffBump (0:Plane):=⟨R/2,R,half_pos hR,half_lt_self hR⟩
  let A:=fun i y=>χ y*a i y
  refine ⟨R/2,A,half_pos hR,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (by dsimp [R]; linarith [min_le_right (d/2) (1/2:ℝ)]) (by norm_num : (1/2:ℝ)<1)
  · intro y hy
    exact hdsub (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt (by change R/2 < d; dsimp [R]; linarith [min_le_left (d/2) (1/2:ℝ)])))
  · intro i
    apply smooth_mul_of_support hs χ.contDiff (ha i)
    rw [χ.tsupport_eq]
    intro y hy
    exact hdsub (mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy) (by change R < d; dsimp [R]; linarith [min_le_left (d/2) (1/2:ℝ)])))
  · intro i y hy
    dsimp [A]
    rw [χ.one_of_mem_closedBall hy,one_mul]

end SharpNodal.Geometry

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Conductivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.trans {e : OpenPartialHomeomorph M Plane} {c : OpenPartialHomeomorph Plane Plane}
    (he : ChartSmooth e) (hc : ChartSmooth c) : ChartSmooth (e.trans c) := by
  constructor
  · exact hc.1.comp (he.1.mono inter_subset_left) (fun _ h=>h.2)
  · exact he.2.comp (hc.2.mono inter_subset_left) (fun _ h=>h.2)

end SharpNodal.Geometry
noncomputable section

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma ChartSmooth.conductivity_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (chartConductivity e i j) e.target := by
  have hden : ContDiffOn ℝ ∞ (fun y=>Real.sqrt (pullMetric (e.symm : Plane → M) y).det) e.target := by
    have hdet : (fun y=>(pullMetric (e.symm : Plane → M) y).det)=
        fun y=>pullMetric (e.symm : Plane → M) y 0 0*pullMetric (e.symm : Plane → M) y 1 1-
          (pullMetric (e.symm : Plane → M) y 0 1)^2 := by
      funext y; rw [Matrix.det_fin_two,pullMetric_symm _ _ 1 0]; ring
    simp_rw [congrFun hdet]
    apply (((he.metric_smooth 0 0).mul (he.metric_smooth 1 1)).sub ((he.metric_smooth 0 1).pow 2)).sqrt
    intro y hy
    have hp:=(he.metric_positive hy).2.ne'
    rwa [congrFun hdet y] at hp
  have hn (y) (hy:y∈e.target) : Real.sqrt (pullMetric (e.symm : Plane → M) y).det≠0:=
    (Real.sqrt_pos.mpr (he.metric_positive hy).2).ne'
  unfold chartConductivity
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, ↓reduceIte, Fin.zero_eta,Fin.mk_one]
  · exact (he.metric_smooth 1 1).div hden hn
  · exact (he.metric_smooth 0 1).neg.div hden hn
  · exact (he.metric_smooth 0 1).neg.div hden hn
  · exact (he.metric_smooth 0 0).div hden hn

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma conductivity_normalized {e : OpenPartialHomeomorph M Plane}
    (he : pullMetric (e.symm : Plane → M) 0=1) (i j : Fin 2) :
    chartConductivity e i j 0=if i=j then 1 else 0 := by
  unfold chartConductivity
  rw [he]
  fin_cases i <;> fin_cases j <;> norm_num

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_smul {F : Plane → M} {x : Plane} (r : ℝ)
    (hF : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (r • x)) :
    pullMetric (fun y=>F (r • y)) x=r^2 • pullMetric F (r • x) := by
  have hr : HasFDerivAt (fun y:Plane=>r • y) (r • ContinuousLinearMap.id ℝ Plane) x:=
    (hasFDerivAt_id x).const_smul r
  have hd:=mfderiv_comp x hF hr.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv,hr.fderiv] at hd
  have he (i : Fin 2) : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun y=>F (r • y)) x (EuclideanSpace.single i 1)=
      r • mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (r • x) (EuclideanSpace.single i 1) := by
    erw [hd]
    change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (r • x) (r • EuclideanSpace.single i 1)=_
    exact map_smul _ _ _
  ext i j
  unfold pullMetric
  erw [he i,he j]
  change inner ℝ (r • _) (r • _) = r^2*inner ℝ _ _
  simp only [inner_smul_left,inner_smul_right,RCLike.conj_to_real]
  ring

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.scale {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) (r : ℝ) (hr : r≠0) :
    ChartSmooth (scaleChart e r hr) := by
  apply he.trans
  constructor
  · exact (contDiff_id.const_smul r⁻¹ : ContDiff ℝ ∞ (fun y:Plane=>r⁻¹ • y)).contMDiff.contMDiffOn
  · exact (contDiff_id.const_smul r : ContDiff ℝ ∞ (fun y:Plane=>r • y)).contMDiff.contMDiffOn

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma scaleChart_metric {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) {r : ℝ} (hr : r≠0)
    {y : Plane} (hy : y∈(scaleChart e r hr).target) :
    pullMetric ((scaleChart e r hr).symm : Plane → M) y=r^2 • pullMetric (e.symm : Plane → M) (r • y) := by
  apply pullMetric_smul
  exact he.mdiff.mdifferentiableAt_symm hy.2

lemma sqrt_det_smul_sq (r : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt (r^2 • G).det=r^2*Real.sqrt G.det := by
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg r)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma scaleChart_conductivity {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) {r : ℝ} (hr : r≠0)
    {y : Plane} (hy : y∈(scaleChart e r hr).target) (i j : Fin 2) :
    chartConductivity (scaleChart e r hr) i j y=chartConductivity e i j (r • y) := by
  unfold chartConductivity
  rw [scaleChart_metric he hr hy,sqrt_det_smul_sq]
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,←mul_neg,mul_div_mul_left _ _ (pow_ne_zero 2 hr)]

end SharpNodal.Geometry

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Isothermal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

theorem exists_isothermal_chart_oai (x : M) : ∃e : OpenPartialHomeomorph M Plane,
    x∈e.source ∧ IsConformal e := by
  obtain ⟨E,hEx,hE0,hE,hEG⟩:=exists_normalized_chart x
  have hEt : (0:Plane)∈E.target:=by rw [← hE0]; exact E.map_source hEx
  obtain ⟨r,A,hr,hr1,hrsub,hA,hAE⟩:=exists_smooth_local_extension
    (fun ij:Fin 2×Fin 2=>chartConductivity E ij.1 ij.2) E.open_target hEt
    (fun ij=>hE.conductivity_smooth ij.1 ij.2)
  let B:=fun i j y=>A (i,j) (r • y)
  have hB (i j : Fin 2) : Smooth (B i j):=(hA (i,j)).comp (contDiff_id.const_smul r)
  have hB0 (i j : Fin 2) : B i j 0=if i=j then 1 else 0 := by
    change A (i,j) (r • (0:Plane))=_
    rw [smul_zero,hAE (i,j) (mem_closedBall_self hr.le),conductivity_normalized hEG]
  obtain ⟨t,u,v,e,ht,ht1,hu,hv,he,he0,hes,hef,hei,hconj,_hPDE,hdet⟩:=
    normalized_metric_coordinates B hB hB0
  let d:=r*t
  have hd : 0<d:=mul_pos hr ht
  let E':=scaleChart E d hd.ne'
  have hE' : ChartSmooth E':=hE.scale d hd.ne'
  have he' : ChartSmooth e:=⟨hef.contMDiffOn,hei.contMDiffOn⟩
  have hEs (z : Plane) (hz:z∈e.source) : z∈E'.target := by
    have hz1 : ‖z‖<1:=lt_of_lt_of_le (mem_ball_zero_iff.mp (hes hz)) (by norm_num)
    have htz : t*‖z‖<1:=lt_trans (mul_lt_mul_of_pos_left hz1 ht) (by simpa using ht1)
    have hn : ‖d • z‖ ≤ r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd]
      dsimp [d]
      nlinarith
    exact ⟨mem_univ _,hrsub (mem_closedBall_zero_iff.mpr hn)⟩
  have hBc (i j : Fin 2) (z : Plane) (hz:z∈e.source) :
      B i j (t • z)=chartConductivity E' i j z := by
    rw [scaleChart_conductivity hE hd.ne' (hEs z hz)]
    change A (i,j) (r • t • z)=chartConductivity E i j (d • z)
    rw [smul_smul]
    apply hAE (i,j)
    have hz1 : ‖z‖<1:=lt_of_lt_of_le (mem_ball_zero_iff.mp (hes hz)) (by norm_num)
    have htz : t*‖z‖<1:=lt_trans (mul_lt_mul_of_pos_left hz1 ht) (by simpa using ht1)
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd]
    dsimp [d]; nlinarith
  have hvc (z : Plane) (hz:z∈e.source) :
      coordPartial v 0 z=(pullMetric (E'.symm : Plane → M) z 0 1*coordPartial u 0 z-
        pullMetric (E'.symm : Plane → M) z 0 0*coordPartial u 1 z)/
          Real.sqrt (pullMetric (E'.symm : Plane → M) z).det ∧
      coordPartial v 1 z=(pullMetric (E'.symm : Plane → M) z 1 1*coordPartial u 0 z-
        pullMetric (E'.symm : Plane → M) z 0 1*coordPartial u 1 z)/
          Real.sqrt (pullMetric (E'.symm : Plane → M) z).det := by
    have hh:=hconj z (hes hz)
    simp_rw [hBc _ _ z hz,Fin.sum_univ_two,chartConductivity] at hh
    norm_num at hh
    constructor
    · rw [hh.1]; ring
    · rw [hh.2]; ring
  have hux : ContDiffOn ℝ ∞ u e.source:=hu.contDiffOn
  have hvx : ContDiffOn ℝ ∞ v e.source:=hv.mono (hes.trans (ball_subset_ball (by norm_num)))
  refine ⟨E'.trans e,?_,hE'.trans he',?_⟩
  · constructor
    · exact ⟨hEx,mem_univ _⟩
    · change d⁻¹ • E x∈e.source
      rw [hE0,smul_zero]
      exact he0
  · intro y hy
    exact conjugate_chart_conformal hE' he hux hvx hei hvc (fun z hz=>hdet z (hes hz)) hy

end SharpNodal.Geometry

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Geometry.exists_isothermal_chart_oai.{u_1} := @OAI.SharpNodal.Geometry.exists_isothermal_chart_oai.{u_1}
