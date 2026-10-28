-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:21:05.465987+00:00
-- url     : https://prove2.me/submissions/28710503-3356-43fd-89f3-69379c725cf6

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_H10_subcritical

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace


open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict Ω)


lemma weightedValue_ae (u : H10 hΩ) :
    weightedValue hΩ hC hν u =ᵐ[ν] value hΩ u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (value hΩ u)



end StrictHotSpots.H10


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

lemma dense_smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (smoothTestToH10 hΩ) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : H1 Ω) ∈ closure (Set.range (smoothTestToH1 hΩ)) := u.property
  obtain ⟨v,⟨f,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  exact ⟨smoothTestToH10 hΩ f, ⟨f,rfl⟩, hv⟩

end StrictHotSpots
end H10InclusionCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory _root_.Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

lemma plane_integral_target (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (g : CoordinatePlane → ℝ) :
    (∫ y in e.target, g y) = ∫ x in e.source, ‖d x‖^2 * g (e x) := by
  have hh := integral_target_eq_integral_abs_det_fderiv_smul volume hd g
  simpa only [planeMul_det,abs_sq, smul_eq_mul] using hh

lemma plane_dirichlet_energy (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {w : CoordinatePlane → ℝ} (hw : DifferentiableOn ℝ w e.target) :
    (∫ y in e.target, ‖gradient w y‖^2) =
      ∫ x in e.source, ‖gradient (w ∘ e) x‖^2 := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  rw [plane_norm_gradient_comp (hd x hx)
    ((hw (e x) (e.map_source hx)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))),mul_pow]


end StrictHotSpots.Conformal
end
end ConformalCoordinates

section CompactChartTransport




noncomputable section
open Set Filter
open scoped Topology ContDiff Classical
namespace CompactChart
variable {E : Type*} [NormedAddCommGroup E]

variable (e : OpenPartialHomeomorph E E)

lemma transport_source (f : E → ℝ) {x : E} (hx : x ∈ e.source) :
    transport e f (e x) = f x := by
  rw [transport_apply e (e.map_source hx),e.left_inv hx]

lemma transport_comp_eventuallyEq {f : E → ℝ} {x : E} (hx : x ∈ e.source) :
    (transport e f) ∘ e =ᶠ[𝓝 x] f := by
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact transport_source e f hz

end CompactChart
end
end CompactChartTransport

section ConformalH10Tests


noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

lemma test_grad_sq {Ω : Set Plane} (ho : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.grad ho (smoothTestToH10 ho f)‖^2 = ∫ x in Ω, ‖gradient (f : Plane → ℝ) x‖^2 := by
  rw [L2VectorLimits.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(test_gradient_memLp (Ω:=Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
  exact congrArg (fun t : Plane => ‖t‖^2) hx

lemma transportTest_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) (f : smoothTestSpace e.source) :
    ‖H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))‖^2 =
      ‖H10.grad e.open_source (smoothTestToH10 e.open_source f)‖^2 := by
  rw [test_grad_sq,test_grad_sq,plane_dirichlet_energy e d hd
    ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  congr 2
  change gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x
  unfold gradient
  rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]

private lemma scalar_norm_bound {s t a b C : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hsplit : t^2 = a^2+b^2) (hbsq : b^2 ≤ s^2) (hP : a ≤ C*b) :
    t ≤ (C+1)*s := by
  have hbs : b ≤ s := (sq_le_sq₀ hb hs).mp hbsq
  have ht' : t ≤ a+b := (sq_le_sq₀ ht (add_nonneg ha hb)).mp (by nlinarith)
  calc
    t ≤ a+b := ht'
    _ ≤ C*b+b := by linarith
    _ = (C+1)*b := by ring
    _ ≤ (C+1)*s := mul_le_mul_of_nonneg_left hbs (by linarith)

lemma transportTest_bound (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) :
    ∃ C : ℝ, ∀ f : smoothTestSpace e.source,
      ‖smoothTestToH10 e.open_target (transportTest e he f)‖ ≤
        C * ‖smoothTestToH10 e.open_source f‖ := by
  obtain ⟨C,hC,hP⟩ := H10.poincare e.open_target hb
  refine ⟨C+1,fun f => ?_⟩
  let v : H10 e.open_source := smoothTestToH10 e.open_source f
  let w : H10 e.open_target := smoothTestToH10 e.open_target (transportTest e he f)
  have hs := H10.norm_sq e.open_source v
  have ht := H10.norm_sq e.open_target w
  have heq : ‖H10.grad e.open_target w‖^2 = ‖H10.grad e.open_source v‖^2 :=
    transportTest_grad_sq e he d hd f
  have hp : ‖H10.value e.open_target w‖ ≤ C*‖H10.grad e.open_target w‖ := hP w
  have hle : ‖H10.grad e.open_source v‖^2 ≤ ‖v‖^2 := by
    calc
      ‖H10.grad e.open_source v‖^2 ≤
          ‖H10.value e.open_source v‖^2+‖H10.grad e.open_source v‖^2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ = ‖v‖^2 := hs.symm
  exact scalar_norm_bound (norm_nonneg v) (norm_nonneg w)
    (norm_nonneg (H10.value e.open_target w)) (norm_nonneg (H10.grad e.open_target w))
    hC.le ht (heq.le.trans hle) hp

end StrictHotSpots.Conformal
end
end ConformalH10Tests

section ConformalH10





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

lemma transportH10_test (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (f : smoothTestSpace e.source) :
    transportH10 e he (smoothTestToH10 e.open_source f) =
      smoothTestToH10 e.open_target (transportTest e he f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 e.open_source)
    (transportTest_bound e he d hd hb) f

lemma transportH10_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    ‖H10.grad e.open_target (transportH10 e he v)‖^2 =
      ‖H10.grad e.open_source v‖^2 := by
  have H : (fun v : H10 e.open_source => ‖H10.grad e.open_target (transportH10 e he v)‖^2) =
      (fun v => ‖H10.grad e.open_source v‖^2) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous).norm.pow 2)
      ((H10.grad e.open_source).continuous.norm.pow 2)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun w : H10 e.open_target => ‖H10.grad e.open_target w‖^2)
      (transportH10_test e he d hd hb f)).trans (transportTest_grad_sq e he d hd f)
  exact congrFun H v



lemma transported_dirichlet (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) {L : ℝ}
    (hD : ∀ v : H10 e.open_target, L*‖H10.value e.open_target v‖^2 ≤
      ‖H10.grad e.open_target v‖^2) (v : H10 e.open_source) :
    L*‖H10.value e.open_target (transportH10 e he v)‖^2 ≤
      ‖H10.grad e.open_source v‖^2 := by
  exact (hD (transportH10 e he v)).trans_eq (transportH10_grad_sq e he d hd hb v)



lemma transported_subcritical (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (hne : e.target.Nonempty) :
    ∃ L : ℝ, 0 < L ∧ firstPositiveNeumannValue e.target < L ∧
      ∀ v : H10 e.open_source,
        L*‖H10.value e.open_target (transportH10 e he v)‖^2 ≤
          ‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (@H10.subcritical e.target e.open_target hne hb)
  intro L h
  exact Exists.intro L ⟨h.1,h.2.1,transported_dirichlet e he d hd hb h.2.2⟩

end StrictHotSpots.Conformal
end
end ConformalH10

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

lemma chartPull_ae (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (f : Lp ℝ 2 (volume.restrict e.target)) :
    chartPull e d hd f =ᵐ[chartMeasure e d] f ∘ e := by
  exact (Lp.coeFn_compMeasurePreserving f (measurableChart_preserving e d hd)).trans
    ((measurableChart_ae e d).fun_comp f)

lemma chartPull_test_ae
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {f : CoordinatePlane → ℝ} (hf : MemLp f 2 (volume.restrict e.target)) :
    chartPull e d hd (hf.toLp f) =ᵐ[chartMeasure e d] f ∘ e := by
  apply (chartPull_ae e d hd _).trans
  have hh : (hf.toLp f : CoordinatePlane → ℝ) =ᵐ[(chartMeasure e d).map e] f := by
    rw [map_chartMeasure e d hd]
    exact hf.coeFn_toLp
  exact ae_of_ae_map (chart_aemeasurable e d) hh

lemma ae_chart_source : ∀ᵐ x ∂chartMeasure e d, x ∈ e.source :=
  (chartMeasure_ac e d).ae_le (ae_restrict_mem e.open_source.measurableSet)

end StrictHotSpots.Conformal
end
end ConformalMeasure

section LpDensityClosure





noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LpDensityClosure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

lemma ae_eq_of_tendsto (hν : ν ≪ μ)
    {f : ℕ → Lp E 2 μ} {g : ℕ → Lp E 2 ν} {u : Lp E 2 μ} {v : Lp E 2 ν}
    (he : ∀ n, (f n : α → E) =ᵐ[ν] (g n : α → E))
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) :
    (u : α → E) =ᵐ[ν] (v : α → E) := by
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨ψ,hψ,hψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hν.ae_le hφae,hψae,ae_all_iff.mpr he] with x hx hx' heq
  apply tendsto_nhds_unique (hx.comp hψ.tendsto_atTop)
  exact hx'.congr' (Filter.Eventually.of_forall (fun n => (heq (φ (ψ n))).symm))

lemma isClosed_graph (hν : ν ≪ μ) :
    IsClosed {fg : Lp E 2 μ × Lp E 2 ν | (fg.1 : α → E) =ᵐ[ν] (fg.2 : α → E)} := by
  apply IsSeqClosed.isClosed
  intro fg uv hfg ht
  exact ae_eq_of_tendsto hν hfg (continuous_fst.tendsto uv |>.comp ht)
    (continuous_snd.tendsto uv |>.comp ht)

lemma ae_eq_of_dense {X Y : Type*} [TopologicalSpace X]
    {j : Y → X} (hj : DenseRange j) (hν : ν ≪ μ)
    {f : X → Lp E 2 μ} {g : X → Lp E 2 ν}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y, (f (j y) : α → E) =ᵐ[ν] (g (j y) : α → E)) (x : X) :
    (f x : α → E) =ᵐ[ν] (g x : α → E) := by
  have hc : IsClosed {x | (f x : α → E) =ᵐ[ν] (g x : α → E)} :=
    (isClosed_graph hν).preimage (hf.prodMk hg)
  exact closure_minimal (by rintro _ ⟨y,rfl⟩; exact hfg y) hc (hj x)

end LpDensityClosure
end
end LpDensityClosure

section ConformalWeightedValue





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal
variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)
variable (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)


lemma weightedValue_test (hb : Bornology.IsBounded e.target)
    (f : smoothTestSpace e.source) :
    (weightedValue e he d hd (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f := by
  have ht := transportH10_test e he d hd hb f
  have hp : weightedValue e he d hd (smoothTestToH10 e.open_source f) =
      chartPull e d hd (H10.value e.open_target
        (smoothTestToH10 e.open_target (transportTest e he f))) :=
    congrArg (fun w : H10 e.open_target => chartPull e d hd (H10.value e.open_target w)) ht
  rw [hp]
  have ha := chartPull_test_ae e d hd
    (test_memLp (Ω:=e.target) (transportTest e he f).property.1
      (transportTest e he f).property.2.1)
  apply ha.trans
  filter_upwards [ae_chart_source e d] with x hx
  exact CompactChart.transport_source e f hx



lemma weightedValue_ae (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    (H10.value e.open_source v : Plane → ℝ) =ᵐ[chartMeasure e d]
      (weightedValue e he d hd v : Plane → ℝ) := by
  apply LpDensityClosure.ae_eq_of_dense (dense_smoothTestToH10 e.open_source)
    (chartMeasure_ac e d) (H10.value e.open_source).continuous
    (weightedValue e he d hd).continuous _ v
  intro f
  have hs : (H10.value e.open_source (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f :=
    (chartMeasure_ac e d).ae_le
      (test_memLp (Ω:=e.source) f.property.1 f.property.2.1).coeFn_toLp
  exact hs.trans (weightedValue_test e he d hd hb f).symm

lemma weightedValue_norm (v : H10 e.open_source) :
    ‖weightedValue e he d hd v‖ =
      ‖H10.value e.open_target (transportH10 e he v)‖ :=
  (chartPull e d hd).norm_map _

include hd in
lemma physical_value_sq (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    ‖H10.value e.open_target (transportH10 e he v)‖^2 =
      ∫ x, (H10.value e.open_source v x)^2 ∂chartMeasure e d := by
  calc
    _ = ‖weightedValue e he d hd v‖^2 :=
      congrArg (fun t : ℝ => t^2) (weightedValue_norm e he d hd v).symm
    _ = ∫ x, (weightedValue e he d hd v x)^2 ∂chartMeasure e d :=
      L2Limits.norm_sq_eq_integral_sq _
    _ = _ := integral_congr_ae ((weightedValue_ae e he d hd hb v).symm.fun_comp
      (fun t : ℝ => t^2))

include he hd in


theorem weighted_subcritical (hb : Bornology.IsBounded e.target)
    (hne : e.target.Nonempty) :
    ∃ L : ℝ, 0 < L ∧ firstPositiveNeumannValue e.target < L ∧
      ∀ v : H10 e.open_source,
        L*(∫ x, (H10.value e.open_source v x)^2 ∂chartMeasure e d) ≤
          ‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (transported_subcritical e he d hd hb hne)
  intro L h
  refine Exists.intro L ⟨h.1,h.2.1,fun v => ?_⟩
  exact (congrArg (fun t : ℝ => L*t) (physical_value_sq e he d hd hb v)).symm.le.trans (h.2.2 v)

end StrictHotSpots.Conformal
end
end ConformalWeightedValue


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalPotential





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane) (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)

lemma potentialMeasure_integral {μ : ℝ} (hμ : 0 ≤ μ) (f : Plane → ℝ) :
    (∫ x, f x ∂potentialMeasure e d μ) = μ * ∫ x, f x ∂chartMeasure e d := by
  rw [potentialMeasure,integral_smul_measure,ENNReal.toReal_ofReal hμ,smul_eq_mul]

lemma scale_gap {μ L A B : ℝ} (hμ : 0 < μ) (hL : 0 < L)
    (h : L*A ≤ B) : μ*A ≤ (μ/L)*B := by
  have he : μ*A = (μ/L)*(L*A) := by
    rw [← mul_assoc,div_mul_cancel₀ _ hL.ne']
  exact he ▸ mul_le_mul_of_nonneg_left h (div_pos hμ hL).le

include hd in

theorem potentialMeasure_subcritical (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hb : Bornology.IsBounded e.target) (hne : e.target.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue e.target) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ v : H10 e.open_source,
        (∫ x, (H10.value e.open_source v x)^2
          ∂potentialMeasure e d (firstPositiveNeumannValue e.target)) ≤
        δ*‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (weighted_subcritical e he d hd hb hne)
  intro L h
  refine ⟨firstPositiveNeumannValue e.target/L,div_pos hμ h.1,
    (div_lt_one h.1).mpr h.2.1,fun v => ?_⟩
  rw [potentialMeasure_integral e d hμ.le]
  exact scale_gap hμ h.1 (h.2.2 v)



end StrictHotSpots.Conformal
end
end ConformalPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Pullback
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualPotential

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.Conformal
open DiskH10

lemma subcritical_reindex {S T : Set Plane} (ho : IsOpen S) (ho' : IsOpen T)
    (hST : S = T) {ν : Measure Plane} {δ : ℝ}
    (h : ∀ v : H10 ho, (∫ x, (H10.value ho v x)^2 ∂ν) ≤ δ*‖H10.grad ho v‖^2) :
    ∀ v : H10 ho', (∫ x, (H10.value ho' v x)^2 ∂ν) ≤ δ*‖H10.grad ho' v‖^2 := by
  cases hST
  exact h

namespace ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



theorem subcritical_oai (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue Ω) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ v : H10 PlaneGreen.diskOpen,
      ‖H10.weightedValue PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v‖^2 ≤
        δ*‖H10.grad PlaneGreen.diskOpen v‖^2 := by
  have hh := potentialMeasure_subcritical c.e c.d c.deriv c.inverse_smooth
    (c.target_eq.symm ▸ hb) (c.target_eq.symm ▸ hne) (c.target_eq.symm ▸ hμ)
  obtain ⟨δ,hδ,hδ1,hsub⟩ := hh
  have hs := subcritical_reindex c.e.open_source PlaneGreen.diskOpen c.source_eq hsub
  have hs' : ∀ v : H10 PlaneGreen.diskOpen,
      (∫ x, (H10.value PlaneGreen.diskOpen v x)^2 ∂c.potential) ≤ δ*‖H10.grad PlaneGreen.diskOpen v‖^2 := by
    simpa only [potential,c.target_eq] using hs
  refine ⟨δ,hδ,hδ1,fun v => ?_⟩
  rw [L2Limits.norm_sq_eq_integral_sq]
  have he := H10.weightedValue_ae PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v
  exact (integral_congr_ae (he.fun_comp (fun t : ℝ => t^2))).le.trans (hs' v)



end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualPotential


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical_oai
