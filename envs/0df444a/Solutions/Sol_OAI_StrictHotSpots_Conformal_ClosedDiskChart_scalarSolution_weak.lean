-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:40:23.731257+00:00
-- url     : https://prove2.me/submissions/a38e02ac-7530-43b6-ab27-ef02359c2760

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_operator_norm_lt_one
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_boundarySolution_weak

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

lemma transport_symm_transport {f : E → ℝ} (hs : Function.support f ⊆ e.source) :
    transport e.symm (transport e f)=f := by
  funext x
  by_cases hx : x ∈ e.source
  · simpa only [transport_apply e.symm hx,e.symm_symm] using transport_source e f hx
  · rw [transport,OpenPartialHomeomorph.symm_target,ite_eq_right hx]
    exact (Function.notMem_support.mp (fun hh => hx (hs hh))).symm

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

lemma transportH10_inner_grad (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v w : H10 e.open_source) :
    inner ℝ (H10.grad e.open_target (transportH10 e he v))
      (H10.grad e.open_target (transportH10 e he w)) =
      inner ℝ (H10.grad e.open_source v) (H10.grad e.open_source w) := by
  have hv := transportH10_grad_sq e he d hd hb v
  have hw := transportH10_grad_sq e he d hd hb w
  have hsum := transportH10_grad_sq e he d hd hb (v+w)
  simp only [map_add,norm_add_sq_real] at hsum
  linarith

lemma transportTest_symm (he' : ContDiffOn ℝ ∞ e e.source)
    (f : smoothTestSpace e.source) :
    transportTest e.symm he' (transportTest e he f)=f := by
  apply Subtype.ext
  exact CompactChart.transport_symm_transport e ((subset_tsupport _).trans f.property.2.2)

lemma transportH10_symm (he' : ContDiffOn ℝ ∞ e e.source)
    (d d' : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hd' : ∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y)
    (hb : Bornology.IsBounded e.target) (hb' : Bornology.IsBounded e.source)
    (v : H10 e.open_source) :
    transportH10 e.symm he' (transportH10 e he v)=v := by
  have H : (transportH10 e.symm he') ∘ (transportH10 e he) = id := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      ((transportH10 e.symm he').continuous.comp (transportH10 e he).continuous) continuous_id
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (transportH10 e.symm he') (transportH10_test e he d hd hb f)).trans
      ((transportH10_test e.symm he' d' hd' hb' (transportTest e he f)).trans
        (congrArg (smoothTestToH10 e.open_source) (transportTest_symm e he he' f)))
  exact congrFun H v



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

end StrictHotSpots.Conformal
end
end ConformalPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedConformalData

noncomputable section
open Set Filter Metric
open scoped ContDiff NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



lemma diskMap_eq : c.diskMap = c.e := by
  apply OpenPartialHomeomorph.ext c.diskMap c.e (fun _ => rfl) (fun _ => rfl)
  exact c.source_eq.symm

lemma diskMap_inverse_deriv : ∀ y ∈ Ω, HasFDerivAt c.diskMap.symm (planeMul (c.d' y)) y :=
  fun y hy => c.inverse_deriv y (c.target_eq.symm ▸ hy)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedConformalData

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma pullDatum_comp_toH1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    (c.pullDatum_comp_H1 hb hs hw).toH1 = (c.pullDatum_H1 hb hs hw).toH1 := by
  apply H1.value_injective diskOpen
  apply Lp.ext
  filter_upwards [(c.pullDatum_comp_H1 hb hs hw).1.coeFn_toLp,
    (c.pullDatum_H1 hb hs hw).1.coeFn_toLp,ae_restrict_mem diskOpen.measurableSet]
    with x hx hy hxd
  exact hx.trans ((c.pullDatum_eq_inner hxd).symm.trans hy.symm)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


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

section ConformalSmoothEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal

lemma complex_real_inner_mul (a u v : ℂ) :
    inner ℝ (a*u) (a*v) = ‖a‖^2 * inner ℝ u v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.normSq_apply]
  ring

lemma plane_inner_gradient_comp {f : Plane → Plane} {u v : Plane → ℝ}
    {a : ℂ} {x : Plane} (hf : HasFDerivAt f (planeMul a) x)
    (hu : DifferentiableAt ℝ u (f x)) (hv : DifferentiableAt ℝ v (f x)) :
    inner ℝ (gradient (u ∘ f) x) (gradient (v ∘ f) x) =
      ‖a‖^2 * inner ℝ (gradient u (f x)) (gradient v (f x)) := by
  rw [plane_gradient_comp hf hu,plane_gradient_comp hf hv,coordinate.inner_map_map,
    complex_real_inner_mul,Complex.norm_conj,coordinate.symm.inner_map_map]

lemma plane_dirichlet_pair (e : OpenPartialHomeomorph Plane Plane)
    (d : Plane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {u v : Plane → ℝ} (hu : DifferentiableOn ℝ u e.target) (hv : DifferentiableOn ℝ v e.target) :
    (∫ y in e.target, inner ℝ (gradient u y) (gradient v y)) =
      ∫ x in e.source, inner ℝ (gradient (u ∘ e) x) (gradient (v ∘ e) x) := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  exact (plane_inner_gradient_comp (hd x hx)
    ((hu _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
    ((hv _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))).symm

lemma inner_grad_toH1 {Ω : Set Plane} {u v : Plane → ℝ}
    (hu : HasH1Gradient Ω u (gradient u)) (hv : HasH1Gradient Ω v (gradient v)) :
    inner ℝ (H1.grad hu.toH1) (H1.grad hv.toH1) =
      ∫ x in Ω, inner ℝ (gradient u x) (gradient v x) := by
  rw [H1.grad_toH1,H1.grad_toH1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.2.1.coeFn_toLp,hv.2.1.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma inner_grad_test {Ω : Set Plane} (ho : IsOpen Ω) {w : Plane → ℝ}
    (hW : HasH1Gradient Ω w (gradient w)) (f : smoothTestSpace Ω) :
    inner ℝ (H1.grad hW.toH1) (H10.grad ho (smoothTestToH10 ho f)) =
      ∫ x in Ω, inner ℝ (gradient w x) (gradient (f : Plane → ℝ) x) := by
  change inner ℝ (H1.grad hW.toH1)
    (H1.grad ((HasH1Gradient.test ho f.property.1 f.property.2.1).toH1)) = _
  exact inner_grad_toH1 hW (HasH1Gradient.test ho f.property.1 f.property.2.1)

variable (e : OpenPartialHomeomorph Plane Plane)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target)

include d hd in
lemma transportTest_dirichlet_pair {w : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (f : smoothTestSpace e.source) :
    (∫ x in e.target, inner ℝ (gradient w x) (gradient (transportTest e he f : Plane → ℝ) x)) =
      ∫ x in e.source, inner ℝ (gradient (w ∘ e) x) (gradient (f : Plane → ℝ) x) := by
  calc
    _ = ∫ x in e.source, inner ℝ (gradient (w ∘ e) x)
        (gradient ((transportTest e he f : Plane → ℝ) ∘ e) x) :=
      plane_dirichlet_pair e d hd hw
        ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn
    _ = _ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      have hg : gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x := by
        unfold gradient
        rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]
      exact congrArg (fun a : Plane => inner ℝ (gradient (w ∘ e) x) a) hg

include d hd in
lemma transportTest_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (f : smoothTestSpace e.source) :
    inner ℝ (H1.grad hW.toH1)
      (H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source (smoothTestToH10 e.open_source f)) :=
  (inner_grad_test e.open_target hW (transportTest e he f)).trans
    ((transportTest_dirichlet_pair e he d hd hw f).trans (inner_grad_test e.open_source hV f).symm)

include d hd hb in


lemma transportH10_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v)) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v) := by
  have H : (fun v : H10 e.open_source =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v))) =
      (fun v : H10 e.open_source => inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v)) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (continuous_const.inner ((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous))
      (continuous_const.inner (H10.grad e.open_source).continuous)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun z : H10 e.open_target =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target z))
      (transportH10_test e he d hd hb f)).trans (transportTest_mixed_grad e he d hd hw hW hV f)
  exact congrFun H v

end StrictHotSpots.Conformal
end
end ConformalSmoothEnergy

section ConformalAffine

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

lemma pull_affine_value {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w)) (v : H10 e.open_source) :
    chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) =
      chartPull e d hd (H1.value hW.toH1)+weightedValue e he d hd v := by
  exact (chartPull e d hd).map_add (H1.value hW.toH1)
    (H1.value (transportH10 e he v).val)

lemma value_add_H10 {S : Set Plane} (ho : IsOpen S) (a : H1 S) (v : H10 ho) :
    H1.value (a+v.val) = H1.value a+H10.value ho v := H1.value.map_add a v.val

lemma ae_lp_sums {μ ν : Measure Plane} (ha : μ ≪ ν)
    (a b : Lp ℝ 2 μ) (c d : Lp ℝ 2 ν)
    (hac : (a : Plane → ℝ) =ᵐ[μ] c) (hbd : (b : Plane → ℝ) =ᵐ[μ] d) :
    (a+b : Lp ℝ 2 μ) =ᵐ[μ] (c+d : Lp ℝ 2 ν) :=
  (Lp.coeFn_add a b).trans ((hac.add hbd).trans (Filter.EventuallyEq.symm (ha.ae_le (Lp.coeFn_add c d))))

include hb in
lemma affine_value_ae {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    (chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) : Plane → ℝ)
      =ᵐ[chartMeasure e d] H1.value (hV.toH1+v.val) := by
  have ha := chartPull_test_ae e d hd hW.1
  have hc := (chartMeasure_ac e d).ae_le hV.1.coeFn_toLp
  have hv := weightedValue_ae e he d hd hb v
  have hs := ae_lp_sums (chartMeasure_ac e d)
    (chartPull e d hd (H1.value hW.toH1)) (weightedValue e he d hd v)
    (H1.value hV.toH1) (H10.value e.open_source v) (ha.trans (Filter.EventuallyEq.symm hc)) hv.symm
  exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (chartMeasure e d) => (f : Plane → ℝ))
    (pull_affine_value e he d hd hW v))).trans
    (hs.trans (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (volume.restrict e.source) =>
      (f : Plane → ℝ)) (value_add_H10 e.open_source hV.toH1 v))).symm)

lemma isometry_value_pair {μ ν : Measure Plane}
    (L : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (a b : Lp ℝ 2 μ) {f g : Plane → ℝ}
    (ha : (L a : Plane → ℝ) =ᵐ[ν] f) (hb : (L b : Plane → ℝ) =ᵐ[ν] g) :
    inner ℝ a b = ∫ x, f x*g x ∂ν := by
  apply (L.inner_map_map a b).symm.trans
  apply (L2.inner_def _ _).trans
  apply integral_congr_ae
  filter_upwards [ha,hb] with x hx hy
  rw [hx,hy,Real.inner_apply,mul_comm]

end StrictHotSpots.Conformal
end
end ConformalAffine

section ActualScalarPull

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Laplacian
namespace StrictHotSpots.Conformal

lemma observe_inner {S : Set Plane} {ν : Measure Plane} {C : ℝ≥0∞}
    (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict S) (u v : H1 S) :
    inner ℝ (SubcriticalExtension.observe hC hν u) (SubcriticalExtension.observe hC hν v) =
      ∫ x, H1.value u x * H1.value v x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value u),
    Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value v)] with x hx hy
  change inner ℝ (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value u) x)
    (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value v) x) = _
  rw [hx,hy,real_inner_comm]
  rfl

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma potential_diskMap : potentialMeasure c.diskMap c.d (firstPositiveNeumannValue Ω) =
    c.potential := congrArg (fun e => potentialMeasure e c.d (firstPositiveNeumannValue Ω)) c.diskMap_eq

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualScalarPull


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma datumCorrection_spec {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl =
    (c.pullDatum_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val :=
  (c.boundarySolution_datum_class hb hs hμ hw hl).choose_spec

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10
lemma pair_apply (μ : ℝ) (u v : H1 Ω) : pair μ u v =
    inner ℝ (H1.grad v) (H1.grad u)-μ*inner ℝ (H1.value v) (H1.value u) := rfl

lemma pair_comm (μ : ℝ) (u v : H1 Ω) : pair μ u v=pair μ v u := by
  rw [pair_apply,pair_apply]
  exact congrArg₂ (fun a b : ℝ => a-μ*b)
    (real_inner_comm (H1.grad u) (H1.grad v))
    (real_inner_comm (H1.value u) (H1.value v))

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section PhysicalSolutionWeak

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

lemma inner_H1grad_add_single {S : Set Plane} (a b z : H1 S) :
    inner ℝ (H1.grad (a+b)) (H1.grad z) =
    inner ℝ (H1.grad a) (H1.grad z)+inner ℝ (H1.grad b) (H1.grad z) := by
  rw [map_add,inner_add_left]

include d hd hb in
lemma affine_H10_grad_pair {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (u v : H10 e.open_source) :
    inner ℝ (H1.grad (hW.toH1+(transportH10 e he u).val))
      (H10.grad e.open_target (transportH10 e he v)) =
    inner ℝ (H1.grad (hV.toH1+u.val)) (H10.grad e.open_source v) := by
  exact (inner_H1grad_add_single hW.toH1 (transportH10 e he u).val
    (transportH10 e he v).val).trans
      ((congrArg₂ (fun a b : ℝ => a+b) (transportH10_mixed_grad e he d hd hb hw hW hV v)
        (transportH10_inner_grad e he d hd hb u v)).trans
          (inner_H1grad_add_single hV.toH1 u.val v.val).symm)

include hd hb in
lemma affine_H10_mass_pair {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (u v : H10 e.open_source) :
    inner ℝ (H1.value (hW.toH1+(transportH10 e he u).val))
      (H10.value e.open_target (transportH10 e he v)) =
    ∫ x, H1.value (hV.toH1+u.val) x*H10.value e.open_source v x ∂chartMeasure e d :=
  isometry_value_pair (chartPull e d hd) _ _
    (affine_value_ae e he d hd hb hW hV u) (weightedValue_ae e he d hd hb v).symm

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma physicalSolution_mixed_grad {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (v : H10 diskOpen) :
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H10.grad c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) =
    inner ℝ (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl)) (H10.grad diskOpen v) := by
  have hh := affine_H10_grad_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp))
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw) (c.pullDatum_comp_H1 hb hs hw)
    (c.datumCorrection hb hs hμ hw hl) v
  apply hh.trans
  apply congrArg (fun U : H1 disk => inner ℝ (H1.grad U) (H10.grad diskOpen v))
  exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
    (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm

lemma physicalSolution_mixed_mass {w : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (v : H10 diskOpen) :
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H10.value c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) =
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl))
      (H10.weightedValue diskOpen c.densityBound_ne_top (c.density_bound hμ) v) := by
  have hh := affine_H10_mass_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw) (c.pullDatum_comp_H1 hb hs hw)
    (c.datumCorrection hb hs hμ hw hl) v
  have he : (c.pullDatum_comp_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val=
      boundarySolution c.densityBound_ne_top (c.density_bound hμ)
        (c.datumTrace w hw.continuousOn) hl :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  let S := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  have hr := congrArg (fun U : H1 disk =>
    ∫ x, H1.value U x*H10.value diskOpen v x ∂chartMeasure c.diskMap c.d) he
  have hp := potentialMeasure_integral c.diskMap c.d hμ
    (fun x => H1.value S x*H10.value diskOpen v x)
  have hq := congrArg (fun ν : Measure Plane => ∫ x,
    H1.value S x*H10.value diskOpen v x ∂ν) c.potential_diskMap
  exact (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr)).trans
    (hp.symm.trans (hq.trans (observe_inner c.densityBound_ne_top (c.density_bound hμ) S v.val).symm))

lemma pair_forward {S : Set Plane} (μ : ℝ) (u v : H1 S) :
    PhysicalHelmholtz.pair μ u v = inner ℝ (H1.grad u) (H1.grad v)-
      μ*inner ℝ (H1.value u) (H1.value v) :=
  (PhysicalHelmholtz.pair_comm μ u v).trans (PhysicalHelmholtz.pair_apply μ v u)

lemma physicalSolution_transported_weak (hne : Ω.Nonempty) (hpos : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) (t : H10 diskOpen) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl)
      (show H1 Ω from (transportH10 c.diskMap c.diskMap_inverse_smooth t).val)=0 := by
  have hn := c.operator_norm_lt_one hb hne hpos
  have hwk := boundarySolution_weak c.densityBound_ne_top (c.density_bound hμ) hn
    (c.datumTrace w hw.continuousOn) hl t
  have hg := c.physicalSolution_mixed_grad hb hs hμ hw hl t
  have hm := c.physicalSolution_mixed_mass hb hs hμ hw hl t
  exact (pair_forward _ _ _).trans (sub_eq_zero.mpr (hg.trans (hwk.trans hm.symm)))

lemma physicalSolution_weak (hne : Ω.Nonempty) (hpos : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (v : H10 (show IsOpen Ω from c.diskMap.open_target)) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl) v.val=0 := by
  let t : H10 diskOpen := transportH10 c.diskMap.symm c.diskMap_smooth v
  have ht : transportH10 c.diskMap c.diskMap_inverse_smooth t=v :=
    transportH10_symm c.diskMap.symm c.diskMap_smooth c.diskMap_inverse_smooth c.d' c.d
      c.diskMap_inverse_deriv c.diskMap_deriv diskBounded hb v
  have he := c.physicalSolution_transported_weak hb hs hμ hne hpos hw hl t
  exact (congrArg (fun V : H10 (show IsOpen Ω from c.diskMap.open_target) =>
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω) (c.physicalSolution hb hs hμ hw hl) V.val) ht).symm.trans he

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end PhysicalSolutionWeak

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

lemma scalarSolution_weak_oai {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (v : H10 hΩ.2.1) :
    PhysicalHelmholtz.pair (firstPositiveNeumannValue Ω)
      (c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw) v.val=0 :=
  c.physicalSolution_weak hΩ.2.2.1 hΩ.2.2.2.2 hμ.le hΩ.1 hμ hw _ v

end StrictHotSpots.Conformal.ClosedDiskChart

end
end PhysicalMultiplierLimit


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak_oai
