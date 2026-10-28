-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:30:46.909113+00:00
-- url     : https://prove2.me/submissions/4c0d9771-f729-4ed0-9704-35c960975dc3

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_subcritical
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_value_K_of_trace

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
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
namespace StrictHotSpots

lemma integral_inner_gradient_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient φ x)) =
      -(∫ x in Ω, Δ f x * φ x) := by
  let b := stdOrthonormalBasis ℝ Plane
  have hd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (b i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i)) Ω :=
    ((hd i).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have he (x : Plane) : inner ℝ (gradient f x) (gradient φ x) =
      ∑ i, fderiv ℝ f x (b i) * fderiv ℝ φ x (b i) := by
    rw [← b.sum_inner_mul_inner (gradient f x) (gradient φ x)]
    simp only [inner_gradient_left, inner_gradient_right, starRingEnd_apply, star_trivial]
  have hl (x : Plane) (hx : x ∈ Ω) : Δ f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    rw [fderiv_clm_apply
      ((((hf x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hi (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ f x (b i) * fderiv ℝ φ x (b i)) (volume.restrict Ω) := by
    apply Integrable.restrict
    exact integrable_mul_test hΩ (hd i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have hj (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hdd i).continuousOn hφ.continuous hc hs).restrict
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_test_fderiv hΩ (hd _) hφ hc hs]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hl x hx, Finset.sum_mul]

end StrictHotSpots







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

section L2InnerToLpCombinedLayer
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Inner
lemma toLp_pair {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy]
end StrictHotSpots.L2Inner
end L2InnerToLpCombinedLayer

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

section H10HelmholtzCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace Laplacian ContDiff
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)



lemma helmholtz_pair {f : Plane → ℝ} {lam : ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω)
    (hv : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp (gradient f) 2 (volume.restrict Ω))
    (hp : ∀ x ∈ Ω, Δ f x = -lam * f x) (u : H10 hΩ) :
    inner ℝ (hg.toLp _) (grad hΩ u) = lam * inner ℝ (hv.toLp _) (value hΩ u) := by
  let A : H10 hΩ →L[ℝ] ℝ := (innerSL ℝ (hg.toLp _)).comp (grad hΩ)
  let B : H10 hΩ →L[ℝ] ℝ := lam • (innerSL ℝ (hv.toLp _)).comp (value hΩ)
  change A u = B u
  apply isClosed_property (dense_smoothTestToH10 hΩ) (isClosed_eq A.continuous B.continuous) _ u
  intro t
  change inner ℝ (hg.toLp _) ((test_gradient_memLp t.property.1 t.property.2.1).toLp _) =
    lam * inner ℝ (hv.toLp _) ((test_memLp t.property.1 t.property.2.1).toLp _)
  rw [L2Inner.toLp_pair, L2Inner.toLp_pair]
  rw [integral_inner_gradient_test hΩ hf t.property.1 t.property.2.1 t.property.2.2]
  have he : (∫ x in Ω, Δ f x * (t : Plane → ℝ) x) =
      -lam * ∫ x in Ω, f x * (t : Plane → ℝ) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hp x hx]
    ring
  rw [he]
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  rw [show (fun x => (t : Plane → ℝ) x * f x) = (fun x => f x * (t : Plane → ℝ) x) by funext; ring]
  ring

end StrictHotSpots.H10
end H10HelmholtzCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section GapWeakPDECombinedLayer
open scoped Laplacian ContDiff InnerProductSpace
open Set MeasureTheory Filter
namespace StrictHotSpots
open Laplacian

lemma directionalDerivative_contDiffOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (e : Plane) :
    ContDiffOn ℝ ∞ (directionalDerivative f e) Ω :=
  (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

lemma laplacian_eq_sum_directional {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω) :
    (Δ f) x = ∑ i : Fin 2, directionalDerivative (directionalDerivative f (planeBasis i))
      (planeBasis i) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f planeBasis]
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hΩ (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fderiv ℝ f) x) (planeBasis i)) (planeBasis i) =
    (fderiv ℝ (fun y => (fderiv ℝ f y) (planeBasis i)) x) (planeBasis i)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp


end StrictHotSpots

end GapWeakPDECombinedLayer


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

include d hd hb in
lemma smooth_H10_value_pair {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    inner ℝ (H1.value hW.toH1) (H10.value e.open_target (transportH10 e he v)) =
      ∫ x, H1.value hV.toH1 x * H10.value e.open_source v x ∂chartMeasure e d := by
  apply isometry_value_pair (chartPull e d hd)
  · have ha : (H1.value hV.toH1 : Plane → ℝ) =ᵐ[chartMeasure e d] w ∘ e :=
      (chartMeasure_ac e d).ae_le hV.1.coeFn_toLp
    exact (chartPull_test_ae e d hd hW.1).trans ha.symm
  · exact (weightedValue_ae e he d hd hb v).symm

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma potential_diskMap : potentialMeasure c.diskMap c.d (firstPositiveNeumannValue Ω) =
    c.potential := congrArg (fun e => potentialMeasure e c.d (firstPositiveNeumannValue Ω)) c.diskMap_eq

lemma smooth_mixed_mass (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hμ : 0 ≤ firstPositiveNeumannValue Ω) (v : H10 diskOpen) :
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (c.pullDatum_H1 hb hs hw).toH1)
      (H10.weightedValue diskOpen c.densityBound_ne_top (c.density_bound hμ) v) =
    firstPositiveNeumannValue Ω * inner ℝ
      (H1.value (smooth_closure_H1 c.diskMap.open_target hb hs hw).toH1)
      (H10.value c.diskMap.open_target (transportH10 c.diskMap c.diskMap_inverse_smooth v)) := by
  have hh := smooth_H10_value_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 c.diskMap.open_target hb hs hw) (c.pullDatum_comp_H1 hb hs hw) v
  have hr := congrArg (fun U : H1 disk =>
    ∫ x, H1.value U x * H10.value diskOpen v x ∂chartMeasure c.diskMap c.d)
    (c.pullDatum_comp_toH1 hb hs hw)
  change inner ℝ (SubcriticalExtension.observe _ _ _) (SubcriticalExtension.observe _ _ v.val) = _
  apply (observe_inner c.densityBound_ne_top (c.density_bound hμ)
    (c.pullDatum_H1 hb hs hw).toH1 v.val).trans
  have hq := congrArg (fun ν : Measure Plane => ∫ x,
    H1.value (c.pullDatum_H1 hb hs hw).toH1 x * H10.value diskOpen v x ∂ν)
    c.potential_diskMap
  exact hq.symm.trans ((potentialMeasure_integral c.diskMap c.d hμ _).trans
    (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr).symm))

lemma smooth_pull_weak (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hμ : 0 ≤ firstPositiveNeumannValue Ω)
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) :
    SubcriticalExtension.WeakPotential diskOpen c.densityBound_ne_top (c.density_bound hμ)
      (c.pullDatum_H1 hb hs hw).toH1 := by
  intro v
  have hW := smooth_closure_H1 c.diskMap.open_target hb hs hw
  have hh := transportH10_mixed_grad c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp)) hW (c.pullDatum_comp_H1 hb hs hw) v
  have hr := congrArg (fun U : H1 disk => inner ℝ (H1.grad U) (H10.grad diskOpen v))
    (c.pullDatum_comp_toH1 hb hs hw)
  have he := H10.helmholtz_pair c.diskMap.open_target (hw.mono subset_closure) hW.1 hW.2.1 hp
    (transportH10 c.diskMap c.diskMap_inverse_smooth v)
  exact (hh.trans hr).symm.trans (he.trans (c.smooth_mixed_mass hb hs hw hμ v).symm)



theorem smooth_K_representation (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hne : Ω.Nonempty) (hμ : 0 < firstPositiveNeumannValue Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) (x : disk) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    w (c.F x) = ∫ s, fullBoundaryK c.densityBound_ne_top (c.density_bound hμ.le) x s *
      w (c.F s) ∂boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  obtain ⟨δ,hδ,hδ1,hsub⟩ := c.subcritical hb hne hμ
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hb hs hw
  exact value_K_of_trace c.densityBound_ne_top (c.density_bound hμ.le) hδ.le hδ1 hsub
    (c.datumTrace w hw.continuousOn) hB (c.pullDatum_smooth (hw.mono subset_closure))
    (c.pullDatum_continuous hw.continuousOn) (c.pullDatum_H1 hb hs hw) (fun _ => rfl)
    (c.smooth_pull_weak hb hs hw hμ.le hp) x

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualScalarPull

section OriginalGradientKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Laplacian
namespace StrictHotSpots
lemma laplacian_continuousOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) : ContinuousOn (Δ f) Ω := by
  have hh : ContinuousOn (fun x => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) x) Ω :=
    continuousOn_finsetSum _ fun i _ =>
      (directionalDerivative_contDiffOn hΩ
        (directionalDerivative_contDiffOn hΩ hf (planeBasis i)) (planeBasis i)).continuousOn
  exact hh.congr fun x hx => (laplacian_eq_sum_directional hΩ hf hx)



lemma eigenfunction_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω) :
    (Δ u) x + firstPositiveNeumannValue Ω * u x = 0 := by
  have hsu : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hcont : ContinuousOn (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) Ω :=
    (laplacian_continuousOn hΩ hsu).add (hsu.continuousOn.const_mul _)
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hΩ.measurableSet (μ := volume)) ?_
  · have hre : (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) =ᵐ[volume.restrict Ω]
        (fun _ => 0) := (ae_restrict_iff' hΩ.measurableSet).mpr hae
    exact (Measure.eqOn_open_of_ae_eq hre hΩ hcont continuousOn_const) hx
  intro φ hφ hc hs
  have htest := HasH1Gradient.test hΩ hφ hc
  have heq := hu.2.2.2 φ (gradient φ) htest
  rw [integral_inner_gradient_test hΩ hsu hφ hc hs] at heq
  have h1 : IntegrableOn (fun y => (Δ u) y * φ y) Ω :=
    (integrable_mul_test hΩ (laplacian_continuousOn hΩ hsu) hφ.continuous hc hs).integrableOn
  have h2 : IntegrableOn (fun y => u y * φ y) Ω :=
    (integrable_mul_test hΩ hsu.continuousOn hφ.continuous hc hs).integrableOn
  have heq0 : (∫ y in Ω, ((Δ u) y + firstPositiveNeumannValue Ω * u y) * φ y) = 0 := by
    simp only [add_mul, mul_assoc]
    rw [integral_add h1 (h2.const_mul _), integral_const_mul]
    linarith
  rw [setIntegral_mul_test hs] at heq0
  simpa only [smul_eq_mul, mul_comm] using heq0


lemma directionalDerivative_commute {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω)
    (e d : Plane) : directionalDerivative (directionalDerivative f e) d x =
      directionalDerivative (directionalDerivative f d) e x := by
  have hh := (hf x hx).contDiffAt (hΩ.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hΩ (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)
  change (fderiv ℝ (fun y => (fderiv ℝ f y) e) x) d =
    (fderiv ℝ (fun y => (fderiv ℝ f y) d) x) e
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hh.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; decide) d e

lemma directionalDerivative_congr {Ω : Set Plane} (hΩ : IsOpen Ω)
    {f g : Plane → ℝ} (heq : EqOn f g Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    directionalDerivative f e x = directionalDerivative g e x := by
  have hh : f =ᶠ[nhds x] g := Filter.eventually_of_mem (hΩ.mem_nhds hx) heq
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L e) hh.fderiv_eq

lemma laplacian_directionalDerivative {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    (Δ (directionalDerivative f e)) x = directionalDerivative (Δ f) e x := by
  have D (d : Plane) := directionalDerivative_contDiffOn hΩ hf d
  have DD (d c : Plane) := directionalDerivative_contDiffOn hΩ (D d) c
  rw [laplacian_eq_sum_directional hΩ (D e) hx]
  have hs : EqOn (Δ f) (fun y => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) y) Ω :=
    fun y hy => laplacian_eq_sum_directional hΩ hf hy
  rw [directionalDerivative_congr hΩ hs hx e]
  have heq (i : Fin 2) :
      directionalDerivative (directionalDerivative (directionalDerivative f e) (planeBasis i))
        (planeBasis i) x =
      directionalDerivative (directionalDerivative (directionalDerivative f (planeBasis i))
        (planeBasis i)) e x := by
    rw [directionalDerivative_congr hΩ
      (fun y hy => directionalDerivative_commute hΩ hf hy e (planeBasis i)) hx]
    exact directionalDerivative_commute hΩ (D (planeBasis i)) hx e (planeBasis i)
  simp_rw [heq]
  unfold directionalDerivative
  rw [fderiv_fun_sum]
  · simp
  · intro i _
    exact ((DD (planeBasis i) (planeBasis i) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)



lemma eigenfunction_derivative_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω)
    (e : Plane) : (Δ (directionalDerivative u e)) x +
      firstPositiveNeumannValue Ω * directionalDerivative u e x = 0 := by
  have hf : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hs : EqOn (Δ u) (fun y => -(firstPositiveNeumannValue Ω) * u y) Ω := by
    intro y hy
    linear_combination eigenfunction_helmholtz hΩ hu hy
  rw [laplacian_directionalDerivative hΩ hf hx,
    directionalDerivative_congr hΩ hs hx e]
  have hd := ((hf x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [directionalDerivative, fderiv_const_mul hd,
    smul_apply, smul_eq_mul]
  ring

end StrictHotSpots
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Laplacian Topology
namespace StrictHotSpots
lemma closed_directional_eq {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    fderivWithin ℝ u (closure Ω) x e = directionalDerivative u e x := by
  rw [fderivWithin_of_mem_nhds (mem_of_superset (ho.mem_nhds hx) subset_closure)]
  rfl

namespace Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



theorem gradient_K_representation_oai (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) (x : disk) (e : Plane) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    inner ℝ (gradient u (c.F x)) e =
      ∫ s, fullBoundaryK c.densityBound_ne_top
        (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) x s *
        inner ℝ (closedGradient Ω u (c.F s)) e ∂boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hh := c.smooth_K_representation hΩ.2.2.1 hΩ.2.2.2.2 hΩ.1
    (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne)
    (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 e) ?_ x
  · have hx : c.F x ∈ Ω := by rw [← c.diskMap_agrees x.property]; exact c.diskMap.map_source x.property
    rw [closed_directional_eq hΩ.2.1 hx e] at hh
    simpa only [gradient,closedGradient,InnerProductSpace.toDual_symm_apply,
      directionalDerivative] using hh
  intro y hy
  have heq : (fun z => fderivWithin ℝ u (closure Ω) z e) =ᶠ[nhds y]
      directionalDerivative u e :=
    Filter.eventually_of_mem (hΩ.2.1.mem_nhds hy)
      (fun _ hz => closed_directional_eq hΩ.2.1 hz e)
  rw [(InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
    closed_directional_eq hΩ.2.1 hy e]
  linear_combination eigenfunction_derivative_helmholtz hΩ.2.1 hu hy e

end Conformal.ClosedDiskChart
end StrictHotSpots
end
end
end OriginalGradientKernel


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation_oai
