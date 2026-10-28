-- Prove2me | solution 1 for OAI.StrictHotSpots.Hodge.vectorForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:41:07.816998+00:00
-- url     : https://prove2.me/submissions/ce937902-3198-47b7-9711-f1310e1d55db

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

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
namespace StrictHotSpots


lemma existsUnique_of_coercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B u v = ℓ v := by
  let e := hB.continuousLinearEquivOfBilin
  let y := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨e.symm y, ?_, ?_⟩
  · intro v
    calc
      B (e.symm y) v = inner ℝ (e (e.symm y)) v :=
        (hB.continuousLinearEquivOfBilin_apply _ _).symm
      _ = ℓ v := by simp [y, InnerProductSpace.toDual_symm_apply]
  · intro u hu
    apply e.injective
    rw [e.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    calc
      inner ℝ (e u) v = B u v := hB.continuousLinearEquivOfBilin_apply _ _
      _ = ℓ v := hu v
      _ = inner ℝ y v := InnerProductSpace.toDual_symm_apply.symm




lemma integral_test_derivative_zero {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    (∫ x, (fderiv ℝ φ x) e) = 0 := by
  have hdi : Integrable (fun x => (fderiv ℝ φ x) e) volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ e)
  have hint := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Plane => (1 : ℝ)) (g := φ) (v := e) (μ := volume)
    (by simp) (by simpa using hdi)
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const (1 : ℝ))
    (fun x _ => hφ.differentiable (by simp) x)
  simpa using hint

lemma HasH1Gradient.const {Ω : Set Plane} (hbound : Bornology.IsBounded Ω) (a : ℝ) :
    HasH1Gradient Ω (fun _ => a) 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbound.measure_lt_top.ne
  refine ⟨memLp_const a, MemLp.zero, ?_⟩
  intro φ hφ hc hs e
  have hr : (∫ x in Ω, (fderiv ℝ φ x) e) = (∫ x, (fderiv ℝ φ x) e) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport (fun y => (fderiv ℝ φ y) e) :=
      fun hh => hx (hs (tsupport_fderiv_apply_subset ℝ e hh))
    exact image_eq_zero_of_notMem_tsupport (f := fun y => (fderiv ℝ φ y) e) hnot
  simp only [Pi.zero_apply, inner_zero_left, zero_mul, integral_zero, neg_zero,
    integral_const_mul, hr, integral_test_derivative_zero hφ hc e, mul_zero]

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)



lemma existsUnique_energy_solution (hb : Bornology.IsBounded Ω)
    (ℓ : H10 hΩ →L[ℝ] ℝ) :
    ∃! u : H10 hΩ, ∀ v : H10 hΩ, energy hΩ u v = ℓ v := by
  exact @existsUnique_of_coercive (H10 hΩ) (H10.normedAddCommGroup hΩ)
    (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    (energy hΩ) (energy_coercive hΩ hb) ℓ


end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff

open scoped Laplacian







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
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
namespace StrictHotSpots

lemma laplacian_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (g : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (x : E) :
    Δ (f ∘ g) x = Δ f (g x) := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map g)]
  have he : iteratedFDeriv ℝ 2 (f ∘ g) x =
      (iteratedFDeriv ℝ 2 f (g x)).compContinuousLinearMap (fun _ => g.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa [iteratedFDerivWithin_univ] using g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
      uniqueDiffOn_univ (Set.mem_univ (g x)) 2
  simp only [he, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> simp

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
section MainVariationalCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
namespace StrictHotSpots






lemma rayleigh_inequality {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0)
    (hpos : 0 < ∫ x in Ω, (v x) ^ 2) :
    firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2) ≤
      ∫ x in Ω, ‖g x‖ ^ 2 := by
  apply (le_div_iff₀ hpos).mp
  apply csInf_le
  · exact ⟨0, fun _ hr => rayleighValues_nonneg hr⟩
  · exact ⟨v, g, hv, hm, hpos, rfl⟩

lemma rayleigh_inequality_all {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0) :
    firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2) ≤ ∫ x in Ω, ‖g x‖ ^ 2 := by
  have hnn : 0 ≤ ∫ x in Ω, (v x) ^ 2 := integral_nonneg fun x => sq_nonneg (v x)
  rcases eq_or_lt_of_le hnn with hz | hp
  · rw [← hz, mul_zero]
    exact integral_nonneg fun x => sq_nonneg ‖g x‖
  · exact rayleigh_inequality hv hm hp



end StrictHotSpots
end MainVariationalCombinedLayer

section L2InnerToLpCombinedLayer
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Inner
lemma toLp_left {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : α → E} (hf : MemLp f 2 μ) (g : Lp E 2 μ) :
    inner ℝ (hf.toLp f) g = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
end StrictHotSpots.L2Inner
end L2InnerToLpCombinedLayer

section H1RayleighFormCombinedLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace StrictHotSpots.H1
variable {Ω : Set Plane}

variable (hb : Bornology.IsBounded Ω)

lemma mean_eq (u : H1 Ω) : mean hb u = ∫ x in Ω, value u x := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  change inner ℝ ((memLp_const (1 : ℝ)).toLp _) (value u) = _
  rw [L2Inner.toLp_left]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]

end StrictHotSpots.H1
end H1RayleighFormCombinedLayer

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
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section HelmholtzMollificationCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz

lemma directional_convolution {u : ℂ → ℂ} {φ : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x v : ℂ) :
    fderiv ℝ (u ⋆[smulFlip] φ) x v = (u ⋆[smulFlip] (fun z => fderiv ℝ φ z v)) x := by
  rw [(hc.hasFDerivAt_convolution_right smulFlip hu (hφ.of_le (by norm_num)) x).fderiv]
  exact convolution_precompR_apply _ hu (hc.fderiv ℝ)
    (hφ.continuous_fderiv (by norm_num)) x v

lemma laplacian_convolution {u : ℂ → ℂ} {φ : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    (Δ (u ⋆[smulFlip] φ)) x = (u ⋆[smulFlip] (Δ φ)) x := by
  have hφ' : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hconv : ContDiff ℝ ∞ (u ⋆[smulFlip] φ) := hc.contDiff_convolution_right smulFlip hu hφ
  have hcv' : Differentiable ℝ (fderiv ℝ (u ⋆[smulFlip] φ)) :=
    (hconv.fderiv_right (show ∞+1 ≤ ∞ by simp)).differentiable (by simp)
  have he (v w : ℂ) :
      fderiv ℝ (fderiv ℝ (u ⋆[smulFlip] φ)) x v w =
        (u ⋆[smulFlip] (fun y => fderiv ℝ (fderiv ℝ φ) y v w)) x := by
    have hfun : (fun y => fderiv ℝ (u ⋆[smulFlip] φ) y w) =
        (u ⋆[smulFlip] fun y => fderiv ℝ φ y w) := funext fun y => directional_convolution hu hφ hc y w
    have haux := directional_convolution hu (hφ'.clm_apply contDiff_const)
      (hc.fderiv_apply ℝ w) x v
    rw [← hfun] at haux
    simpa only [fderiv_clm_apply hcv'.differentiableAt (differentiableAt_const w),
      fderiv_clm_apply (hφ'.differentiable (by simp)).differentiableAt (differentiableAt_const w),
      fderiv_const_apply,add_apply,ContinuousLinearMap.comp_apply,
      zero_apply,map_zero,add_zero,zero_add,ContinuousLinearMap.flip_apply] using haux
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,he]
  have hcc (v w : ℂ) : HasCompactSupport (fun y => fderiv ℝ (fderiv ℝ φ) y v w) :=
    ((hc.fderiv ℝ).fderiv ℝ).comp_left (g := fun F : ℂ →L[ℝ] ℂ →L[ℝ] ℝ => F v w) (by simp)
  have hints (v w : ℂ) : ConvolutionExistsAt u (fun y => fderiv ℝ (fderiv ℝ φ) y v w) x smulFlip volume :=
    (hcc v w).convolutionExists_right smulFlip hu
      (((hφ'.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply continuous_const) x
  exact ((hints 1 1).distrib_add (hints Complex.I Complex.I)).symm

lemma laplacian_reflect_translate {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x y : ℂ) :
    (Δ (fun z => φ (x-z))) y = (Δ φ) (x-y) := by
  have hφ' : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hd (z : ℂ) : HasFDerivAt (fun z : ℂ => x-z) (-ContinuousLinearMap.id ℝ ℂ) z := by
    simpa only [zero_sub,Pi.sub_apply,id_eq] using! (hasFDerivAt_const x z).sub (hasFDerivAt_id z)
  have hD : fderiv ℝ (fun z => φ (x-z)) = fun z => -(fderiv ℝ φ (x-z)) := by
    funext z
    have h := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z (hd z)).fderiv
    simpa only [ContinuousLinearMap.comp_neg,ContinuousLinearMap.comp_id,Function.comp_def] using! h
  have hDD : fderiv ℝ (fderiv ℝ (fun z => φ (x-z))) y = fderiv ℝ (fderiv ℝ φ) (x-y) := by
    rw [hD]
    have h := (((hφ'.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y (hd y)).neg).fderiv
    simpa only [ContinuousLinearMap.comp_neg,ContinuousLinearMap.comp_id,neg_neg,Function.comp_def,Pi.neg_apply] using! h
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,hDD]


lemma convolution_solves {U : Set ℂ} {μ : ℝ} {u : ℂ → ℂ}
    (hu : LocallyIntegrable u volume) (hPDE : WeakEquation U μ u)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {x : ℂ}
    (hsupp : tsupport (fun z => φ (x-z)) ⊆ U) :
    (Δ (u ⋆[smulFlip] φ)) x = -μ • (u ⋆[smulFlip] φ) x := by
  rw [laplacian_convolution hu hφ hc]
  have ht : ContDiff ℝ ∞ (fun z => φ (x-z)) := hφ.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun z => φ (x-z)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hp := hPDE _ ht hct hsupp
  simpa only [convolution_def,smulFlip,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply,laplacian_reflect_translate hφ] using hp

end StrictHotSpots.Helmholtz
end HelmholtzMollificationCombinedLayer

section HelmholtzWeakCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz

lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [mul_zero,mul_one_div,mollifier] using h

lemma smoothen_contDiff {u : ℂ → ℂ} (hu : LocallyIntegrable u volume) (n : ℕ) :
    ContDiff ℝ ∞ (smoothen u n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_right _ hu
    (mollifier n).contDiff_normed

lemma smoothen_tendsto {u : ℂ → ℂ} (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothen u n x) atTop (𝓝 (u x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_radius_tendsto (K := 2) (Eventually.of_forall (fun n => by
      dsimp [mollifier]
      rw [mul_one_div])) hu
  simpa only [smoothen,smulFlip,convolution_flip] using h

lemma reflected_mollifier_support (n : ℕ) (x : ℂ) :
    tsupport (fun z => (mollifier n).normed volume (x-z)) ⊆ closedBall x (mollifier n).rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hz' : x-z ∈ ball (0:ℂ) (mollifier n).rOut := by
    rwa [← (mollifier n).support_normed_eq (μ := volume)]
  rw [mem_closedBall]
  have hzdist : dist z x < (mollifier n).rOut := by
    simpa [mem_ball,dist_eq_norm,norm_sub_rev] using hz'
  exact hzdist.le

lemma smoothen_PDE {u : ℂ → ℂ} {a : ℂ} {R μ : ℝ}
    (hu : LocallyIntegrable u volume) (hPDE : WeakEquation (ball a R) μ u)
    (n : ℕ) {x : ℂ} (hx : x ∈ ball a (R-(mollifier n).rOut)) :
    (Δ (smoothen u n)) x = -μ • smoothen u n x := by
  apply convolution_solves hu hPDE (mollifier n).contDiff_normed
    (mollifier n).hasCompactSupport_normed
  intro z hz
  have hp := reflected_mollifier_support n x hz
  rw [mem_ball] at hx ⊢
  rw [mem_closedBall] at hp
  have ht := dist_triangle z x a
  linarith


lemma WeakEquation.mono {U V : Set ℂ} {μ : ℝ} {u : ℂ → ℂ}
    (h : WeakEquation U μ u) (hVU : V ⊆ U) : WeakEquation V μ u :=
  fun φ hφ hc hs => h φ hφ hc (hs.trans hVU)




end StrictHotSpots.Helmholtz
end HelmholtzWeakCombinedLayer

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
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section

section HarmonicRadialRegularityBaseLayer
open Set MeasureTheory Metric _root_.Complex Function Filter Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Weyl

lemma radialBump_contDiff (R : ℝ) : ContDiff ℝ ∞ (radialBump R) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma radialBump_zero {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R ≤ ‖z‖) :
    radialBump R z = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  nlinarith [norm_nonneg z]

lemma radialBump_support {R : ℝ} (hR : 0 ≤ R) :
    tsupport (radialBump R) ⊆ closedBall (0:ℂ) R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [mem_closedBall,dist_zero_right]
  by_contra h
  exact hz (radialBump_zero hR (le_of_not_ge h))

lemma radialBump_compact {R : ℝ} (hR : 0 ≤ R) : HasCompactSupport (radialBump R) :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (radialBump_support hR)

lemma radialBump_integral_pos {R : ℝ} (hR : 0 < R) : 0 < ∫ z, radialBump R z := by
  apply (integral_pos_iff_support_of_nonneg (fun z => expNegInvGlue.nonneg _)
    ((radialBump_contDiff R).continuous.integrable_of_hasCompactSupport (radialBump_compact hR.le))).mpr
  have hb : ball (0:ℂ) R ⊆ support (radialBump R) := by
    intro z hz
    apply ne_of_gt
    apply expNegInvGlue.pos_of_pos
    have hn : ‖z‖ < R := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  exact (measure_ball_pos volume (0:ℂ) hR).trans_le (measure_mono hb)

lemma radialBump_polar (R r θ : ℝ) : radialBump R (Complex.polarCoord.symm (r,θ)) =
    expNegInvGlue (R^2-r^2) := by simp only [radialBump,Complex.norm_polarCoord_symm,sq_abs]

lemma polar_continuous : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
  have he : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      fun p => (p.1:ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  rw [he]
  fun_prop

lemma polar_circle (x : ℂ) (r θ : ℝ) : x-Complex.polarCoord.symm (r,θ) = circleMap x (-r) θ := by
  rw [circleMap,Complex.polarCoord_symm_apply,Complex.exp_mul_I]
  push_cast
  ring

lemma angle_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℂ → F) (x : ℂ) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap x r θ)) = (2*Real.pi) • circleAverage f x r := by
  have hp : Periodic (fun θ => f (circleMap x r θ)) (2*Real.pi) :=
    fun θ => congrArg f (periodic_circleMap x r θ)
  have he := hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add] at he
  have he' : (∫ θ in -Real.pi..Real.pi, f (circleMap x r θ)) =
      ∫ θ in 0..2*Real.pi, f (circleMap x r θ) := by
    convert he.symm using 1
    ring_nf
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),he',circleAverage_def]
  rw [smul_smul,mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),one_smul]

lemma polar_bump_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} (hf : Continuous f) (x : ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • (radialBump R (Complex.polarCoord.symm p) •
      f (x-Complex.polarCoord.symm p))) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  apply IntegrableOn.of_inter_support (measurableSet_Ioi.prod measurableSet_Ioo)
  have hc : Continuous (fun p : ℝ × ℝ => p.1 • (radialBump R (Complex.polarCoord.symm p) •
      f (x-Complex.polarCoord.symm p))) :=
    continuous_fst.smul (((radialBump_contDiff R).continuous.comp polar_continuous).smul
      (hf.comp (continuous_const.sub polar_continuous)))
  apply (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  refine ⟨⟨hp.1.1.le,?_⟩,⟨hp.1.2.1.le,hp.1.2.2.le⟩⟩
  by_contra hh
  have hz : radialBump R (Complex.polarCoord.symm p) = 0 := by
    apply radialBump_zero hR.le
    rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1.1]
    exact (lt_of_not_ge hh).le
  exact hp.2 (by simp only [hz,zero_smul,smul_zero])


theorem radial_average {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} (hf : Continuous f) (x : ℂ)
    (hh : InnerProductSpace.HarmonicOnNhd f (ball x R)) :
    (∫ z, radialBump R z • f (x-z)) = (∫ z, radialBump R z) • f x := by
  rw [← integral_smul_const]
  rw [← Complex.integral_comp_polarCoord_symm, ← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump R (Complex.polarCoord.symm p) • f (x-Complex.polarCoord.symm p))) =
    ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump R (Complex.polarCoord.symm p) • f x)
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hR hf x),
    setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hR (f := fun _ => f x) continuous_const (0:ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp_rw [radialBump_polar,polar_circle,integral_smul]
  by_cases hrR : r < R
  · have hh' : InnerProductSpace.HarmonicOnNhd f (closedBall x |(-r)|) := by
      rw [abs_neg,abs_of_pos hr]
      exact hh.mono (closedBall_subset_ball hrR)
    rw [angle_integral,hh'.circleAverage_eq]
    simp only [integral_const]
    rw [Measure.real,Measure.restrict_apply_univ,volume_Ioo,ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi- -Real.pi)]
    congr 2
    ring_nf
  · have hzero : expNegInvGlue (R^2-r^2) = 0 := by
      apply expNegInvGlue.zero_of_nonpos
      have hr' : R ≤ r := le_of_not_gt hrR
      nlinarith
    simp only [hzero,zero_smul,smul_zero]

end StrictHotSpots.Weyl
end HarmonicRadialRegularityBaseLayer

section ConvolutionShuffleRegularityBaseLayer
open Set MeasureTheory Metric _root_.Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Weyl
open Helmholtz

lemma convolution_assoc_scalar {u : ℂ → ℂ} {g k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hk : Continuous k) (hck : HasCompactSupport k) :
    (u ⋆[smulFlip] g) ⋆[smulFlip] k = u ⋆[smulFlip] (g ⋆[mul ℝ ℝ] k) := by
  funext x
  apply convolution_assoc smulFlip smulFlip smulFlip (mul ℝ ℝ)
    (fun z a b => by simp only [smulFlip,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',smul_smul]; rw [mul_comm])
    hu.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hcg.convolutionExists_right _ hu hg)
  · exact Eventually.of_forall (hck.norm.convolutionExists_right _ hg.norm.locallyIntegrable hk.norm)
  · exact (hcg.norm.convolution (mul ℝ ℝ) hck.norm).convolutionExists_right _ (fun x => (hu x).norm)
      (hck.norm.continuous_convolution_right _ hg.norm.locallyIntegrable hk.norm) x

lemma convolution_shuffle {u : ℂ → ℂ} {g k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hk : Continuous k) (hck : HasCompactSupport k) :
    (u ⋆[smulFlip] g) ⋆[smulFlip] k = (u ⋆[smulFlip] k) ⋆[smulFlip] g := by
  rw [convolution_assoc_scalar hu hg hcg hk hck,convolution_assoc_scalar hu hk hck hg hcg]
  have hh : (mul ℝ ℝ).flip = mul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
    exact mul_comm y x
  rw [← convolution_flip (L := mul ℝ ℝ),hh]

end StrictHotSpots.Weyl
end ConvolutionShuffleRegularityBaseLayer

section WeakWeylRegularityBaseLayer
open Set MeasureTheory Metric _root_.Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Weyl
open Helmholtz



theorem local_representative {u : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hu : LocallyIntegrable u volume) (hR : 0 < R) (hpde : WeakEquation (ball a R) 0 u) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      ∀ᵐ x ∂volume, x ∈ ball a (R/4) → f x = u x := by
  let φ := radialBump (R/4)
  let c : ℝ := ∫ z, φ z
  have hc : 0 < c := radialBump_integral_pos (by positivity)
  have hφ : ContDiff ℝ ∞ φ := radialBump_contDiff _
  have hcφ : HasCompactSupport φ := radialBump_compact (by positivity)
  let v := u ⋆[smulFlip] φ
  have hv : ContDiff ℝ ∞ v := hcφ.contDiff_convolution_right _ hu hφ
  refine ⟨fun x => c⁻¹ • v x,?_,?_⟩
  · simpa only [Pi.smul_apply] using! (contDiff_const (c := c⁻¹)).smul hv
  filter_upwards [smoothen_tendsto hu,smoothen_tendsto hv.continuous.locallyIntegrable] with x hx hxv
  intro hxa
  have he : ∀ᶠ n in atTop, smoothen v n x = c • smoothen u n x := by
    filter_upwards [(tendsto_order.1 mollifier_radius_tendsto).2 (R/2) (by positivity)] with n hn
    have hh : InnerProductSpace.HarmonicOnNhd (smoothen u n) (ball x (R/4)) := by
      intro y hy
      have hym : y ∈ ball a (R-(mollifier n).rOut) := by
        rw [mem_ball] at hy hxa ⊢
        have ht := dist_triangle y x a
        linarith
      refine ⟨((smoothen_contDiff hu n).of_le (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt,?_⟩
      filter_upwards [isOpen_ball.mem_nhds hym] with z hz
      simpa only [neg_zero,zero_smul,Pi.zero_apply] using smoothen_PDE hu hpde n hz
    calc
      smoothen v n x = (smoothen u n ⋆[smulFlip] φ) x :=
        (congrFun (convolution_shuffle hu (mollifier n).continuous_normed
          (mollifier n).hasCompactSupport_normed hφ.continuous hcφ) x).symm
      _ = c • smoothen u n x := by
        rw [← convolution_flip]
        exact radial_average (by positivity) (smoothen_contDiff hu n).continuous x hh
  have ht : Tendsto (fun n => smoothen v n x) atTop (𝓝 (c • u x)) :=
    (hx.const_smul c).congr' (he.mono (fun _ h => h.symm))
  have hvx : v x = c • u x := tendsto_nhds_unique hxv ht
  rw [hvx,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]



theorem representative {u : ℂ → ℂ} {Ω : Set ℂ} (ho : IsOpen Ω)
    (hu : LocallyIntegrable u volume) (hpde : WeakEquation Ω 0 u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume, x ∈ Ω → f x = u x := by
  classical
  have hball (x : Ω) : ∃ R : ℝ, 0 < R ∧ ball (x:ℂ) R ⊆ Ω :=
    Metric.isOpen_iff.mp ho x x.property
  choose R hR hRΩ using hball
  choose f hf hfu using fun x : Ω => local_representative hu (hR x) (hpde.mono (hRΩ x))
  have hsmall (x : Ω) : ball (x:ℂ) (R x/4) ⊆ Ω :=
    (ball_subset_ball (by linarith [hR x])).trans (hRΩ x)
  have heq (x y : Ω) : EqOn (f x) (f y) (ball (x:ℂ) (R x/4) ∩ ball (y:ℂ) (R y/4)) := by
    apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ (isOpen_ball.inter isOpen_ball)
      (hf x).continuous.continuousOn (hf y).continuous.continuousOn
    apply (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mpr
    filter_upwards [hfu x,hfu y] with z hx hy
    intro hz
    exact (hx hz.1).trans (hy hz.2).symm
  let g : ℂ → ℂ := fun x => if hx : x ∈ Ω then f ⟨x,hx⟩ x else 0
  have hgf (x : Ω) {z : ℂ} (hz : z ∈ ball (x:ℂ) (R x/4)) : g z = f x z := by
    have hzΩ := hsmall x hz
    dsimp only [g]
    rw [dite_eq_left hzΩ]
    exact heq ⟨z,hzΩ⟩ x ⟨mem_ball_self (by linarith [hR ⟨z,hzΩ⟩]),hz⟩
  refine ⟨g,?_,?_⟩
  · intro x hx
    let x' : Ω := ⟨x,hx⟩
    have he : g =ᶠ[𝓝 x] f x' := by
      filter_upwards [ball_mem_nhds x (by linarith [hR x'] : 0 < R x'/4)] with z hz
      exact hgf x' hz
    exact ((hf x').contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  · obtain ⟨T,hT,hcover⟩ := (IsLindelof.of_coe (s := Ω)).elim_nhds_subcover'
      (fun x hx => ball x (R ⟨x,hx⟩/4)) (fun x hx => ball_mem_nhds x (by linarith [hR ⟨x,hx⟩]))
    have ha : ∀ᵐ z ∂volume, ∀ x ∈ T, z ∈ ball (x:ℂ) (R x/4) → f x z = u z :=
      (eventually_countable_ball hT).mpr (fun x _ => hfu x)
    filter_upwards [ha] with z hz
    intro hzΩ
    obtain ⟨x,hx,hzB⟩ := mem_iUnion₂.mp (hcover hzΩ)
    exact (hgf x hzB).trans (hz x hx hzB)

end StrictHotSpots.Weyl
end WeakWeylRegularityBaseLayer




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

lemma expand (x : Plane) : c 0 x • e 0 + c 1 x • e 1 = x := by
  simpa only [Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply, real_inner_comm] using planeBasis.sum_repr x
lemma basis_inner (i j : Fin 2) : inner ℝ (e i) (e j) = if i=j then 1 else 0 :=
  planeBasis.inner_eq_ite i j
lemma inner_two (x y : Plane) : inner ℝ x y = c 0 x*c 0 y+c 1 x*c 1 y := by
  simpa only [Fin.sum_univ_two,real_inner_comm (e 0) y,real_inner_comm (e 1) y] using
    (planeBasis.sum_inner_mul_inner x y).symm

lemma rot_apply (x : Plane) : rot x = c 0 x • e 1-c 1 x • e 0 := by
  simp only [rot,sub_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,real_inner_comm]
lemma c_rot (x : Plane) : c 0 (rot x) = -c 1 x ∧ c 1 (rot x) = c 0 x := by
  rw [rot_apply]
  simp only [c,inner_sub_left,inner_smul_left,conj_trivial,basis_inner]
  norm_num
lemma rot_inner (x y : Plane) : inner ℝ (rot x) (rot y) = inner ℝ x y := by
  rw [inner_two,inner_two,(c_rot x).1,(c_rot x).2,(c_rot y).1,(c_rot y).2]
  ring
lemma D_smooth {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) : ContDiff ℝ ∞ (D i φ) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const
lemma D_compact {φ : Plane → ℝ} (hc : HasCompactSupport φ) (i : Fin 2) : HasCompactSupport (D i φ) :=
  hc.fderiv_apply ℝ (e i)
lemma D_support (φ : Plane → ℝ) (i : Fin 2) : tsupport (D i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (e i)
lemma gradient_c (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : c i (gradient φ x) = D i φ x :=
  inner_gradient_left
lemma D_D {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 2) (x : Plane) :
    D i (D j φ) x = D j (D i φ) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ φ)).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ φ y (e j)) x (e i) =
    fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e j)
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) _ _

lemma laplace_two {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Plane) :
    Δ φ x = D 0 (D 0 φ) x + D 1 (D 1 φ) x := by
  simpa only [Fin.sum_univ_two] using
    laplacian_eq_sum_directional isOpen_univ hφ.contDiffOn (mem_univ x)

lemma inner_gradient (Z : Plane) (φ : Plane → ℝ) (x : Plane) :
    inner ℝ Z (gradient φ x) = c 0 Z*D 0 φ x+c 1 Z*D 1 φ x := by
  rw [inner_two,gradient_c,gradient_c]
lemma inner_rot_gradient (Z : Plane) (φ : Plane → ℝ) (x : Plane) :
    inner ℝ Z (rot (gradient φ x)) = c 1 Z*D 0 φ x-c 0 Z*D 1 φ x := by
  rw [inner_two,(c_rot _).1,(c_rot _).2,gradient_c,gradient_c]
  ring
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer


section PlaneWeakWeylInteriorSupportLayer


open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Weyl

private lemma complexExtension_integral (Ω : Set Plane) (hΩ : MeasurableSet Ω)
    (u : Plane → ℝ) (ψ : ℂ → ℝ) :
    (∫ z, ψ z • complexExtension Ω u z) =
      Complex.ofReal (∫ x in Ω, u x * ψ (coord.symm x)) := by
  have he : (fun z => ψ z • complexExtension Ω u z) =
      (fun z => ((Ω.indicator (fun x => u x * ψ (coord.symm x))) (coord z) : ℂ)) := by
    funext z
    by_cases hz : coord z ∈ Ω
    · simp [complexExtension,indicator_of_mem hz,Complex.real_smul,mul_comm]
    · simp [complexExtension,indicator_of_notMem hz]
  rw [he,integral_complex_ofReal,
    coord.measurePreserving.integral_comp coord.toHomeomorph.measurableEmbedding,
    integral_indicator hΩ]

private lemma complexExtension_integrable {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hu : IntegrableOn u Ω) :
    Integrable (complexExtension Ω u) volume := by
  have hi := (integrable_indicator_iff hΩ).mpr hu
  have hj := coord.measurePreserving.integrable_comp_of_integrable hi
  exact Complex.ofRealCLM.integrable_comp hj

private lemma complexExtension_weak {Ω : Set Plane} {μ : ℝ} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hp : PlaneWeakEquation Ω μ u) :
    Helmholtz.WeakEquation (coord ⁻¹' Ω) μ (complexExtension Ω u) := by
  intro φ hφ hc hs
  have ht : ContDiff ℝ ∞ (φ ∘ coord.symm) :=
    hφ.comp coord.symm.toContinuousLinearEquiv.contDiff
  have htc : HasCompactSupport (φ ∘ coord.symm) := hc.comp_homeomorph coord.symm.toHomeomorph
  have hts : tsupport (φ ∘ coord.symm) ⊆ Ω := by
    change tsupport (φ ∘ coord.symm.toHomeomorph) ⊆ Ω
    rw [tsupport_comp_eq_preimage φ coord.symm.toHomeomorph]
    intro x hx
    have h : coord (coord.symm x) ∈ Ω := hs hx
    simpa only [coord.apply_symm_apply] using h
  have h := hp _ ht htc hts
  simp only [laplacian_comp_linearIsometryEquiv,Function.comp_apply] at h
  rw [complexExtension_integral Ω hΩ u (Δ φ),complexExtension_integral Ω hΩ u φ,h]
  simp



theorem plane_representative {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : IntegrableOn u Ω) (hp : PlaneWeakEquation Ω 0 u) :
    ∃ f : Plane → ℝ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume.restrict Ω, f x = u x := by
  obtain ⟨f,hf,hfu⟩ := representative (ho.preimage coord.continuous)
    (complexExtension_integrable ho.measurableSet hu).locallyIntegrable
    (complexExtension_weak ho.measurableSet hp)
  refine ⟨fun x => (f (coord.symm x)).re,?_,?_⟩
  · exact Complex.reCLM.contDiff.comp_contDiffOn (hf.comp
      coord.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => by simpa only [mem_preimage,coord.apply_symm_apply] using hx))
  · apply (ae_restrict_iff' ho.measurableSet).mpr
    filter_upwards [coord.symm.measurePreserving.quasiMeasurePreserving.ae hfu] with x hx
    intro hxm
    have he := hx (show coord.symm x ∈ coord ⁻¹' Ω by simpa using hxm)
    simpa only [complexExtension,coord.apply_symm_apply,indicator_of_mem hxm,Complex.ofReal_re] using congrArg Complex.re he

end StrictHotSpots.Weyl

end PlaneWeakWeylInteriorSupportLayer


section PrimitiveAtlasInteriorSupportLayer




open Set Filter Bundle
open scoped Topology
namespace StrictHotSpots.Primitives

namespace Atlas
variable {X ι : Type*} [TopologicalSpace X] (A : Atlas X ι)



theorem exists_locally_potential [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) : ∃ g : X → ℝ, ∀ x : X, ∃ c : ℝ,
      ∀ᶠ y in 𝓝 x, g y = A.potential (A.idx x) y+c := by
  let Z := A.core
  have hcov : IsCoveringMap Z.proj := IsFiberBundle.isCoveringMap (fun x =>
    ⟨Z.localTriv (Z.indexAt x),Z.mem_baseSet_at x⟩)
  let e₀ : Z.TotalSpace := ⟨x₀,⟨0⟩⟩
  obtain ⟨F,⟨_,hF⟩,_⟩ := hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ rfl
  have hproj (x : X) : (F x).1 = x := congrFun hF x
  let g : X → ℝ := fun x => (F x).2.val+A.potential (A.idx (F x).1) (F x).1
  refine ⟨g,fun x => ?_⟩
  let i := A.idx x
  let c : X → DiscreteReal := fun y => (Z.localTriv i (F y)).2
  have hc : ContinuousAt c x := by
    apply ContinuousAt.snd
    have hm : F x ∈ (Z.localTriv i).source := by
      change Z.proj (F x) ∈ Z.baseSet i
      rw [show Z.proj (F x) = x from hproj x]
      exact A.mem_U x
    exact ((Z.localTriv i).continuousAt hm).comp F.continuous.continuousAt
  have he (y : X) : g y = A.potential i y+(c y).val := by
    dsimp only [g,c]
    rw [Z.localTriv_apply]
    change (F y).2.val+A.potential (A.idx (F y).1) (F y).1 =
      A.potential i y+((F y).2.val+A.potential (A.idx (F y).1) (F y).1-A.potential i (F y).1)
    rw [hproj y]
    ring
  have hn : ∀ᶠ y in 𝓝 x, c y = c x := by
    have hh : {c x} ∈ 𝓝 (c x) := by simp
    exact hc hh
  refine ⟨(c x).val,?_⟩
  filter_upwards [hn] with y hy
  rw [he y,hy]

end Atlas
end StrictHotSpots.Primitives

end PrimitiveAtlasInteriorSupportLayer


section SimplyConnectedPoincareInteriorSupportLayer

open Set Filter Metric
open scoped Topology
namespace StrictHotSpots.Primitives



theorem exists_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    {ω : E → E →L[ℝ] ℝ} (hω : DifferentiableOn ℝ ω Ω)
    (hd : ∀ a ∈ Ω, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f : E → ℝ, ∀ a ∈ Ω, HasFDerivAt f (ω a) a := by
  classical
  let : SimplyConnectedSpace Ω := hs
  let : LocallyPathConnectedSpace Ω := ho.locallyPathConnectedSpace
  have hb (p : Ω) : ∃ r : ℝ, 0 < r ∧ ball (p : E) r ⊆ Ω :=
    Metric.isOpen_iff.mp ho p p.property
  choose r hr hrΩ using hb
  have hprim (p : Ω) : ∃ F : E → ℝ, ∀ a ∈ ball (p : E) (r p), HasFDerivAt F (ω a) a :=
    (convex_ball (p : E) (r p)).exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_ball
      (hω.mono (hrΩ p)) (fun a ha => hd a (hrΩ p ha))
  choose F hF using hprim
  let A : Atlas Ω Ω := {
    U := fun p => Subtype.val ⁻¹' ball (p : E) (r p)
    isOpen_U := fun p => isOpen_ball.preimage continuous_subtype_val
    idx := id
    mem_U := fun p => mem_ball_self (hr p)
    potential := fun p x => F p x
    constant_overlap := by
      intro p q x y hx hy
      let U := ball (p : E) (r p) ∩ ball (q : E) (r q)
      have hu : IsOpen U := isOpen_ball.inter isOpen_ball
      have hh (z : E) (hz : z ∈ U) : HasFDerivAt (fun z => F p z-F q z) (0 : E →L[ℝ] ℝ) z := by
        simpa only [sub_self,Pi.sub_apply] using! (hF p z hz.1).sub (hF q z hz.2)
      apply ((convex_ball (p : E) (r p)).inter (convex_ball (q : E) (r q))).is_const_of_fderivWithin_eq_zero
          (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
          (fun z hz => (hh z hz).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffOn z hz)) hx hy }
  obtain ⟨x₀⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨g,hg⟩ := A.exists_locally_potential x₀
  let f : E → ℝ := fun x => if hx : x ∈ Ω then g ⟨x,hx⟩ else 0
  refine ⟨f,fun a ha => ?_⟩
  let a' : Ω := ⟨a,ha⟩
  obtain ⟨c,hc⟩ := hg a'
  have he : ∀ᶠ x in 𝓝 a, f x = F a' x+c := by
    have hsub : ∀ᶠ x : Ω in 𝓝 a', g x = F a' x+c := hc
    rw [nhds_subtype_eq_comap] at hsub
    obtain ⟨s,hsn,hss⟩ := Filter.mem_comap.mp hsub
    filter_upwards [hsn,ho.mem_nhds ha] with x hx hxΩ
    have hm := hss (show (⟨x,hxΩ⟩ : Ω) ∈ Subtype.val ⁻¹' s from hx)
    change g ⟨x,hxΩ⟩ = F a' x+c at hm
    simpa only [f,dite_eq_left hxΩ] using hm
  exact ((hF a' a (mem_ball_self (hr a'))).add_const c).congr_of_eventuallyEq he

end StrictHotSpots.Primitives

end SimplyConnectedPoincareInteriorSupportLayer


section SmoothTruncationInteriorSupportLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Truncation

lemma smooth (n : ℕ) : ContDiff ℝ ∞ (trunc n) := by
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const _))
lemma derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (trunc n) (1 / (1 + (t/((n:ℝ)+1))^2)) t := by
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  convert (((hasDerivAt_id t).div_const ((n:ℝ)+1)).arctan.const_mul ((n:ℝ)+1)) using 1 <;> try rfl
  simp only [id_eq]
  field_simp
lemma deriv_bound (n : ℕ) (t : ℝ) : ‖deriv (trunc n) t‖ ≤ 1 := by
  rw [(derivative n t).deriv, Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (t/((n:ℝ)+1))])
lemma norm_le (n : ℕ) (t : ℝ) : ‖trunc n t‖ ≤ ‖t‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := trunc n) (s := univ)
    (fun x _ => (derivative n x).differentiableAt)
    (fun x _ => deriv_bound n x) convex_univ (mem_univ t) (mem_univ (0:ℝ))
  simpa [trunc] using h
lemma bounded (n : ℕ) (t : ℝ) : ‖trunc n t‖ ≤ ((n:ℝ)+1)*(Real.pi/2) := by
  rw [trunc,norm_mul,Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩
lemma tends (t : ℝ) : Tendsto (fun n => trunc n t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst t
    simp [trunc]
  have ht0 : Tendsto (fun n : ℕ => t/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (by simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop))
  have htne : Tendsto (fun n : ℕ => t/((n:ℝ)+1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0,Eventually.of_forall (fun n => by simpa using div_ne_zero ht (by positivity : (n:ℝ)+1 ≠ 0))⟩
  have hh := ((Real.hasDerivAt_arctan 0).tendsto_slope_zero.comp htne).const_mul t
  convert hh using 1
  · ext n
    simp only [Function.comp_apply,zero_add, Real.arctan_zero,sub_zero,smul_eq_mul,trunc]
    field_simp
  · simp
end StrictHotSpots.Truncation

end SmoothTruncationInteriorSupportLayer


section AnchoredEstimateInteriorSupportLayer

open Set MeasureTheory Filter
namespace StrictHotSpots


lemma anchored_l2_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {B : Set α} (_hB : MeasurableSet B) (hβ : 0 < (μ B).toReal)
    {f : α → ℝ} (hf : MemLp f 2 μ) {m M D : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict B, ‖f x‖ ≤ M)
    (hv : (∫ x, (f x-m)^2 ∂μ) ≤ D) :
    (∫ x, (f x)^2 ∂μ) ≤ 2*D + 2*((2*D + 2*M^2*(μ B).toReal)/(μ B).toReal)*(μ univ).toReal := by
  have hfi : Integrable (fun x => (f x)^2) μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hfm : MemLp (fun x => f x-m) 2 μ := hf.sub (memLp_const m)
  have hvI : Integrable (fun x => (f x-m)^2) μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hfm
  have hvB : (∫ x in B, (f x-m)^2 ∂μ) ≤ D :=
    (setIntegral_le_integral hvI (Eventually.of_forall (fun x => sq_nonneg _))).trans hv
  have hmB : m^2*(μ B).toReal ≤ 2*D + 2*M^2*(μ B).toReal := by
    have he : (∫ _ in B, m^2 ∂μ) ≤ ∫ x in B, 2*(f x-m)^2 + 2*M^2 ∂μ := by
      apply integral_mono_ae (integrable_const _) ((hvI.restrict.const_mul 2).add (integrable_const _))
      filter_upwards [ha] with x hx
      have hM := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
      simp only [Real.norm_eq_abs,sq_abs] at hM
      change m^2 ≤ 2*(f x-m)^2+2*M^2
      nlinarith [sq_nonneg (2*f x-m)]
    rw [integral_add (hvI.restrict.const_mul 2) (integrable_const _),integral_const_mul] at he
    simp only [integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at he
    nlinarith
  have hm : m^2 ≤ (2*D + 2*M^2*(μ B).toReal)/(μ B).toReal :=
    (le_div_iff₀ hβ).mpr hmB
  have he : (∫ x, (f x)^2 ∂μ) ≤ ∫ x, 2*(f x-m)^2+2*m^2 ∂μ := by
    apply integral_mono_ae hfi ((hvI.const_mul 2).add (integrable_const _))
    exact Eventually.of_forall fun x => by
      change (f x)^2 ≤ 2*(f x-m)^2+2*m^2
      nlinarith [sq_nonneg (f x-2*m)]
  rw [integral_add (hvI.const_mul 2) (integrable_const _),integral_const_mul] at he
  simp only [integral_const,smul_eq_mul,measureReal_def] at he
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hv (by norm_num))
    (by nlinarith [mul_le_mul_of_nonneg_right hm (ENNReal.toReal_nonneg (a := μ univ))]))
end StrictHotSpots

end AnchoredEstimateInteriorSupportLayer


section FiniteEnergyPrimitiveInteriorSupportLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots



theorem finiteEnergy_hasH1Gradient {Ω : Set Plane} (ho : IsOpen Ω)
    (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {r : Plane → ℝ}
    (hr : ContDiffOn ℝ ∞ r Ω) (hg : MemLp (gradient r) 2 (volume.restrict Ω)) :
    HasH1Gradient Ω r (gradient r) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hvol : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (ne_of_gt (ho.measure_pos volume hne)) hb.measure_lt_top.ne
  have hrm : AEStronglyMeasurable r (volume.restrict Ω) := hr.continuousOn.aestronglyMeasurable ho.measurableSet
  let F (n : ℕ) (x : Plane) := Truncation.trunc n (r x)
  have hF (n : ℕ) : ContDiffOn ℝ ∞ (F n) Ω := (Truncation.smooth n).comp_contDiffOn hr
  have hmF (n : ℕ) : MemLp (F n) 2 (volume.restrict Ω) := by
    apply (memLp_const (((n:ℝ)+1)*(Real.pi/2))).mono
      ((hF n).continuousOn.aestronglyMeasurable ho.measurableSet)
    exact Eventually.of_forall fun x => (Truncation.bounded n (r x)).trans (le_abs_self _)
  have hgrad (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
      gradient (F n) x = deriv (Truncation.trunc n) (r x) • gradient r x := by
    apply (InnerProductSpace.toDual ℝ Plane).injective
    simp only [gradient,map_smul,LinearIsometryEquiv.apply_symm_apply]
    have hdx := ((hr.contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (((Truncation.smooth n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x hdx).fderiv
  have hgradle (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖gradient (F n) x‖ ≤ ‖gradient r x‖ := by
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    rw [hgrad n hx,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Truncation.deriv_bound n (r x))
  have hmG (n : ℕ) : MemLp (gradient (F n)) 2 (volume.restrict Ω) := by
    apply hg.mono _ (hgradle n)
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (F n)) Ω := (hF n).fderiv_of_isOpen ho (by simp)
    have hc : ContinuousOn (gradient (F n)) Ω :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
        hd.continuousOn
    exact hc.aestronglyMeasurable ho.measurableSet
  have hH (n : ℕ) : HasH1Gradient Ω (F n) (gradient (F n)) :=
    HasH1Gradient.of_contDiffOn ho (hF n) (hmF n) (hmG n)
  let m (n : ℕ) := (∫ x in Ω, F n x)/(volume Ω).toReal
  let G := ∫ x in Ω, ‖gradient r x‖^2
  have hm (n : ℕ) : (∫ x in Ω, F n x-m n) = 0 := by
    rw [integral_sub ((hmF n).integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
    change (∫ x in Ω, F n x)-(volume Ω).toReal*m n = 0
    dsimp [m]
    field_simp
    ring
  have hvar (n : ℕ) : (∫ x in Ω, (F n x-m n)^2) ≤ G/firstPositiveNeumannValue Ω := by
    have hH' : HasH1Gradient Ω (fun x => F n x-m n) (gradient (F n)) := by
      simpa only [sub_zero] using! (hH n).sub (HasH1Gradient.const hb (m n))
    have he := rayleigh_inequality_all hH' (hm n)
    have he' : (∫ x in Ω, ‖gradient (F n) x‖^2) ≤ G := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm (hmG n).aestronglyMeasurable).mp (hmG n))
        ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
      exact (hgradle n).mono fun x hx => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
    exact (le_div_iff₀ hμ).mpr (by nlinarith)
  obtain ⟨a,ha⟩ := hne
  have heΩ : ∀ᶠ x in 𝓝 a, x ∈ Ω := ho.mem_nhds ha
  have he : ∀ᶠ x in 𝓝 a, x ∈ Ω ∧ ‖r x‖ < ‖r a‖+1 :=
    heΩ.and (((hr.continuousOn a ha).continuousAt (ho.mem_nhds ha)).norm.eventually
      (gt_mem_nhds (by linarith : ‖r a‖ < ‖r a‖+1)))
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp he
  have hBΩ : ball a ε ⊆ Ω := fun x hx => (hεs hx).1
  have hβ : 0 < ((volume.restrict Ω) (ball a ε)).toReal := by
    rw [Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hBΩ]
    exact ENNReal.toReal_pos (ne_of_gt (isOpen_ball.measure_pos volume (nonempty_ball.mpr hε)))
      (measure_ball_lt_top.ne)
  let C := 2*(G/firstPositiveNeumannValue Ω) +
    2*((2*(G/firstPositiveNeumannValue Ω)+2*(‖r a‖+1)^2*((volume.restrict Ω) (ball a ε)).toReal)/
      ((volume.restrict Ω) (ball a ε)).toReal)*((volume.restrict Ω) univ).toReal
  have hbound (n : ℕ) : (∫ x in Ω, (F n x)^2) ≤ C := by
    apply anchored_l2_bound measurableSet_ball hβ (hmF n) (m := m n)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (Truncation.norm_le n (r x)).trans (hεs hx).2.le
    · exact hvar n
  have hLP (n : ℕ) : eLpNorm (F n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal (Real.sqrt (max C 0)) := by
    rw [(hmF n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
    rw [← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ((hbound n).trans (le_max_left C 0)))
  have hrL : MemLp r 2 (volume.restrict Ω) := by
    exact ⟨hrm, (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hLP)
      (fun n => (hmF n).aestronglyMeasurable)
      (Eventually.of_forall (fun x => Truncation.tends (r x)))).trans_lt
      ENNReal.ofReal_lt_top⟩
  exact HasH1Gradient.of_contDiffOn ho hr hrL hg
end StrictHotSpots

end FiniteEnergyPrimitiveInteriorSupportLayer


section SmoothClosedPotentialInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots



theorem closed_finiteEnergy_potential {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a y x) :
    ∃ r : Plane → ℝ, ContDiffOn ℝ ∞ r Ω ∧ HasH1Gradient Ω r Z := by
  have hw : ContDiffOn ℝ ∞ (fun a => innerSL ℝ (Z a)) Ω :=
    (innerSL ℝ (E := Plane)).contDiff.comp_contDiffOn hZ
  obtain ⟨r,hr⟩ := Primitives.exists_primitive ho hs (hw.differentiableOn (by simp)) hd
  have he : EqOn (fderiv ℝ r) (fun a => innerSL ℝ (Z a)) Ω := fun a ha => (hr a ha).fderiv
  have hrs : ContDiffOn ℝ ∞ r Ω := by
    rw [contDiffOn_infty_iff_fderiv_of_isOpen ho]
    exact ⟨fun a ha => (hr a ha).differentiableAt.differentiableWithinAt, hw.congr he⟩
  have heg : ∀ a ∈ Ω, gradient r a = Z a := by
    intro a ha
    apply (InnerProductSpace.toDual ℝ Plane).injective
    change (InnerProductSpace.toDual ℝ Plane) ((InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ r a)) = _
    rw [LinearIsometryEquiv.apply_symm_apply,he ha]
    ext y
    rfl
  have hae : gradient r =ᵐ[volume.restrict Ω] Z :=
    (ae_restrict_mem ho.measurableSet).mono fun a ha => heg a ha
  have hgr : MemLp (gradient r) 2 (volume.restrict Ω) := (memLp_congr_ae hae).mpr hm
  have hne : Ω.Nonempty := by
    let : SimplyConnectedSpace Ω := hs
    obtain ⟨x⟩ := (inferInstance : Nonempty Ω)
    exact ⟨x,x.property⟩
  refine ⟨r,hrs,?_⟩
  exact (finiteEnergy_hasH1Gradient ho hne hb hμ hrs hgr).congr (Filter.Eventually.of_forall (fun _ => rfl)) hae



theorem closed_orthogonal_gradient_zero {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a y x)
    (hz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (Z x) (g x)) = 0) :
    ∀ x ∈ Ω, Z x = 0 := by
  obtain ⟨r,_,hr⟩ := closed_finiteEnergy_potential ho hs hb hμ hZ hm hd
  have he := hz r Z hr
  simp only [real_inner_self_eq_norm_sq] at he
  have hI := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hae : ∀ᵐ x ∂volume.restrict Ω, ‖Z x‖^2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg ‖Z x‖)) hI).mp he
  have hae' : Z =ᵐ[volume.restrict Ω] 0 := hae.mono fun x hx => by simpa using hx
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' ho hZ.continuousOn continuousOn_const
end StrictHotSpots

end SmoothClosedPotentialInteriorSupportLayer


section WeakHodgeRegularityInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

lemma weak_harmonic_coordinates {Ω : Set Plane} (ho : IsOpen Ω)
    {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : WeakDivZero Ω Z) (hc : WeakCurlZero Ω Z) (i : Fin 2) :
    PlaneWeakEquation Ω 0 (fun x => c i (Z x)) := by
  intro φ hφ hk hs
  have hI (j : Fin 2) : IntegrableOn (fun x => inner ℝ (Z x) (gradient (D j φ) x)) Ω :=
    integrable_inner_of_memLp hm (HasH1Gradient.test ho (D_smooth hφ j) (D_compact hk j)).2.1
  have hJ (j : Fin 2) : IntegrableOn (fun x => inner ℝ (Z x) (rot (gradient (D j φ) x))) Ω :=
    integrable_inner_of_memLp hm (rot.comp_memLp' (HasH1Gradient.test ho (D_smooth hφ j) (D_compact hk j)).2.1)
  have hD (j : Fin 2) := hd _ (D_smooth hφ j) (D_compact hk j) ((D_support φ j).trans hs)
  have hC (j : Fin 2) := hc _ (D_smooth hφ j) (D_compact hk j) ((D_support φ j).trans hs)
  have he0 (x : Plane) : c 0 (Z x)*Δ φ x =
      inner ℝ (Z x) (gradient (D 0 φ) x) - inner ℝ (Z x) (rot (gradient (D 1 φ) x)) := by
    rw [laplace_two hφ,inner_gradient,inner_rot_gradient,D_D hφ 1 0]
    ring
  have he1 (x : Plane) : c 1 (Z x)*Δ φ x =
      inner ℝ (Z x) (gradient (D 1 φ) x) + inner ℝ (Z x) (rot (gradient (D 0 φ) x)) := by
    rw [laplace_two hφ,inner_gradient,inner_rot_gradient,D_D hφ 1 0]
    ring
  fin_cases i
  · change (∫ x in Ω, c 0 (Z x) * Δ φ x) = _
    simp_rw [he0]
    rw [integral_sub (hI 0) (hJ 1),hD 0,hC 1]
    simp
  · change (∫ x in Ω, c 1 (Z x) * Δ φ x) = _
    simp_rw [he1]
    rw [integral_add (hI 1) (hJ 0),hD 1,hC 0]
    simp



theorem weak_divCurl_smooth {Ω : Set Plane} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : WeakDivZero Ω Z) (hc : WeakCurlZero Ω Z) :
    ∃ W : Plane → Plane, ContDiffOn ℝ ∞ W Ω ∧ W =ᵐ[volume.restrict Ω] Z := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hh (i : Fin 2) := Weyl.plane_representative ho
    ((hm.inner_const (e i)).integrable (by norm_num)) (weak_harmonic_coordinates ho hm hd hc i)
  choose f hf he using hh
  refine ⟨fun x => f 0 x • e 0+f 1 x • e 1,(hf 0).smul contDiffOn_const |>.add ((hf 1).smul contDiffOn_const),?_⟩
  filter_upwards [he 0,he 1] with x hx0 hx1
  rw [hx0,hx1,expand]

lemma smooth_curl_zero {Ω : Set Plane} (ho : IsOpen Ω)
    {W : Plane → Plane} (hW : ContDiffOn ℝ ∞ W Ω) (hc : WeakCurlZero Ω W) :
    ∀ x ∈ Ω, D 0 (fun y => c 1 (W y)) x = D 1 (fun y => c 0 (W y)) x := by
  let a : Plane → ℝ := fun x => c 0 (W x)
  let b : Plane → ℝ := fun x => c 1 (W x)
  have ha : ContDiffOn ℝ ∞ a Ω := hW.inner ℝ contDiffOn_const
  have hb : ContDiffOn ℝ ∞ b Ω := hW.inner ℝ contDiffOn_const
  have hda := directionalDerivative_contDiffOn ho ha (e 1)
  have hdb := directionalDerivative_contDiffOn ho hb (e 0)
  have hcont : ContinuousOn (fun x => D 0 b x-D 1 a x) Ω := hdb.continuousOn.sub hda.continuousOn
  have hz := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn ho.measurableSet (μ := volume)) ?_
  · have he : (fun x => D 0 b x-D 1 a x) =ᵐ[volume.restrict Ω] 0 := (ae_restrict_iff' ho.measurableSet).mpr hz
    have hh := MeasureTheory.Measure.eqOn_open_of_ae_eq he ho hcont continuousOn_const
    intro x hx
    exact sub_eq_zero.mp (hh hx)
  · intro φ hφ hk hs
    have hi : IntegrableOn (fun x => D 0 b x*φ x) Ω := (integrable_mul_test ho hdb.continuousOn hφ.continuous hk hs).integrableOn
    have hj : IntegrableOn (fun x => D 1 a x*φ x) Ω := (integrable_mul_test ho hda.continuousOn hφ.continuous hk hs).integrableOn
    have hi' : IntegrableOn (fun x => b x*D 0 φ x) Ω := (integrable_mul_test ho hb.continuousOn (D_smooth hφ 0).continuous
      (D_compact hk 0) ((D_support φ 0).trans hs)).integrableOn
    have hj' : IntegrableOn (fun x => a x*D 1 φ x) Ω := (integrable_mul_test ho ha.continuousOn (D_smooth hφ 1).continuous
      (D_compact hk 1) ((D_support φ 1).trans hs)).integrableOn
    have h0 := integral_mul_test_fderiv ho hb hφ hk hs (e 0)
    have h1 := integral_mul_test_fderiv ho ha hφ hk hs (e 1)
    have h := hc φ hφ hk hs
    simp_rw [inner_rot_gradient] at h
    rw [integral_sub hi' hj'] at h
    change (∫ x in Ω, b x * D 0 φ x) = -(∫ x in Ω, D 0 b x * φ x) at h0
    change (∫ x in Ω, a x * D 1 φ x) = -(∫ x in Ω, D 1 a x * φ x) at h1
    rw [h0,h1] at h
    simp only [smul_eq_mul]
    simp_rw [mul_comm (φ _) _]
    rw [← setIntegral_mul_test hs]
    simp_rw [sub_mul]
    rw [integral_sub hi hj]
    linarith

lemma smooth_closed {Ω : Set Plane} (ho : IsOpen Ω)
    {W : Plane → Plane} (hW : ContDiffOn ℝ ∞ W Ω) (hc : WeakCurlZero Ω W) :
    ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (W a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (W a)) a y x := by
  intro a ha x y
  have hw : DifferentiableAt ℝ W a :=
    (hW.differentiableOn (by simp) a ha).differentiableAt (ho.mem_nhds ha)
  have hform (x y : Plane) :
      fderiv ℝ (fun a => innerSL ℝ (W a)) a x y = inner ℝ (fderiv ℝ W a x) y := by
    have hh : HasFDerivAt (fun a => innerSL ℝ (W a))
        ((innerSL ℝ (E := Plane)).comp (fderiv ℝ W a)) a :=
      (innerSL ℝ (E := Plane)).hasFDerivAt.comp a hw.hasFDerivAt
    rw [hh.fderiv]
    rfl
  have hcoord (i j : Fin 2) : D i (fun y => c j (W y)) a =
      inner ℝ (fderiv ℝ W a (e i)) (e j) := by
    change fderiv ℝ (fun y => inner ℝ (W y) (e j)) a (e i) = _
    rw [fderiv_inner_apply ℝ hw (differentiableAt_const _)]
    simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,inner_zero_right,zero_add]
  have hc' := smooth_curl_zero ho hW hc a ha
  rw [hcoord,hcoord] at hc'
  simp_rw [hform]
  conv_lhs => rw [← expand x,← expand y]
  conv_rhs => rw [← expand y,← expand x]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,conj_trivial]
  rw [hc']
  ring




theorem weak_divCurl_zero {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hc : WeakCurlZero Ω Z)
    (hz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (Z x) (g x)) = 0) :
    Z =ᵐ[volume.restrict Ω] 0 := by
  have hd : WeakDivZero Ω Z := fun φ hφ hk _ => hz φ _ (HasH1Gradient.test ho hφ hk)
  obtain ⟨W,hW,he⟩ := weak_divCurl_smooth ho hb hm hd hc
  have hwm : MemLp W 2 (volume.restrict Ω) := (memLp_congr_ae he).mpr hm
  have heI (f : Plane → Plane) : (∫ x in Ω, inner ℝ (W x) (f x)) =
      ∫ x in Ω, inner ℝ (Z x) (f x) :=
    integral_congr_ae (he.mono fun x hx => congrArg (fun t => inner ℝ t (f x)) hx)
  have hwc : WeakCurlZero Ω W := fun φ hφ hk ht => (heI _).trans (hc φ hφ hk ht)
  have hwz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (W x) (g x)) = 0 :=
    fun v g hv => (heI g).trans (hz v g hv)
  have hw0 := closed_orthogonal_gradient_zero ho hs hb hμ hW hwm (smooth_closed ho hW hwc) hwz
  exact he.symm.trans ((ae_restrict_mem ho.measurableSet).mono fun x hx => hw0 x hx)

end StrictHotSpots.Hodge

end WeakHodgeRegularityInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Hodge
attribute [-instance] _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section ActualNeumannHilbertLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots
namespace H1
variable {Ω : Set Plane}

lemma norm_value_sq (u : H1 Ω) :
    ‖value u‖ ^ 2 = ∫ x in Ω, (value u x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

lemma norm_grad_sq (u : H1 Ω) :
    ‖grad u‖ ^ 2 = ∫ x in Ω, ‖grad u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]


lemma rayleigh (u : H1 Ω) (hm : (∫ x in Ω, value u x) = 0) :
    firstPositiveNeumannValue Ω * ‖value u‖ ^ 2 ≤ ‖grad u‖ ^ 2 := by
  by_cases hz : ‖value u‖ = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact sq_nonneg _
  · have hp : 0 < ‖value u‖ ^ 2 := sq_pos_of_ne_zero hz
    rw [norm_value_sq] at hp
    simpa only [norm_value_sq, norm_grad_sq] using
      rayleigh_inequality (hasH1Gradient u) hm hp


lemma mean_apply (hb : Bornology.IsBounded Ω) (u : H1 Ω) :
    mean hb u = ∫ x in Ω, value u x := mean_eq hb u

end H1


namespace N1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)

lemma norm_sq (u : N1 hb) : ‖u‖ ^ 2 = ‖value hb u‖ ^ 2 + ‖grad hb u‖ ^ 2 :=
  H1.norm_sq u.val

lemma mean_zero (u : N1 hb) : (∫ x in Ω, value hb u x) = 0 := by
  have hu : H1.mean hb u.val = 0 := u.property
  change (∫ x in Ω, H1.value u.val x) = 0
  simpa only [H1.mean_apply] using hu

lemma rayleigh (u : N1 hb) :
    firstPositiveNeumannValue Ω * ‖value hb u‖ ^ 2 ≤ ‖grad hb u‖ ^ 2 :=
  H1.rayleigh u.val (mean_zero hb u)

lemma energy_coercive (hμ : 0 < firstPositiveNeumannValue Ω) :
    @IsCoercive (N1 hb) (N1.normedAddCommGroup hb).toSeminormedAddCommGroup
      (N1.innerProductSpace hb).toNormedSpace (energy hb) := by
  let μ := firstPositiveNeumannValue Ω
  have hden : 0 < μ + 1 := by dsimp [μ]; positivity
  refine ⟨μ / (μ + 1), div_pos hμ hden, fun u => ?_⟩
  have hR := rayleigh hb u
  have hbound : μ * ‖u‖ ^ 2 ≤ (μ + 1) * ‖grad hb u‖ ^ 2 := by
    rw [norm_sq hb]
    nlinarith
  calc
    (μ / (μ + 1)) * ‖u‖ * ‖u‖ = (μ * ‖u‖ ^ 2) / (μ + 1) := by ring
    _ ≤ ‖grad hb u‖ ^ 2 := (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hbound)
    _ = energy hb u u := (real_inner_self_eq_norm_sq _).symm




lemma existsUnique_energy_solution (hμ : 0 < firstPositiveNeumannValue Ω)
    (ℓ : N1 hb →L[ℝ] ℝ) :
    ∃! u : N1 hb, ∀ v : N1 hb, energy hb u v = ℓ v := by
  exact @existsUnique_of_coercive (N1 hb) (N1.normedAddCommGroup hb)
    (N1.innerProductSpace hb) (N1.completeSpace hb)
    (energy hb) (energy_coercive hb hμ) ℓ

end N1
end StrictHotSpots

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
end ActualNeumannHilbertLayer

section HodgeOrthogonalityInteriorSupportLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Hodge

lemma weakCurl_gradient {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) : WeakCurlZero Ω g := by
  intro φ hφ hk hs
  have h0 := hv.2.2 (D 0 φ) (D_smooth hφ 0) (D_compact hk 0) ((D_support φ 0).trans hs) (e 1)
  have h1 := hv.2.2 (D 1 φ) (D_smooth hφ 1) (D_compact hk 1) ((D_support φ 1).trans hs) (e 0)
  change (∫ x in Ω, v x * D 1 (D 0 φ) x) = -(∫ x in Ω, c 1 (g x)*D 0 φ x) at h0
  change (∫ x in Ω, v x * D 0 (D 1 φ) x) = -(∫ x in Ω, c 0 (g x)*D 1 φ x) at h1
  simp_rw [D_D hφ 1 0] at h0
  have hi := (hv.2.1.inner_const (e 1)).integrable_mul (test_derivative_memLp hφ hk (e 0))
  have hj := (hv.2.1.inner_const (e 0)).integrable_mul (test_derivative_memLp hφ hk (e 1))
  change IntegrableOn (fun x => c 1 (g x)*D 0 φ x) Ω at hi
  change IntegrableOn (fun x => c 0 (g x)*D 1 φ x) Ω at hj
  simp_rw [inner_rot_gradient]
  rw [integral_sub hi hj]
  linarith

lemma rotL_ae {Ω : Set Plane} (u : V2 Ω) : rotL Ω u =ᵐ[volume.restrict Ω] fun x => rot (u x) :=
  rot.coeFn_compLpL u
lemma rotL_inner {Ω : Set Plane} (u v : V2 Ω) : inner ℝ (rotL Ω u) (rotL Ω v) = inner ℝ u v := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rotL_ae u,rotL_ae v] with x hx hy
  rw [hx,hy,rot_inner]
lemma rotL_norm {Ω : Set Plane} (u : V2 Ω) : ‖rotL Ω u‖ = ‖u‖ := by
  have hh := rotL_inner u u
  simp only [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (rotL Ω u),norm_nonneg u]

lemma weakCurl_iff {Ω : Set Plane} (ho : IsOpen Ω) (Z : V2 Ω) :
    WeakCurlZero Ω Z ↔ ∀ j : H10 ho, inner ℝ Z (rotL Ω (H10.grad ho j)) = 0 := by
  constructor
  · intro hz j
    apply isClosed_property (dense_smoothTestToH10 ho)
      (isClosed_eq (continuous_const.inner ((rotL Ω).continuous.comp (H10.grad ho).continuous)) continuous_const) _ j
    intro f
    rw [L2.inner_def]
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient f.val :=
      (test_gradient_memLp f.property.1 f.property.2.1).coeFn_toLp
    calc
      _ = ∫ x in Ω, inner ℝ (Z x) (rot (gradient f.val x)) := by
        apply integral_congr_ae
        filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
        change inner ℝ (Z x) ((rotL Ω (H10.grad ho (smoothTestToH10 ho f))) x) = _
        rw [hx,hy]
      _ = 0 := hz f.val f.property.1 f.property.2.1 f.property.2.2
  · intro hz φ hφ hk hs
    let f : smoothTestSpace Ω := ⟨φ,hφ,hk,hs⟩
    have h := hz (smoothTestToH10 ho f)
    rw [L2.inner_def] at h
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient φ :=
      (test_gradient_memLp hφ hk).coeFn_toLp
    convert h using 1
    apply integral_congr_ae
    filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
    rw [hx,hy]

lemma grad_rotGrad_orthogonal {Ω : Set Plane} (ho : IsOpen Ω) (v : H1 Ω) (j : H10 ho) :
    inner ℝ (H1.grad v) (rotL Ω (H10.grad ho j)) = 0 :=
  (weakCurl_iff ho (H1.grad v)).mp (weakCurl_gradient (H1.hasH1Gradient v)) j

lemma exists_meanZero_same_grad {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (v : H1 Ω) :
    ∃ u : N1 hb, N1.grad hb u = H1.grad v := by
  let C : H1 Ω := (HasH1Gradient.const hb 1).toH1
  have hcG : H1.grad C = 0 := by
    apply Lp.ext
    exact ((HasH1Gradient.const hb 1).2.1.coeFn_toLp).trans (Lp.coeFn_zero _ _ _).symm
  have hcM : H1.mean hb C = (volume Ω).toReal := by
    rw [H1.mean_apply]
    calc
      _ = ∫ x in Ω, (1 : ℝ) := integral_congr_ae (HasH1Gradient.const hb 1).1.coeFn_toLp
      _ = _ := by simp [Measure.real]
  have hv : (volume Ω).toReal ≠ 0 :=
    (ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne).ne'
  let u : H1 Ω := v - (H1.mean hb v/(volume Ω).toReal) • C
  have hm : H1.mean hb u = 0 := by
    simp only [u,map_sub,map_smul,smul_eq_mul,hcM]
    field_simp
    ring
  refine ⟨⟨u,hm⟩,?_⟩
  change H1.grad u = _
  simp only [u,map_sub,map_smul,hcG,smul_zero,sub_zero]

end Hodge
end StrictHotSpots

end HodgeOrthogonalityInteriorSupportLayer


section HodgeProjectionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge
lemma nProjection {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ v : N1 hb, ∀ w : N1 hb, inner ℝ (N1.grad hb v) (N1.grad hb w) =
      inner ℝ X (N1.grad hb w) :=
  ExistsUnique.exists (N1.existsUnique_energy_solution hb hμ (nFunctional hb X))

lemma nProjection_extend {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) (v : N1 hb)
    (hv : ∀ w : N1 hb, inner ℝ (N1.grad hb v) (N1.grad hb w) = inner ℝ X (N1.grad hb w))
    (u : H1 Ω) : inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u) := by
  obtain ⟨w,hw⟩ := exists_meanZero_same_grad (Ω := Ω) ho hne hb u
  exact hw ▸ hv w

lemma neumann_projection {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ v : N1 hb, ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u) :=
  (nProjection (Ω := Ω) hb hμ X).imp fun v hv => nProjection_extend ho hne hb X v hv

lemma jProjection {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ j : H10 ho, ∀ k : H10 ho, inner ℝ (H10.grad ho j) (H10.grad ho k) =
      inner ℝ X (rotL Ω (H10.grad ho k)) :=
  ExistsUnique.exists (H10.existsUnique_energy_solution ho hb (jFunctional ho X))

lemma dirichlet_projection {Ω : Set Plane} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ j : H10 ho, ∀ k : H10 ho,
      inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
        inner ℝ X (rotL Ω (H10.grad ho k)) := by
  exact (jProjection (Ω := Ω) ho hb X).imp fun j hj k =>
    (rotL_inner (Ω := Ω) (H10.grad ho j) (H10.grad ho k)).trans (hj k)
end StrictHotSpots.Hodge

end HodgeProjectionInteriorSupportLayer


section HodgeResidualInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

private lemma inner_sub_sub_normal_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (first second third test : E)
    (hsecond : inner ℝ second test = inner ℝ first test)
    (hthird : inner ℝ third test = 0) :
    inner ℝ (first - second - third) test = 0 := by
  rw [inner_sub_left, inner_sub_left, hsecond, hthird, sub_self, sub_zero]

lemma residual_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u))
    (u : H1 Ω) : inner ℝ (residual ho hb X v j) (H1.grad u) = 0 := by
  have he : inner ℝ (rotL Ω (H10.grad ho j)) (H1.grad u) = 0 :=
    (real_inner_comm _ _).trans (grad_rotGrad_orthogonal ho u j)
  exact inner_sub_sub_normal_zero X (N1.grad hb v) (rotL Ω (H10.grad ho j))
    (H1.grad u) (hn u) he

lemma inner_sub_sub_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X A B Y : E) (he : inner ℝ A Y = 0) (hj : inner ℝ B Y = inner ℝ X Y) :
    inner ℝ (X-A-B) Y = 0 := by
  rw [inner_sub_left,inner_sub_left,he,hj,sub_zero,sub_self]

lemma residual_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hj : ∀ k : H10 ho, inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
      inner ℝ X (rotL Ω (H10.grad ho k))) (k : H10 ho) :
    inner ℝ (residual ho hb X v j) (rotL Ω (H10.grad ho k)) = 0 :=
  inner_sub_sub_zero X (N1.grad hb v) (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k))
    (grad_rotGrad_orthogonal ho v.val k) (hj k)

lemma orthogonal_all_zero {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω) (Z : V2 Ω)
    (hzN : ∀ u : H1 Ω, inner ℝ Z (H1.grad u) = 0)
    (hzJ : ∀ k : H10 ho, inner ℝ Z (rotL Ω (H10.grad ho k)) = 0) : Z = 0 := by
  apply Lp.ext
  refine (weak_divCurl_zero ho hs hb hμ (Lp.memLp Z) ((weakCurl_iff ho Z).mpr hzJ) ?_).trans
    (Lp.coeFn_zero _ _ _).symm
  intro u g hh
  have h := hzN hh.toH1
  rw [L2.inner_def] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hh.2.1.coeFn_toLp] with x hx
  change inner ℝ (Z x) (g x) = inner ℝ (Z x) (hh.2.1.toLp g x)
  rw [hx]

lemma sub_sub_zero_iff {E : Type*} [AddCommGroup E] (X A B : E) :
    X-A-B=0 ↔ X=A+B := by rw [sub_sub,sub_eq_zero]

lemma residual_zero_iff {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho) :
    residual ho hb X v j = 0 ↔ X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  sub_sub_zero_iff X (N1.grad hb v) (rotL Ω (H10.grad ho j))

lemma norm_add_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : ‖a+b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  rw [norm_add_sq_real,h]
  ring

lemma decomposition_norm {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) :
    ‖N1.grad hb v + rotL Ω (H10.grad ho j)‖^2 =
      ‖N1.grad hb v‖^2 + ‖H10.grad ho j‖^2 := by
  exact (norm_add_orthogonal _ _ (grad_rotGrad_orthogonal ho v.val j)).trans
    (congrArg (fun r : ℝ => ‖N1.grad hb v‖^2 + r^2) (rotL_norm (H10.grad ho j)))
end StrictHotSpots.Hodge

end HodgeResidualInteriorSupportLayer


section HodgeDecompositionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

lemma projection_eq {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u))
    (hj : ∀ k : H10 ho, inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
      inner ℝ X (rotL Ω (H10.grad ho k))) :
    X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (residual_zero_iff ho hb X v j).mp (orthogonal_all_zero ho hs hb hμ (residual ho hb X v j)
    (residual_normal ho hb X v j hn) (residual_curl ho hb X v j hj))

lemma projection_eq_exists {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    (X : V2 Ω) (v : N1 hb)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u)) :
    ∃ j : H10 ho, X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (dirichlet_projection ho hb X).imp fun j hj => projection_eq ho hs hb hμ X v j hn hj



theorem decomposition {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) (X : V2 Ω) :
    ∃ (v : N1 hb) (j : H10 ho), X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (neumann_projection ho hne hb hμ X).imp fun v hn => projection_eq_exists ho hs hb hμ X v hn
end StrictHotSpots.Hodge

end HodgeDecompositionInteriorSupportLayer


section HodgeVectorEnergyInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

lemma scalar_energy_bound {a b c θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ht : 0 ≤ θ) (hr : θ*b^2 ≤ a^2) (he : a^2 ≤ b*c) : θ*a^2 ≤ c^2 := by
  by_cases h : b = 0
  · subst b
    have hz : a = 0 := by nlinarith
    simp [hz,sq_nonneg]
  · have hp : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
    have htc : θ*b ≤ c := (mul_le_mul_iff_of_pos_right hp).mp (by nlinarith)
    calc
      θ*a^2 ≤ θ*(b*c) := mul_le_mul_of_nonneg_left he ht
      _ = (θ*b)*c := by ring
      _ ≤ c*c := mul_le_mul_of_nonneg_right htc hc
      _ = c^2 := by ring

lemma pair_add_orthogonal_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : inner ℝ (a+b) a = ‖a‖^2 := by
  rw [inner_add_left,real_inner_comm a b,h,add_zero,real_inner_self_eq_norm_sq]

lemma pair_add_orthogonal_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : inner ℝ (a+b) b = ‖b‖^2 := by
  rw [inner_add_left,h,zero_add,real_inner_self_eq_norm_sq]

lemma neg_inner_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : -inner ℝ a b ≤ ‖b‖*‖a‖ := by
  simpa only [inner_neg_left,norm_neg,mul_comm] using real_inner_le_norm (-a) b

lemma energy_pair_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (F : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv (N1.grad hb v + rotL Ω (H10.grad ho j)) F) :
    ‖N1.grad hb v‖^2 = -inner ℝ F (N1.value hb v) :=
  (pair_add_orthogonal_left _ _ (grad_rotGrad_orthogonal ho v.val j)).symm.trans (hF v.val)

lemma energy_pair_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (G : Lp ℝ 2 (volume.restrict Ω))
    (hG : WeakCurl ho (N1.grad hb v + rotL Ω (H10.grad ho j)) G) :
    ‖H10.grad ho j‖^2 = -inner ℝ G (H10.value ho j) :=
  (congrArg (fun r : ℝ => r^2) (rotL_norm (H10.grad ho j))).symm.trans
    ((pair_add_orthogonal_right _ _ (grad_rotGrad_orthogonal ho v.val j)).symm.trans (hG j))

lemma energy_bound_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (F : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv (N1.grad hb v + rotL Ω (H10.grad ho j)) F) :
    firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 := by
  apply scalar_energy_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (firstPositiveNeumannValue_nonneg Ω) (N1.rayleigh hb v)
  exact (energy_pair_normal ho hb v j F hF).trans_le (neg_inner_bound F (N1.value hb v))

lemma energy_bound_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (G : Lp ℝ 2 (volume.restrict Ω)) {L : ℝ} (hl : 0 ≤ L)
    (hD : L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (hG : WeakCurl ho (N1.grad hb v + rotL Ω (H10.grad ho j)) G) :
    L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 := by
  apply scalar_energy_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hl hD
  exact (energy_pair_curl ho hb v j G hG).trans_le (neg_inner_bound G (H10.value ho j))

lemma energy_decomposition_of_eq {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ} (hl : 0 ≤ L) (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω)) (v : N1 hb) (j : H10 ho)
    (hX : X = N1.grad hb v + rotL Ω (H10.grad ho j))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    X = N1.grad hb v + rotL Ω (H10.grad ho j) ∧
      firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 ∧
      L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 :=
  ⟨hX,energy_bound_normal ho hb v j F (by rwa [← hX]),
    energy_bound_curl ho hb v j G hl (hD j) (by rwa [← hX])⟩


theorem energy_decomposition {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    ∃ (v : N1 hb) (j : H10 ho),
      X = N1.grad hb v + rotL Ω (H10.grad ho j) ∧
      firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 ∧
      L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 :=
  (decomposition ho hne hs hb hμ X).imp fun v hv => hv.imp fun j hj =>
    energy_decomposition_of_eq ho hb (hμ.trans hl).le hD X F G v j hj hF hG

theorem vector_inequality {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : Lp Plane 2 (volume.restrict Ω)) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    firstPositiveNeumannValue Ω * ‖X‖^2 ≤ ‖F‖^2 + ‖G‖^2 := by
  obtain ⟨v,j,hX,hv,hj⟩ := energy_decomposition ho hne hs hb hμ hl hD X F G hF hG
  rw [hX,decomposition_norm ho hb]
  nlinarith [sq_nonneg ‖H10.grad ho j‖]

end StrictHotSpots.Hodge

end HodgeVectorEnergyInteriorSupportLayer


end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section VectorSobolevActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


lemma coordinateL_ae (i : Fin 2) (v : V2 Ω) :
    coordinateL Ω i v =ᵐ[volume.restrict Ω] fun x => c i (v x) := by
  filter_upwards [(innerSL ℝ (e i)).coeFn_compLpL v] with x hx
  apply hx.trans
  change inner ℝ (e i) (v x) = inner ℝ (v x) (e i)
  exact real_inner_comm _ _


lemma axisL_ae (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω i u =ᵐ[volume.restrict Ω] fun x => u x • e i :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).coeFn_compLpL u

lemma scalar_pair_L2 (u v : Lp ℝ 2 (volume.restrict Ω)) :
    inner ℝ u v = ∫ x in Ω, u x*v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    exact mul_comm _ _

lemma partialL_compact_integration_by_parts (ho : IsOpen Ω) (i : Fin 2)
    (u : H1 Ω) (φ : smoothTestSpace Ω) :
    inner ℝ (H1.value u) (partialL i (smoothTestToH10 ho φ).val) =
      -inner ℝ (partialL i u) (H10.value ho (smoothTestToH10 ho φ)) := by
  have hv : H10.value ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] φ.val :=
    (test_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  have hg : H10.grad ho (smoothTestToH10 ho φ) =ᵐ[volume.restrict Ω] gradient φ.val :=
    (test_gradient_memLp φ.property.1 φ.property.2.1).coeFn_toLp
  rw [scalar_pair_L2,scalar_pair_L2]
  have hl : (∫ x in Ω, H1.value u x*partialL i (smoothTestToH10 ho φ).val x) =
      ∫ x in Ω, H1.value u x*(fderiv ℝ φ.val x) (e i) := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H10.grad ho (smoothTestToH10 ho φ)),hg] with x hx hy
    exact congrArg (fun a : ℝ => H1.value u x*a)
      (hx.trans ((congrArg (c i) hy).trans (gradient_c _ _ _)))
  have hr : (∫ x in Ω, partialL i u x*H10.value ho (smoothTestToH10 ho φ) x) =
      ∫ x in Ω, inner ℝ (H1.grad u x) (e i)*φ.val x := by
    apply integral_congr_ae
    filter_upwards [coordinateL_ae i (H1.grad u),hv] with x hx hy
    exact congrArg₂ (fun a b : ℝ => a*b) hx hy
  exact hl.trans (((H1.hasH1Gradient u).2.2 φ.val φ.property.1 φ.property.2.1
    φ.property.2.2 (e i)).trans (congrArg Neg.neg hr).symm)



lemma partialL_integration_by_parts (ho : IsOpen Ω) (i : Fin 2) (u : H1 Ω) (v : H10 ho) :
    inner ℝ (H1.value u) (partialL i v.val) =
      -inner ℝ (partialL i u) (H10.value ho v) := by
  apply isClosed_property (dense_smoothTestToH10 ho) _ _ v
  · exact isClosed_eq
      (continuous_const.inner ((coordinateL Ω i).continuous.comp (H10.grad ho).continuous))
      ((continuous_const.inner (H10.value ho).continuous).neg)
  · exact partialL_compact_integration_by_parts ho i u

lemma axis_coordinate_pair (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω i u) v = inner ℝ u (coordinateL Ω i v) := by
  rw [L2.inner_def,scalar_pair_L2]
  apply integral_congr_ae
  filter_upwards [axisL_ae i u,coordinateL_ae i v] with x hx hy
  rw [hx,hy,real_inner_smul_left]
  exact congrArg (fun t : ℝ => u x*t) (real_inner_comm _ _)

lemma coordinateL_rot_zero (v : V2 Ω) :
    coordinateL Ω 0 (rotL Ω v) = -coordinateL Ω 1 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 0 (rotL Ω v),rotL_ae v,
    coordinateL_ae 1 v,Lp.coeFn_neg (coordinateL Ω 1 v)] with x h0 hr h1 hn
  rw [h0,hr,hn,Pi.neg_apply,h1,(c_rot _).1]

lemma coordinateL_rot_one (v : V2 Ω) :
    coordinateL Ω 1 (rotL Ω v) = coordinateL Ω 0 v := by
  apply Lp.ext
  filter_upwards [coordinateL_ae 1 (rotL Ω v),rotL_ae v,
    coordinateL_ae 0 v] with x h0 hr h1
  rw [h0,hr,h1,(c_rot _).2]

lemma axis_sum_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) v =
      inner ℝ a (coordinateL Ω 0 v)+inner ℝ b (coordinateL Ω 1 v) := by
  rw [inner_add_left,axis_coordinate_pair,axis_coordinate_pair]

lemma axis_sum_rot_pair (a b : Lp ℝ 2 (volume.restrict Ω)) (v : V2 Ω) :
    inner ℝ (axisL Ω 0 a+axisL Ω 1 b) (rotL Ω v) =
      -inner ℝ a (coordinateL Ω 1 v)+inner ℝ b (coordinateL Ω 0 v) := by
  rw [axis_sum_pair,coordinateL_rot_zero,coordinateL_rot_one,inner_neg_right]

lemma partialL_test_curl (ho : IsOpen Ω) (X : Fin 2 → H1 Ω) (v : H10 ho) :
    inner ℝ (vectorValue X) (rotL Ω (H10.grad ho v)) =
      -inner ℝ (curlL X) (H10.value ho v) := by
  calc
    _ = -inner ℝ (H1.value (X 0)) (partialL 1 v.val)+
        inner ℝ (H1.value (X 1)) (partialL 0 v.val) := axis_sum_rot_pair _ _ _
    _ = -(-inner ℝ (partialL 1 (X 0)) (H10.value ho v))+
        (-inner ℝ (partialL 0 (X 1)) (H10.value ho v)) :=
      congrArg₂ (fun a b : ℝ => -a+b) (partialL_integration_by_parts ho 1 (X 0) v)
        (partialL_integration_by_parts ho 0 (X 1) v)
    _ = _ := by simp only [curlL,inner_sub_left]; ring

end StrictHotSpots.Hodge
end VectorSobolevActualCompatibleLayer

section TangentVectorClassActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


theorem vectorForm_nonneg_oai (ho : IsOpen Ω) (hne : Ω.Nonempty) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : Fin 2 → H1 Ω) (hX : TangentWeak X) :
    0 ≤ vectorForm (firstPositiveNeumannValue Ω) X X := by
  have hh := vector_inequality ho hne hs hb hμ hl hD (vectorValue X)
    (divergenceL X) (curlL X) hX (partialL_test_curl ho X)
  simpa only [vectorForm,real_inner_self_eq_norm_sq,sub_nonneg] using hh

end StrictHotSpots.Hodge
end TangentVectorClassActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
end
end ActualVectorSupport


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Hodge.vectorForm_nonneg_oai := @OAI.StrictHotSpots.Hodge.vectorForm_nonneg_oai
