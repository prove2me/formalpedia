-- Prove2me | solution 1 for OAI.StrictHotSpots.H10.subcritical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:18:46.723991+00:00
-- url     : https://prove2.me/submissions/167d5188-e3e7-4a5c-9b7c-6c4bfeb8eeb1

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003
import Theorems.Thm_OAI_StrictHotSpots_H10_minimum

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

end StrictHotSpots




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

lemma integral_norm_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Plane} {f g : Plane → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℝ) :
    (∫ x, ‖f x + t • g x‖ ^ 2 ∂μ) = (∫ x, ‖f x‖ ^ 2 ∂μ) +
      2 * t * (∫ x, inner ℝ (f x) (g x) ∂μ) + t ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.integrable_norm_pow (by norm_num)
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ := hg.integrable_norm_pow (by norm_num)
  have hfg := integrable_inner_of_memLp hf hg
  calc
    _ = ∫ x, ‖f x‖ ^ 2 + 2 * t * inner ℝ (f x) (g x) + t ^ 2 * ‖g x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_comm (g x) (f x)]
      ring
    _ = _ := by
      have hi12 : Integrable (fun x => ‖f x‖ ^ 2 + 2 * t * inner ℝ (f x) (g x)) μ :=
        hf2.add (hfg.const_mul (2 * t))
      rw [integral_add hi12 (hg2.const_mul (t ^ 2)),
        integral_add hf2 (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]

lemma integral_sq_add_mul {μ : Measure Plane} {v w : Plane → ℝ}
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) (t : ℝ) :
    (∫ x, (v x + t * w x) ^ 2 ∂μ) = (∫ x, (v x) ^ 2 ∂μ) +
      2 * t * (∫ x, v x * w x ∂μ) + t ^ 2 * (∫ x, (w x) ^ 2 ∂μ) := by
  simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using
    integral_norm_add_smul_sq hv hw t

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

section PlaneWavesCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff Laplacian
namespace StrictHotSpots.PlaneWaves

lemma laplacian_cosine (k x : Plane) : Δ (cosine k) x = -‖k‖^2 * cosine k x := by
  let b := stdOrthonormalBasis ℝ Plane
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hd : ∀ i, iteratedFDeriv ℝ 2 (cosine k) x ![b i, b i] =
      -(inner ℝ k (b i))^2 * cosine k x := by
    intro i
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : fderiv ℝ (cosine k) = fun y => (-sine k y) • innerSL ℝ k :=
      funext (fderiv_cosine k)
    rw [hc, fderiv_smul_const (c := fun y : Plane => -(sine k y)) ((sine_smooth k).differentiable (by simp) x).neg (innerSL ℝ k : Plane →L[ℝ] ℝ),
      fderiv_fun_neg, fderiv_sine]
    simp
    ring
  change (∑ i, iteratedFDeriv ℝ 2 _ x ![b i, b i]) = _
  simp_rw [hd]
  rw [← Finset.sum_mul]
  have hs : ∑ i, (inner ℝ k (b i))^2 = ‖k‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq,real_inner_comm (b _) k] using (b.sum_inner_mul_inner k k)
  rw [Finset.sum_neg_distrib,hs]

lemma laplacian_sine (k x : Plane) : Δ (sine k) x = -‖k‖^2 * sine k x := by
  let b := stdOrthonormalBasis ℝ Plane
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hd : ∀ i, iteratedFDeriv ℝ 2 (sine k) x ![b i, b i] =
      -(inner ℝ k (b i))^2 * sine k x := by
    intro i
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : fderiv ℝ (sine k) = fun y => cosine k y • innerSL ℝ k :=
      funext (fderiv_sine k)
    rw [hc, fderiv_smul_const ((cosine_smooth k).differentiable (by simp) x) (innerSL ℝ k : Plane →L[ℝ] ℝ),
      fderiv_cosine]
    simp
    ring
  change (∑ i, iteratedFDeriv ℝ 2 _ x ![b i, b i]) = _
  simp_rw [hd]
  rw [← Finset.sum_mul]
  have hs : ∑ i, (inner ℝ k (b i))^2 = ‖k‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq,real_inner_comm (b _) k] using (b.sum_inner_mul_inner k k)
  rw [Finset.sum_neg_distrib,hs]

end StrictHotSpots.PlaneWaves
end PlaneWavesCombinedLayer

section LowerEulerCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace StrictHotSpots
lemma lower_rayleigh {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0) :
    lam * (∫ x in Ω, (v x)^2) ≤ ∫ x in Ω, ‖g x‖^2 :=
  (mul_le_mul_of_nonneg_right hle (integral_nonneg fun x => sq_nonneg (v x))).trans
    (rayleigh_inequality_all hv hm)


lemma lower_euler_mean_zero {Ω : Set Plane} {u v : Plane → ℝ}
    {g k : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω) (hb : Bornology.IsBounded Ω)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0) (hmv : (∫ x in Ω, v x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      lam * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      lam * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hvar (t : ℝ) := lower_rayleigh hle (hu.add (hv.smul t)) (by
    show (∫ x in Ω, u x + t * v x) = 0
    rw [integral_add hui (hvi.const_mul t), integral_const_mul, hmu, hmv]
    ring)
  have hpoly : ∀ t : ℝ, 0 ≤
      ((∫ x in Ω, ‖k x‖ ^ 2) - lam * (∫ x in Ω, (v x) ^ 2)) * (t * t) +
      (2 * ((∫ x in Ω, inner ℝ (g x) (k x)) -
        lam * (∫ x in Ω, u x * v x))) * t + 0 := by
    intro t
    have ht := hvar t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
    rw [integral_norm_add_smul_sq hu.2.1 hv.2.1 t,
      integral_sq_add_mul hu.1 hv.1 t, he] at ht
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg ((∫ x in Ω, inner ℝ (g x) (k x)) -
    lam * (∫ x in Ω, u x * v x))]



lemma lower_euler {Ω : Set Plane} {u v : Plane → ℝ} {g k : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hb : Bornology.IsBounded Ω) (hvol : 0 < (volume Ω).toReal)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      lam * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      lam * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  let c := (∫ x in Ω, v x) / (volume Ω).toReal
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hw : HasH1Gradient Ω (fun x => v x - c) k := by
    change HasH1Gradient Ω (v - fun _ => c) k
    simpa only [sub_zero] using hv.sub (HasH1Gradient.const hb c)
  have hm : (∫ x in Ω, v x - c) = 0 := by
    rw [integral_sub hvi (integrable_const c)]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    change (∫ x in Ω, v x) - (volume Ω).toReal * c = 0
    dsimp [c]
    field_simp
    ring
  have hh := lower_euler_mean_zero hle hb hu hw hmu hm he
  have hi : (∫ x in Ω, u x * (v x - c)) = (∫ x in Ω, u x * v x) := by
    simp only [mul_sub]
    have huv : Integrable (fun x => u x * v x) (volume.restrict Ω) := hu.1.integrable_mul hv.1
    rw [integral_sub huv (hui.mul_const c),
      integral_mul_const, hmu, zero_mul, sub_zero]
  rwa [hi] at hh


end StrictHotSpots
end LowerEulerCombinedLayer

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
lemma toLp_left {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : α → E} (hf : MemLp f 2 μ) (g : Lp E 2 μ) :
    inner ℝ (hf.toLp f) g = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
lemma toLp_right {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : α → E} (f : Lp E 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ f (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
end StrictHotSpots.L2Inner
end L2InnerToLpCombinedLayer

section H1RayleighFormCombinedLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace StrictHotSpots
private lemma two_inner_sub_left {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (lam : ℝ) (a b c : A) (x y z : B) :
    inner ℝ (a-b) c - lam * inner ℝ (x-y) z =
      (inner ℝ a c - lam * inner ℝ x z) - (inner ℝ b c - lam * inner ℝ y z) := by
  rw [inner_sub_left,inner_sub_left]
  ring
private lemma two_inner_sub_right {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (lam : ℝ) (a b c : A) (x y z : B) :
    inner ℝ a (b-c) - lam * inner ℝ x (y-z) =
      (inner ℝ a b - lam * inner ℝ x y) - (inner ℝ a c - lam * inner ℝ x z) := by
  rw [inner_sub_right,inner_sub_right]
  ring
end StrictHotSpots
namespace StrictHotSpots.H1
variable {Ω : Set Plane}

lemma form_symm (lam : ℝ) (u v : H1 Ω) : form lam u v = form lam v u := by
  exact congrArg₂ (fun a b : ℝ => a - lam * b)
    (real_inner_comm (grad u) (grad v)).symm (real_inner_comm (value u) (value v)).symm
lemma form_sub_left (lam : ℝ) (u v w : H1 Ω) :
    form lam (u-v) w = form lam u w - form lam v w := by
  exact StrictHotSpots.two_inner_sub_left lam (grad u) (grad v) (grad w) (value u) (value v) (value w)
lemma form_sub_right (lam : ℝ) (u v w : H1 Ω) :
    form lam u (v-w) = form lam u v - form lam u w := by
  exact StrictHotSpots.two_inner_sub_right lam (grad u) (grad v) (grad w) (value u) (value v) (value w)
lemma form_smul_left (lam c : ℝ) (u v : H1 Ω) :
    form lam (c • u) v = c * form lam u v := by
  unfold form
  change inner ℝ (c • grad u) (grad v) - lam * inner ℝ (c • value u) (value v) = _
  rw [real_inner_smul_left,real_inner_smul_left]
  ring
lemma form_smul_right (lam c : ℝ) (u v : H1 Ω) :
    form lam u (c • v) = c * form lam u v := by
  unfold form
  change inner ℝ (grad u) (c • grad v) - lam * inner ℝ (value u) (c • value v) = _
  rw [real_inner_smul_right,real_inner_smul_right]
  ring
lemma form_diag_sub (lam c : ℝ) (u v : H1 Ω)
    (hv : form lam v v = 0) (huv : form lam u v = 0) :
    form lam (u-c•v) (u-c•v) = form lam u u := by
  rw [form_sub_left,form_sub_right,form_sub_right,form_smul_right,
    form_smul_left,form_smul_left,form_smul_right,hv,huv,← form_symm lam u v,huv]
  ring

variable (hb : Bornology.IsBounded Ω)

lemma mean_eq (u : H1 Ω) : mean hb u = ∫ x in Ω, value u x := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  change inner ℝ ((memLp_const (1 : ℝ)).toLp _) (value u) = _
  rw [L2Inner.toLp_left]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]

lemma form_self_integral (lam : ℝ) (u : H1 Ω) :
    form lam u u = (∫ x in Ω, ‖grad u x‖^2) - lam * (∫ x in Ω, (value u x)^2) := by
  simp only [form,L2.inner_def,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma form_nonneg {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (u : H1 Ω) (hm : mean hb u = 0) : 0 ≤ form lam u u := by
  rw [form_self_integral]
  exact sub_nonneg.mpr (lower_rayleigh hle (hasH1Gradient u) ((mean_eq hb u).symm.trans hm))

lemma form_zero_euler {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hvol : 0 < (volume Ω).toReal) (u : H1 Ω) (hm : mean hb u = 0)
    (hz : form lam u u = 0) (v : H1 Ω) : form lam u v = 0 := by
  rw [form_self_integral,sub_eq_zero] at hz
  have he := lower_euler hle hb hvol (hasH1Gradient u) (hasH1Gradient v)
    ((mean_eq hb u).symm.trans hm) hz
  rw [form,L2.inner_def,L2.inner_def]
  simp only [RCLike.inner_apply,RCLike.conj_to_real]
  rw [show (fun x => value v x * value u x) = (fun x => value u x * value v x) by funext; ring,he,sub_self]

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
section PlaneWaveFormsCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.PlaneWaves
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
include hΩ hb

lemma cosH1_pair (lam : ℝ) (k l : Plane) :
    H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb l) =
      inner ℝ k l * (∫ x in Ω, sine k x * sine l x) -
        lam * (∫ x in Ω, cosine k x * cosine l x) := by
  unfold cosH1 H1.form
  rw [H1.grad_toH1,H1.grad_toH1,H1.value_toH1,H1.value_toH1,
    L2Inner.toLp_pair,L2Inner.toLp_pair]
  congr 1
  · rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [gradient_cosine,gradient_cosine,real_inner_smul_left,real_inner_smul_right]
      ring
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply,RCLike.conj_to_real]; ring

lemma sinH1_pair (lam : ℝ) (k l : Plane) :
    H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb l) =
      inner ℝ k l * (∫ x in Ω, cosine k x * cosine l x) -
        lam * (∫ x in Ω, sine k x * sine l x) := by
  unfold sinH1 H1.form
  rw [H1.grad_toH1,H1.grad_toH1,H1.value_toH1,H1.value_toH1,
    L2Inner.toLp_pair,L2Inner.toLp_pair]
  congr 1
  · rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [gradient_sine,gradient_sine,real_inner_smul_left,real_inner_smul_right]
      ring
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply,RCLike.conj_to_real]; ring

lemma pair_sum (lam : ℝ) (k l : Plane) :
    H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb l) +
      H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb l) =
        (inner ℝ k l - lam) * (∫ x in Ω, cosine (k-l) x) := by
  rw [cosH1_pair,sinH1_pair]
  have he : (∫ x in Ω, cosine (k-l) x) =
      (∫ x in Ω, cosine k x * cosine l x) + (∫ x in Ω, sine k x * sine l x) := by
    have hc : Integrable (fun x => cosine k x * cosine l x) (volume.restrict Ω) :=
      (cosine_memLp hb k).integrable_mul (cosine_memLp hb l)
    have hs : Integrable (fun x => sine k x * sine l x) (volume.restrict Ω) :=
      (sine_memLp hb k).integrable_mul (sine_memLp hb l)
    rw [← integral_add hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [cosine,sine,inner_sub_left,Real.cos_sub]
  rw [he]
  ring

lemma self_sum {lam : ℝ} {k : Plane} (hk : ‖k‖^2 = lam) :
    H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb k) +
      H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb k) = 0 := by
  rw [pair_sum,real_inner_self_eq_norm_sq,hk,sub_self,zero_mul]

lemma cosH1_dirichlet_pair {lam : ℝ} {k : Plane} (hk : ‖k‖^2 = lam) (φ : H10 hΩ) :
    H1.form lam (cosH1 hΩ hb k) φ.val = 0 := by
  unfold H1.form cosH1
  rw [H1.grad_toH1,H1.value_toH1]
  change inner ℝ ((cosine_h1_gradient hΩ hb k).2.1.toLp _) (H10.grad hΩ φ) -
    lam * inner ℝ ((cosine_h1_gradient hΩ hb k).1.toLp _) (H10.value hΩ φ) = 0
  rw [H10.helmholtz_pair hΩ (cosine_smooth k).contDiffOn
    (cosine_h1_gradient hΩ hb k).1 (cosine_h1_gradient hΩ hb k).2.1
    (fun x _ => by rw [laplacian_cosine,hk]),sub_self]

lemma sinH1_dirichlet_pair {lam : ℝ} {k : Plane} (hk : ‖k‖^2 = lam) (φ : H10 hΩ) :
    H1.form lam (sinH1 hΩ hb k) φ.val = 0 := by
  unfold H1.form sinH1
  rw [H1.grad_toH1,H1.value_toH1]
  change inner ℝ ((sine_h1_gradient hΩ hb k).2.1.toLp _) (H10.grad hΩ φ) -
    lam * inner ℝ ((sine_h1_gradient hΩ hb k).1.toLp _) (H10.value hΩ φ) = 0
  rw [H10.helmholtz_pair hΩ (sine_smooth k).contDiffOn
    (sine_h1_gradient hΩ hb k).1 (sine_h1_gradient hΩ hb k).2.1
    (fun x _ => by rw [laplacian_sine,hk]),sub_self]

end StrictHotSpots.PlaneWaves
end PlaneWaveFormsCombinedLayer

section LpZeroExtensionCombinedLayer
open MeasureTheory Set Filter
open scoped ENNReal
namespace StrictHotSpots.LpZeroExtension
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set α} (hs : MeasurableSet s)

lemma linearIsometry_ae (f : Lp E 2 (μ.restrict s)) :
    linearIsometry hs f =ᵐ[μ] s.indicator f := lift_ae hs f

lemma linearIsometry_toLp {f : α → E} (hf : MemLp f 2 μ)
    (hsupp : Function.support f ⊆ s) :
    linearIsometry hs ((hf.mono_measure Measure.restrict_le_self).toLp f) = hf.toLp f := by
  apply Lp.ext
  exact (linearIsometry_ae hs _).trans
    (((ae_eq_restrict_iff_indicator_ae_eq hs).mp
      (hf.mono_measure Measure.restrict_le_self).coeFn_toLp).trans
      (by rw [Set.indicator_eq_self.mpr hsupp]; exact hf.coeFn_toLp.symm))

end StrictHotSpots.LpZeroExtension
end LpZeroExtensionCombinedLayer

section H10ZeroExtensionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.H10
private lemma inner_smul_reverse (v w : Plane) (c : ℝ) :
    inner ℝ (c • v) w = inner ℝ w v * c := by
  rw [real_inner_smul_left, real_inner_comm, mul_comm]

variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma zeroValue_test (f : smoothTestSpace Ω)
    (hf : MemLp (f : Plane → ℝ) 2 (volume : Measure Plane)) :
    zeroValue hΩ (smoothTestToH10 hΩ f) = hf.toLp f := by
  exact LpZeroExtension.linearIsometry_toLp hΩ.measurableSet hf
    ((subset_tsupport _).trans f.property.2.2)

lemma zeroGrad_test (f : smoothTestSpace Ω)
    (hf : MemLp (gradient (f : Plane → ℝ)) 2 (volume : Measure Plane)) :
    zeroGrad hΩ (smoothTestToH10 hΩ f) = hf.toLp (gradient (f : Plane → ℝ)) := by
  apply LpZeroExtension.linearIsometry_toLp hΩ.measurableSet hf
  intro x hx
  by_contra hn
  apply hx
  rw [gradient,fderiv_of_notMem_tsupport ℝ (fun hh => hn (f.property.2.2 hh)),map_zero]

lemma inner_zeroValue_toLp {a : Plane → ℝ} (ha : MemLp a 2 (volume : Measure Plane))
    (u : H10 hΩ) : inner ℝ (ha.toLp a) (zeroValue hΩ u) = ∫ x, zeroValue hΩ u x * a x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply, RCLike.conj_to_real, hx]

lemma inner_zeroGrad_toLp {φ : Plane → ℝ} (e : Plane)
    (ha : MemLp (fun x => φ x • e) 2 (volume : Measure Plane))
    (u : H10 hΩ) : inner ℝ (ha.toLp _) (zeroGrad hΩ u) =
      ∫ x, inner ℝ (zeroGrad hΩ u x) e * φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp] with x hx
  change inner ℝ ((ha.toLp _) x) ((zeroGrad hΩ u) x) = _
  calc
    _ = inner ℝ (φ x • e) ((zeroGrad hΩ u) x) := congrArg (fun z : Plane => inner ℝ z ((zeroGrad hΩ u) x)) hx
    _ = _ := inner_smul_reverse e ((zeroGrad hΩ u) x) (φ x)



lemma zero_hasH1Gradient (u : H10 hΩ) :
    HasH1Gradient univ (zeroValue hΩ u) (zeroGrad hΩ u) := by
  refine ⟨by simpa using Lp.memLp (zeroValue hΩ u),by simpa using Lp.memLp (zeroGrad hΩ u),?_⟩
  intro φ hφ hc _ e
  have hdf : MemLp (fun x => fderiv ℝ φ x e) 2 (volume : Measure Plane) := by
    simpa using test_derivative_memLp (Ω := univ) hφ hc e
  have hvec : MemLp (fun x => φ x • e) 2 (volume : Measure Plane) := by
    simpa using test_vector_memLp (Ω := univ) hφ hc e
  let a : Lp ℝ 2 (volume : Measure Plane) := hdf.toLp _
  let b : Lp Plane 2 (volume : Measure Plane) := hvec.toLp _
  let L : H10 hΩ →L[ℝ] ℝ := ((innerSL ℝ a).comp (zeroValue hΩ)) +
    ((innerSL ℝ b).comp (zeroGrad hΩ))
  have hL (v : H10 hΩ) : L v =
      (∫ x, zeroValue hΩ v x * fderiv ℝ φ x e) +
      (∫ x, inner ℝ (zeroGrad hΩ v x) e * φ x) := by
    change inner ℝ a (zeroValue hΩ v) + inner ℝ b (zeroGrad hΩ v) = _
    exact congrArg₂ (· + ·) (inner_zeroValue_toLp hΩ hdf v) (inner_zeroGrad_toLp hΩ e hvec v)
  have hdense : ∀ f : smoothTestSpace Ω, L (smoothTestToH10 hΩ f) = 0 := by
    intro f
    have hmf : MemLp (f : Plane → ℝ) 2 (volume : Measure Plane) := by
      simpa using test_memLp (Ω := univ) f.property.1 f.property.2.1
    have hmg : MemLp (gradient (f : Plane → ℝ)) 2 (volume : Measure Plane) := by
      simpa using test_gradient_memLp (Ω := univ) f.property.1 f.property.2.1
    rw [hL,zeroValue_test hΩ f hmf,zeroGrad_test hΩ f hmg]
    have hi := (HasH1Gradient.test isOpen_univ f.property.1 f.property.2.1).2.2
      φ hφ hc (subset_univ _) e
    simp only [Measure.restrict_univ] at hi
    have hv : (∫ x, hmf.toLp (f : Plane → ℝ) x * fderiv ℝ φ x e) = ∫ x, (f : Plane → ℝ) x * fderiv ℝ φ x e := by
      apply integral_congr_ae
      filter_upwards [hmf.coeFn_toLp] with x hx using congrArg (fun t => t * fderiv ℝ φ x e) hx
    have hg : (∫ x, inner ℝ (hmg.toLp _ x) e * φ x) =
      ∫ x, inner ℝ (gradient (f : Plane → ℝ) x) e * φ x := by
      apply integral_congr_ae
      filter_upwards [hmg.coeFn_toLp] with x hx using congrArg (fun t => inner ℝ t e * φ x) hx
    rw [hv,hg,hi,neg_add_cancel]
  have hz : L u = 0 := isClosed_property (dense_smoothTestToH10 hΩ)
    (isClosed_eq L.continuous continuous_const) hdense u
  rw [hL] at hz
  simp only [Measure.restrict_univ]
  linarith

end StrictHotSpots.H10
end H10ZeroExtensionCombinedLayer

section HelmholtzUCPCombinedLayer






open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

lemma secondOrder_zero {f g A B : ℝ → ℂ} {a b K : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ x ∈ Ico a b, HasDerivAt f (g x) x)
    (hdg : ∀ x ∈ Ico a b, HasDerivAt g (A x * f x + B x * g x) x)
    (ha : f a = 0) (hga : g a = 0)
    (hK : ∀ x ∈ Ico a b, 1 + ‖A x‖ + ‖B x‖ ≤ K) :
    ∀ x ∈ Icc a b, f x = 0 ∧ g x = 0 := by
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun x => (f x,g x)) (f' := fun x => (g x,A x*f x+B x*g x))
    (hf.prodMk hg) (fun x hx => ((hdf x hx).prodMk (hdg x hx)).hasDerivWithinAt)
    (by simp [ha,hga]) (K := K) ?_
  · intro x hx
    have h := hz x hx
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro x hx
    rw [Prod.norm_def, Prod.norm_def]
    apply max_le
    · have hk : 1 ≤ K := by
        have := hK x hx
        linarith [norm_nonneg (A x), norm_nonneg (B x)]
      exact (le_max_right _ _).trans (le_mul_of_one_le_left (by positivity) hk)
    · apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      calc
        _ ≤ ‖A x‖ * max ‖f x‖ ‖g x‖ + ‖B x‖ * max ‖f x‖ ‖g x‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
        _ = (‖A x‖ + ‖B x‖) * max ‖f x‖ ‖g x‖ := (add_mul _ _ _).symm
        _ ≤ K * max ‖f x‖ ‖g x‖ := by
          gcongr
          have := hK x hx
          linarith

lemma continuous_eq_zero_of_fourierCoeff {T : ℝ} [Fact (0 < T)]
    {f : AddCircle T → ℂ} (hf : Continuous f) (h : ∀ n : ℤ, fourierCoeff f n = 0) :
    f = 0 := by
  let F : C(AddCircle T,ℂ) := ⟨f,hf⟩
  have he : fourierCoeff F = fun _ : ℤ => (0 : ℂ) := funext h
  have hs : Summable (fourierCoeff F) := by rw [he]; exact summable_zero
  funext x
  have hz := has_pointwise_sum_fourier_series_of_summable hs x
  have hz' : HasSum (fun _ : ℤ => (0 : ℂ)) (f x) := by
    simpa only [he, zero_smul] using! hz
  exact hz'.unique hasSum_zero

lemma bilinear_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (e : ℂ) :
    B e e + B (e * I) (e * I) = ‖e‖ ^ 2 • (B 1 1 + B I I) := by
  have he : e = e.re • (1 : ℂ) + e.im • I := by
    simpa only [real_smul, mul_one] using (re_add_im e).symm
  have hei : e * I = (-e.im) • (1 : ℂ) + e.re • I := by
    apply Complex.ext <;> simp
  have hn : (‖e‖ ^ 2 : ℝ) = e.re^2 + e.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc
    _ = B (e.re • 1 + e.im • I) (e.re • 1 + e.im • I) +
        B ((-e.im) • 1 + e.re • I) ((-e.im) • 1 + e.re • I) := by
      exact congrArg₂ (· + ·) (congrArg (fun z => B z z) he)
        (congrArg (fun z => B z z) hei)
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply]
      simp only [real_smul, hn]
      push_cast
      ring


lemma point_eq (a : ℂ) (r θ : ℝ) :
    circleMap a r θ = a + r • direction θ := by simp [direction,circleMap,real_smul]

lemma hasDerivAt_point_radius (a : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t => circleMap a t θ) (direction θ) r := by
  simpa only [point_eq,one_smul,id_eq] using!
    ((hasDerivAt_id r).smul_const (direction θ)).const_add a

lemma hasDerivAt_radial {u : ℂ → ℂ} {a : ℂ} {r θ : ℝ}
    (hu : DifferentiableAt ℝ u (circleMap a r θ)) :
    HasDerivAt (fun t => radial u a t θ) (radialDeriv u a r θ) r :=
  hu.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_point_radius a r θ)

lemma hasDerivAt_radialDeriv {u : ℂ → ℂ} {a : ℂ} {r θ : ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (circleMap a r θ)) :
    HasDerivAt (fun t => radialDeriv u a t θ) (radialSecond u a r θ) r := by
  have hD : HasDerivAt (fun t : ℝ => fderiv ℝ u (circleMap a t θ))
      (fderiv ℝ (fderiv ℝ u) (circleMap a r θ) (direction θ)) r :=
    hu.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_point_radius a r θ)
  have h := hD.clm_apply (hasDerivAt_const r (direction θ))
  simpa only [radialDeriv,radialSecond,map_zero,add_zero] using! h

lemma hasDerivAt_angular {u : ℂ → ℂ} {a : ℂ} {r θ : ℝ}
    (hu : DifferentiableAt ℝ u (circleMap a r θ)) :
    HasDerivAt (radial u a r) (angularDeriv u a r θ) θ :=
  hu.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap a r θ)

lemma hasDerivAt_angularDeriv {u : ℂ → ℂ} {a : ℂ} {r θ : ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (circleMap a r θ)) :
    HasDerivAt (angularDeriv u a r) (angularSecond u a r θ) θ := by
  have h := (hu.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap a r θ)).clm_apply
    ((hasDerivAt_circleMap 0 r θ).mul_const I)
  have he : (circleMap 0 r θ * I) * I = -(r • direction θ) := by
    rw [mul_assoc,I_mul_I,mul_neg_one,point_eq,zero_add]
  simpa only [Function.comp_def,he,map_neg,map_smul,sub_eq_add_neg,
    angularDeriv,angularSecond,radialDeriv] using! h

lemma polar_laplacian (u : ℂ → ℂ) (a : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    radialSecond u a r θ + r⁻¹ • radialDeriv u a r θ +
      (r^2)⁻¹ • angularSecond u a r θ = (Δ u) (circleMap a r θ) := by
  have hrot := bilinear_rotation (fderiv ℝ (fderiv ℝ u) (circleMap a r θ)) (direction θ)
  have hn : ‖direction θ‖ = 1 := by simp [direction]
  rw [hn,one_pow,one_smul] at hrot
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← hrot]
  unfold radialSecond angularSecond radialDeriv
  rw [point_eq (0 : ℂ),zero_add,smul_mul_assoc]
  simp only [map_smul,smul_apply,smul_smul]
  simp only [real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_mul]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp [hrc]
  ring

end StrictHotSpots.Helmholtz
end HelmholtzUCPCombinedLayer

section HelmholtzFourierCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian Interval
namespace StrictHotSpots.Helmholtz


lemma hasDerivAt_intervalIntegral_of_continuousOn {F F' : ℝ → ℝ → ℂ}
    {S : Set ℝ} (hS : IsOpen S) {r : ℝ} (hr : r ∈ S) (a b : ℝ)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ univ))
    (hF' : ContinuousOn (Function.uncurry F') (S ×ˢ univ))
    (hD : ∀ t ∈ S, ∀ θ, HasDerivAt (fun t => F t θ) (F' t θ) t) :
    HasDerivAt (fun t => ∫ θ in a..b, F t θ) (∫ θ in a..b, F' r θ) r := by
  obtain ⟨ε,hε,hεS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hr)
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hsub : Icc (r-δ) (r+δ) ⊆ S := by
    intro x hx
    apply hεS
    rw [Metric.mem_ball,Real.dist_eq]
    rw [abs_lt]
    rcases hx with ⟨hx₁,hx₂⟩
    constructor <;> dsimp [δ] at * <;> linarith
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (hF'.mono (show Icc (r-δ) (r+δ) ×ˢ uIcc a b ⊆ S ×ˢ univ from by
      intro x hx; exact ⟨hsub hx.1,mem_univ _⟩))
  have hc (t : ℝ) (ht : t ∈ S) : Continuous (F t) := by
    rw [← continuousOn_univ]
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ _ => ⟨ht,mem_univ θ⟩)
  have hc' (t : ℝ) (ht : t ∈ S) : Continuous (F' t) := by
    rw [← continuousOn_univ]
    exact hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ _ => ⟨ht,mem_univ θ⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (r-δ) (r+δ)) (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith)) ?_
    ((hc r hr).intervalIntegrable a b) ((hc' r hr).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hS.mem_nhds hr] with t ht
    exact (hc t ht).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun θ hθ t ht => hC (t,θ) ⟨ht,uIoc_subset_uIcc hθ⟩)
  · exact Filter.Eventually.of_forall (fun θ _ t ht => hD t (hsub ht) θ)

lemma hasDerivAt_weight (n : ℤ) (θ : ℝ) :
    HasDerivAt (weight n) (-I*n*weight n θ) θ := by
  have he : (-2 * (Real.pi:ℂ) * I * n / (2*Real.pi) : ℂ) = -I*n := by
    have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  simpa only [weight,Complex.ofReal_mul,Complex.ofReal_ofNat,he] using!
    hasDerivAt_fourier_neg (2*Real.pi) n θ

lemma continuous_weight (n : ℤ) : Continuous (weight n) :=
  continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_weight n θ).continuousAt

lemma weight_periodic (n : ℤ) : Function.Periodic (weight n) (2*Real.pi) := by
  intro θ
  simp [weight]

lemma integral_weight_deriv {f f' : ℝ → ℂ} (n : ℤ)
    (hdf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in 0..2*Real.pi, weight n θ * f' θ) =
      (I*n) * ∫ θ in 0..2*Real.pi, weight n θ * f θ := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun θ _ => hasDerivAt_weight n θ) (fun θ _ => hdf θ)
    (((continuous_const.mul (continuous_weight n))).intervalIntegrable 0 (2*Real.pi))
    (hf'.intervalIntegrable 0 (2*Real.pi))
  have hp0 : f (2*Real.pi) = f 0 := by simpa using hp 0
  have hw0 : weight n (2*Real.pi) = weight n 0 := by simpa using weight_periodic n 0
  rw [hp0,hw0,sub_self,zero_sub] at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  simpa only [neg_mul,neg_neg,mul_assoc] using h

lemma circleMap_mem_ball {a : ℂ} {r R θ : ℝ} (hr : r ∈ Ioo 0 R) :
    circleMap a r θ ∈ ball a R := by
  rw [mem_ball,dist_eq_norm]
  have h : circleMap a r θ - a = circleMap 0 r θ := by simp [circleMap]
  rw [h,norm_circleMap_zero,abs_of_pos hr.1]
  exact hr.2

lemma continuous_jointCircleMap (a : ℂ) :
    Continuous (fun p : ℝ × ℝ => circleMap a p.1 p.2) := by
  unfold circleMap
  fun_prop

lemma continuous_direction : Continuous direction := by
  exact continuous_circleMap 0 1

lemma radial_regular {u : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z) :
    ContinuousOn (Function.uncurry (radial u a)) (Ioo 0 R ×ˢ univ) ∧
    ContinuousOn (Function.uncurry (radialDeriv u a)) (Ioo 0 R ×ˢ univ) ∧
    ContinuousOn (Function.uncurry (radialSecond u a)) (Ioo 0 R ×ˢ univ) := by
  have hp := continuous_jointCircleMap a
  have hdir : Continuous (fun p : ℝ × ℝ => direction p.2) := continuous_direction.comp continuous_snd
  have h1 (p : ℝ × ℝ) (h : p ∈ Ioo 0 R ×ˢ univ) :
      ContDiffAt ℝ 1 (fderiv ℝ u) (circleMap a p.1 p.2) :=
    (hu _ (circleMap_mem_ball h.1)).fderiv_right (by norm_num)
  have h2 (p : ℝ × ℝ) (h : p ∈ Ioo 0 R ×ˢ univ) :
      ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ u)) (circleMap a p.1 p.2) :=
    (h1 p h).fderiv_right (by norm_num)
  refine ⟨?_,?_,?_⟩
  · intro p hp'
    exact ((hu _ (circleMap_mem_ball (θ := p.2) hp'.1)).continuousAt.comp (f := fun q : ℝ × ℝ => circleMap a q.1 q.2) hp.continuousAt).continuousWithinAt
  · intro p hp'
    exact (((h1 p hp').continuousAt.comp (f := fun q : ℝ × ℝ => circleMap a q.1 q.2) hp.continuousAt).clm_apply hdir.continuousAt).continuousWithinAt
  · intro p hp'
    exact ((((h2 p hp').continuousAt.comp (f := fun q : ℝ × ℝ => circleMap a q.1 q.2) hp.continuousAt).clm_apply
      hdir.continuousAt).clm_apply hdir.continuousAt).continuousWithinAt

lemma angular_regular {u : ℂ → ℂ} {a : ℂ} {r R : ℝ}
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z) (hr : r ∈ Ioo 0 R) :
    Continuous (radial u a r) ∧ Continuous (angularDeriv u a r) ∧
      Continuous (angularSecond u a r) := by
  have hp := continuous_circleMap a r
  have hv : Continuous (fun θ => circleMap 0 r θ * I) := by fun_prop
  have hd : Continuous (radialDeriv u a r) := by
    rw [← continuousOn_univ]
    exact (radial_regular hu).2.1.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hr,mem_univ _⟩)
  have h1 (θ : ℝ) : ContDiffAt ℝ 1 (fderiv ℝ u) (circleMap a r θ) :=
    (hu _ (circleMap_mem_ball hr)).fderiv_right (by norm_num)
  have h2 (θ : ℝ) : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ u)) (circleMap a r θ) :=
    (h1 θ).fderiv_right (by norm_num)
  refine ⟨continuous_iff_continuousAt.mpr ?_,continuous_iff_continuousAt.mpr ?_,
    continuous_iff_continuousAt.mpr ?_⟩
  · intro θ
    exact (hu _ (circleMap_mem_ball hr)).continuousAt.comp hp.continuousAt
  · intro θ
    exact ((h1 θ).continuousAt.comp hp.continuousAt).clm_apply hv.continuousAt
  · intro θ
    exact ((((h2 θ).continuousAt.comp hp.continuousAt).clm_apply hv.continuousAt).clm_apply
      hv.continuousAt).sub ((show ContinuousAt (fun _ : ℝ => r) θ from continuousAt_const).smul hd.continuousAt)

lemma hasDerivAt_coeff {u : ℂ → ℂ} {a : ℂ} {r R : ℝ} (n : ℤ)
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (coeff u a n) (coeffDeriv u a n r) r := by
  have h := radial_regular hu
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radial u a t θ)
    (F' := fun t θ => weight n θ * radialDeriv u a t θ) isOpen_Ioo hr 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).continuousOn.mul h.1)
    (((continuous_weight n).comp continuous_snd).continuousOn.mul h.2.1)
    (fun t ht θ => (hasDerivAt_radial
      ((hu _ (circleMap_mem_ball ht)).differentiableAt (by norm_num))).const_mul _)

lemma hasDerivAt_coeffDeriv {u : ℂ → ℂ} {a : ℂ} {r R : ℝ} (n : ℤ)
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (coeffDeriv u a n) (coeffSecond u a n r) r := by
  have h := radial_regular hu
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radialDeriv u a t θ)
    (F' := fun t θ => weight n θ * radialSecond u a t θ) isOpen_Ioo hr 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).continuousOn.mul h.2.1)
    (((continuous_weight n).comp continuous_snd).continuousOn.mul h.2.2)
    (fun t ht θ => (hasDerivAt_radialDeriv
      (((hu _ (circleMap_mem_ball ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num))).const_mul _)

lemma radial_periodic (u : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    Function.Periodic (radial u a r) (2*Real.pi) :=
  (periodic_circleMap a r).comp u

lemma angularDeriv_periodic (u : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    Function.Periodic (angularDeriv u a r) (2*Real.pi) := by
  intro θ
  simp only [angularDeriv,periodic_circleMap a r θ,periodic_circleMap 0 r θ]

lemma integral_weight_angularSecond {u : ℂ → ℂ} {a : ℂ} {r R : ℝ} (n : ℤ)
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z) (hr : r ∈ Ioo 0 R) :
    (∫ θ in 0..2*Real.pi, weight n θ * angularSecond u a r θ) =
      -(n : ℂ)^2 * coeff u a n r := by
  have hd : ∀ θ, HasDerivAt (radial u a r) (angularDeriv u a r θ) θ :=
    fun θ => hasDerivAt_angular ((hu _ (circleMap_mem_ball hr)).differentiableAt (by norm_num))
  have hdd : ∀ θ, HasDerivAt (angularDeriv u a r) (angularSecond u a r θ) θ :=
    fun θ => hasDerivAt_angularDeriv
      (((hu _ (circleMap_mem_ball hr)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num))
  rw [integral_weight_deriv n hdd (angular_regular hu hr).2.2 (angularDeriv_periodic u a r),
    integral_weight_deriv n hd (angular_regular hu hr).2.1 (radial_periodic u a r)]
  change I * n * (I * n * coeff u a n r) = _
  calc
    _ = Complex.I^2 * (n : ℂ)^2 * coeff u a n r := by ring
    _ = _ := by rw [I_sq]; ring

lemma coeff_ode {u : ℂ → ℂ} {a : ℂ} {r R μ : ℝ} (n : ℤ)
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z)
    (hPDE : ∀ z ∈ ball a R, (Δ u) z = -μ • u z) (hr : r ∈ Ioo 0 R) :
    coeffSecond u a n r = ((n : ℂ)^2 / (r : ℂ)^2 - μ) * coeff u a n r +
      (-(r : ℂ)⁻¹) * coeffDeriv u a n r := by
  have hc := radial_regular hu
  have hcr (F : ℝ → ℝ → ℂ)
      (h : ContinuousOn (Function.uncurry F) (Ioo 0 R ×ˢ univ)) : Continuous (F r) := by
    rw [← continuousOn_univ]
    exact h.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hr,mem_univ _⟩)
  have h1 := (continuous_weight n).mul (hcr _ hc.2.1)
  have h2 := (continuous_weight n).mul (hcr _ hc.2.2)
  have hA := (continuous_weight n).mul (angular_regular hu hr).2.2
  have he (θ : ℝ) :
      weight n θ * radialSecond u a r θ + (r : ℂ)⁻¹ * (weight n θ * radialDeriv u a r θ) +
        ((r : ℂ)^2)⁻¹ * (weight n θ * angularSecond u a r θ) =
      -(μ : ℂ) * (weight n θ * radial u a r θ) := by
    have hp := polar_laplacian u a hr.1.ne' θ
    rw [hPDE _ (circleMap_mem_ball hr)] at hp
    simp only [real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_neg] at hp
    change _ = -(μ : ℂ) * radial u a r θ at hp
    linear_combination weight n θ * hp
  have hI := intervalIntegral.integral_congr (μ := volume) (a := 0) (b := 2*Real.pi) (fun θ _ => he θ)
  have hi1 : IntervalIntegrable
      (fun θ => (r : ℂ)⁻¹ * (weight n θ * radialDeriv u a r θ)) volume 0 (2*Real.pi) :=
    (continuous_const.mul h1).intervalIntegrable _ _
  have hiA : IntervalIntegrable
      (fun θ => ((r : ℂ)^2)⁻¹ * (weight n θ * angularSecond u a r θ)) volume 0 (2*Real.pi) :=
    (continuous_const.mul hA).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun θ => weight n θ * radialSecond u a r θ) volume 0 (2*Real.pi) :=
    h2.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi2.add hi1) hiA,
    intervalIntegral.integral_add hi2 hi1] at hI
  simp only [intervalIntegral.integral_const_mul] at hI
  rw [integral_weight_angularSecond n hu hr] at hI
  change coeffSecond u a n r + (r : ℂ)⁻¹ * coeffDeriv u a n r +
    ((r : ℂ)^2)⁻¹ * (-(n:ℂ)^2 * coeff u a n r) = -(μ:ℂ)*coeff u a n r at hI
  rw [div_eq_mul_inv]
  linear_combination hI

end StrictHotSpots.Helmholtz
end HelmholtzFourierCombinedLayer

section HelmholtzContinuationCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

local instance twoPiPosCont : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma circleFunction_coe (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) :
    circleFunction u a r (θ : AddCircle (2*Real.pi)) = radial u a r θ := by
  simp only [circleFunction,AddCircle.homeomorphCircle'_apply_mk,Circle.coe_exp,radial,circleMap,real_smul]

lemma continuous_circleFunction {u : ℂ → ℂ} {a : ℂ} {r R : ℝ}
    (hu : ∀ z ∈ ball a R, ContinuousAt u z) (hr : r ∈ Ioo 0 R) :
    Continuous (circleFunction u a r) := by
  let f : AddCircle (2*Real.pi) → ℂ := fun s => a + r • (AddCircle.homeomorphCircle' s : ℂ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hm (s : AddCircle (2*Real.pi)) : f s ∈ ball a R := by
    rw [mem_ball,dist_eq_norm]
    dsimp only [f]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,Circle.norm_coe,mul_one]
    exact hr.2
  exact continuous_iff_continuousAt.mpr fun s => (hu _ (hm s)).comp hf.continuousAt

lemma coeff_zero_implies_radial_zero {u : ℂ → ℂ} {a : ℂ} {r R : ℝ}
    (hu : ∀ z ∈ ball a R, ContinuousAt u z) (hr : r ∈ Ioo 0 R)
    (h : ∀ n, coeff u a n r = 0) : ∀ θ, radial u a r θ = 0 := by
  have hz : circleFunction u a r = 0 := continuous_eq_zero_of_fourierCoeff
    (continuous_circleFunction hu hr) (fun n => by
      rw [fourierCoeff_eq_intervalIntegral _ _ 0]
      simp only [zero_add,circleFunction_coe,smul_eq_mul]
      change (1/(2*Real.pi)) • coeff u a n r = 0
      rw [h n,smul_zero])
  intro θ
  rw [← circleFunction_coe]
  exact congrFun hz (θ : AddCircle (2*Real.pi))

lemma coeff_zero_of_ball_zero {u : ℂ → ℂ} {a : ℂ} {r ε : ℝ}
    (hzero : ∀ z ∈ ball a ε, u z = 0) (hr : r ∈ Ioo 0 ε) (n : ℤ) :
    coeff u a n r = 0 := by
  unfold coeff radial
  simp only [hzero _ (circleMap_mem_ball hr),mul_zero,intervalIntegral.integral_zero]

lemma coeffDeriv_zero_of_ball_zero {u : ℂ → ℂ} {a : ℂ} {r ε : ℝ}
    (hzero : ∀ z ∈ ball a ε, u z = 0) (hr : r ∈ Ioo 0 ε) (n : ℤ) :
    coeffDeriv u a n r = 0 := by
  have hd (z : ℂ) (hz : z ∈ ball a ε) : fderiv ℝ u z = 0 := by
    have he : u =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with x hx
      exact hzero x hx
    simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)
  unfold coeffDeriv radialDeriv
  simp only [hd _ (circleMap_mem_ball hr),zero_apply,mul_zero,
    intervalIntegral.integral_zero]

lemma coeff_zero_on_ball {u : ℂ → ℂ} {a : ℂ} {R ε μ : ℝ}
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z)
    (hPDE : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hε : 0 < ε) (hzero : ∀ z ∈ ball a ε, u z = 0)
    (n : ℤ) : ∀ r ∈ Ioo 0 R, coeff u a n r = 0 := by
  intro r hr
  by_cases hrε : r < ε
  · exact coeff_zero_of_ball_zero hzero ⟨hr.1,hrε⟩ n
  have hεr : ε ≤ r := le_of_not_gt hrε
  let r₀ := ε/2
  have hr₀ : r₀ ∈ Ioo 0 ε := ⟨half_pos hε,half_lt_self hε⟩
  have hi : Icc r₀ r ⊆ Ioo 0 R := by
    intro x hx
    exact ⟨hr₀.1.trans_le hx.1,hx.2.trans_lt hr.2⟩
  let A : ℝ → ℂ := fun x => (n : ℂ)^2 / (x : ℂ)^2 - μ
  let B : ℝ → ℂ := fun x => -(x : ℂ)⁻¹
  have hA : ContinuousOn A (Icc r₀ r) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div continuousOn_const ((Complex.continuous_ofReal.comp continuous_id).continuousOn.pow 2)
    intro x hx
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hi hx).1.ne')
  have hB : ContinuousOn B (Icc r₀ r) := by
    apply ContinuousOn.neg
    exact (Complex.continuous_ofReal.comp continuous_id).continuousOn.inv₀
      (fun x hx => Complex.ofReal_ne_zero.mpr (hi hx).1.ne')
  obtain ⟨CA,hCA⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨CB,hCB⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  exact (secondOrder_zero
    (fun x hx => (hasDerivAt_coeff n hu (hi hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_coeffDeriv n hu (hi hx)).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_coeff n hu (hi (Ico_subset_Icc_self hx)))
    (fun x hx => by
      rw [← coeff_ode n hu hPDE (hi (Ico_subset_Icc_self hx))]
      exact hasDerivAt_coeffDeriv n hu (hi (Ico_subset_Icc_self hx)))
    (coeff_zero_of_ball_zero hzero hr₀ n) (coeffDeriv_zero_of_ball_zero hzero hr₀ n)
    (K := 1+CA+CB) (fun x hx => by
      have h1 := hCA x (Ico_subset_Icc_self hx)
      have h2 := hCB x (Ico_subset_Icc_self hx)
      dsimp [A,B] at *
      linarith) r ⟨hr₀.2.le.trans hεr,le_rfl⟩).1


lemma zero_on_ball_of_zero_on_small_ball {u : ℂ → ℂ} {a : ℂ} {R ε μ : ℝ}
    (hu : ∀ z ∈ ball a R, ContDiffAt ℝ 2 u z)
    (hPDE : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hε : 0 < ε) (hzero : ∀ z ∈ ball a ε, u z = 0) :
    ∀ z ∈ ball a R, u z = 0 := by
  intro z hz
  by_cases hza : z = a
  · subst z
    exact hzero a (mem_ball_self hε)
  let r := ‖z-a‖
  have hr : r ∈ Ioo 0 R := ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza),by simpa [r,mem_ball,dist_eq_norm] using hz⟩
  have he : circleMap a r (arg (z-a)) = z := by
    simp only [circleMap,r,norm_mul_exp_arg_mul_I]
    abel
  have hv := coeff_zero_implies_radial_zero (fun z hz => (hu z hz).continuousAt) hr
    (fun n => coeff_zero_on_ball hu hPDE hε hzero n r hr) (arg (z-a))
  simpa only [radial,he] using hv



end StrictHotSpots.Helmholtz
end HelmholtzContinuationCombinedLayer

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

lemma smoothen_zero {u : ℂ → ℂ} {a : ℂ} {ε : ℝ}
    (hzero : ∀ᵐ z ∂volume, z ∈ ball a ε → u z = 0)
    {n : ℕ} (hn : (mollifier n).rOut < ε/2)
    {x : ℂ} (hx : x ∈ ball a (ε/2)) : smoothen u n x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with z hz
  change (mollifier n).normed volume (x-z) • u z = 0
  by_cases hza : z ∈ ball a ε
  · rw [hz hza,smul_zero]
  · suffices hh : (mollifier n).normed volume (x-z) = 0 by rw [hh,zero_smul]
    by_contra hh
    have hh' : x-z ∈ ball (0:ℂ) (mollifier n).rOut := by
      rwa [← (mollifier n).support_normed_eq (μ := volume)]
    have hzdist : dist z x < (mollifier n).rOut := by
      simpa [mem_ball,dist_eq_norm,norm_sub_rev] using hh'
    rw [mem_ball] at hx hza
    have ht := dist_triangle z x a
    linarith

lemma weak_zero_on_ball {u : ℂ → ℂ} {a : ℂ} {R ε μ : ℝ}
    (hu : LocallyIntegrable u volume) (hPDE : WeakEquation (ball a R) μ u)
    (hε : 0 < ε) (hzero : ∀ᵐ z ∂volume, z ∈ ball a ε → u z = 0) :
    ∀ᵐ z ∂volume, z ∈ ball a R → u z = 0 := by
  filter_upwards [smoothen_tendsto hu] with z hz
  intro hzR
  have hzdist : 0 < R-dist z a := sub_pos.mpr hzR
  have hs : ∀ᶠ n in atTop, smoothen u n z = 0 := by
    filter_upwards [(tendsto_order.1 mollifier_radius_tendsto).2 (min (ε/2) (R-dist z a))
      (lt_min (half_pos hε) hzdist)] with n hn
    have hn₁ : (mollifier n).rOut < ε/2 := hn.trans_le (min_le_left _ _)
    have hn₂ : z ∈ ball a (R-(mollifier n).rOut) := by
      rw [mem_ball]
      have := hn.trans_le (min_le_right _ _)
      linarith
    exact zero_on_ball_of_zero_on_small_ball
      (fun y _ => ((smoothen_contDiff hu n).of_le (show (2 : ℕ∞ω) ≤ ∞ by decide)).contDiffAt)
      (fun y hy => smoothen_PDE hu hPDE n hy)
      (half_pos hε) (fun y hy => smoothen_zero hzero hn₁ hy) z hn₂
  exact tendsto_nhds_unique hz (tendsto_const_nhds.congr' (hs.mono (fun _ he => he.symm)))


lemma WeakEquation.mono {U V : Set ℂ} {μ : ℝ} {u : ℂ → ℂ}
    (h : WeakEquation U μ u) (hVU : V ⊆ U) : WeakEquation V μ u :=
  fun φ hφ hc hs => h φ hφ hc (hs.trans hVU)




theorem weak_uniqueContinuation {u : ℂ → ℂ} {U : Set ℂ} {μ : ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hu : LocallyIntegrable u volume) (hPDE : WeakEquation U μ u)
    (hzero : ∃ a ∈ U, ∃ ε > 0, ∀ᵐ z ∂volume, z ∈ ball a ε → u z = 0) :
    ∀ᵐ z ∂volume, z ∈ U → u z = 0 := by
  let S : Set ℂ := {a | ∃ ε > 0, ∀ᵐ z ∂volume, z ∈ ball a ε → u z = 0}
  have hopen : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    intro a ha
    obtain ⟨ε,hε,hza⟩ := ha
    refine ⟨ε/2,half_pos hε,?_⟩
    intro b hb
    refine ⟨ε/2,half_pos hε,?_⟩
    filter_upwards [hza] with z hz
    intro hzb
    apply hz
    rw [mem_ball] at hb hzb ⊢
    have ht := dist_triangle z b a
    linarith
  have hne : (U ∩ S).Nonempty := hzero
  have hcl : closure S ∩ U ⊆ S := by
    intro x hx
    obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx.2)
    obtain ⟨a,ha,hxa⟩ := Metric.mem_closure_iff.mp hx.1 (R/4) (by positivity)
    have hax : dist a x < R/4 := by simpa [dist_comm] using hxa
    obtain ⟨ε,hε,hza⟩ := ha
    have hbig : ball a (R/2) ⊆ U := by
      intro z hz
      apply hball
      rw [mem_ball] at hz ⊢
      have ht := dist_triangle z a x
      linarith
    have hzbig := weak_zero_on_ball hu (hPDE.mono hbig) hε hza
    refine ⟨R/4,by positivity,?_⟩
    filter_upwards [hzbig] with z hz
    intro hzx
    apply hz
    rw [mem_ball] at hzx ⊢
    have ht := dist_triangle z x a
    linarith
  have hsub := hconn.subset_of_closure_inter_subset hopen hne hcl
  choose ε hε he using fun x : U => hsub x.2
  obtain ⟨T,hT,hcover⟩ := (IsLindelof.of_coe (s := U)).elim_nhds_subcover'
    (fun x hx => ball x (ε ⟨x,hx⟩)) (fun x hx => ball_mem_nhds x (hε ⟨x,hx⟩))
  have ha : ∀ᵐ z ∂volume, ∀ x ∈ T, z ∈ ball (x:ℂ) (ε x) → u z = 0 :=
    (eventually_countable_ball hT).mpr (fun x _ => he x)
  filter_upwards [ha] with z hz
  intro hzU
  obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp (hcover hzU)
  exact hz x hx hy

end StrictHotSpots.Helmholtz
end HelmholtzWeakCombinedLayer

section GapWeakPDECombinedLayer
open scoped Laplacian ContDiff InnerProductSpace
open Set MeasureTheory Filter
namespace StrictHotSpots
open Laplacian

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

section


open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots


lemma weak_laplacian_test {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hu : HasH1Gradient Ω u g) {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, u x * Δ φ x) = -(∫ x in Ω, inner ℝ (g x) (gradient φ x)) := by
  have hd (i : Fin 2) : ContDiff ℝ ∞ (directionalDerivative φ (planeBasis i)) :=
    hφ.fderiv_right (by simp) |>.clm_apply contDiff_const
  have hdc (i : Fin 2) : HasCompactSupport (directionalDerivative φ (planeBasis i)) :=
    hc.fderiv_apply ℝ (planeBasis i)
  have hds (i : Fin 2) : tsupport (directionalDerivative φ (planeBasis i)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (planeBasis i)).trans hs
  have hi (i : Fin 2) : Integrable (fun x => u x * directionalDerivative
      (directionalDerivative φ (planeBasis i)) (planeBasis i) x) (volume.restrict Ω) :=
    hu.1.integrable_mul (test_derivative_memLp (hd i) (hdc i) (planeBasis i))
  have hj (i : Fin 2) : Integrable (fun x => inner ℝ (g x) (planeBasis i) *
      directionalDerivative φ (planeBasis i) x) (volume.restrict Ω) :=
    (hu.2.1.inner_const (planeBasis i)).integrable_mul (test_derivative_memLp hφ hc (planeBasis i))
  have hp (x : Plane) : inner ℝ (g x) (gradient φ x) =
      ∑ i : Fin 2, inner ℝ (g x) (planeBasis i) * directionalDerivative φ (planeBasis i) x := by
    rw [← planeBasis.sum_inner_mul_inner]
    simp only [directionalDerivative, inner_gradient_right,conj_trivial]
  simp_rw [laplacian_eq_sum_directional isOpen_univ hφ.contDiffOn (mem_univ _),
    Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [show ∀ i : Fin 2, (∫ x in Ω, u x * directionalDerivative
      (directionalDerivative φ (planeBasis i)) (planeBasis i) x) =
      -(∫ x in Ω, inner ℝ (g x) (planeBasis i) * directionalDerivative φ (planeBasis i) x)
    from fun i => hu.2.2 _ (hd i) (hdc i) (hds i) (planeBasis i)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hj i)]
  simp_rw [← hp]

end StrictHotSpots
end

section


open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots

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



theorem planeWeak_uniqueContinuation {Ω : Set Plane} {μ : ℝ} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hu : IntegrableOn u Ω)
    (hp : PlaneWeakEquation Ω μ u)
    (hz : ∃ a ∈ Ω, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ ball a ε → u x = 0) :
    ∀ᵐ x ∂volume, x ∈ Ω → u x = 0 := by
  have hconn : IsPreconnected (coord ⁻¹' Ω) :=
    coord.toHomeomorph.isPreconnected_preimage.mpr hc
  have hz' : ∃ a ∈ coord ⁻¹' Ω, ∃ ε > 0,
      ∀ᵐ z ∂volume, z ∈ ball a ε → complexExtension Ω u z = 0 := by
    obtain ⟨a,ha,ε,hε,hz⟩ := hz
    refine ⟨coord.symm a,by simpa,ε,hε,?_⟩
    filter_upwards [coord.measurePreserving.quasiMeasurePreserving.ae hz] with z hz
    intro hzb
    have hd : coord z ∈ ball a ε := by
      simpa only [mem_ball,← coord.dist_map z (coord.symm a),coord.apply_symm_apply] using hzb
    by_cases hzm : coord z ∈ Ω
    · simp only [complexExtension,indicator_of_mem hzm,hz hd,Complex.ofReal_zero]
    · simp only [complexExtension,indicator_of_notMem hzm,Complex.ofReal_zero]
  have hh := Helmholtz.weak_uniqueContinuation
    (hΩ.preimage coord.continuous) hconn
    (complexExtension_integrable hΩ.measurableSet hu).locallyIntegrable
    (complexExtension_weak hΩ.measurableSet hp) hz'
  filter_upwards [coord.symm.measurePreserving.quasiMeasurePreserving.ae hh] with x hx
  intro hxm
  have hm : coord.symm x ∈ coord ⁻¹' Ω := by simpa using hxm
  have he := hx hm
  simpa only [complexExtension,coord.apply_symm_apply,indicator_of_mem hxm,Complex.ofReal_eq_zero] using he

end StrictHotSpots
end
end GapWeakPDECombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Dirichlet
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section ZeroLpPairingCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.LpZeroExtension
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : Set α} (hs : MeasurableSet s)

lemma integral_inner (f : Lp E 2 (μ.restrict s)) (g : α → E) :
    (∫ x, inner ℝ (linearIsometry hs f x) (g x) ∂μ) =
      ∫ x in s, inner ℝ (f x) (g x) ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [linearIsometry_ae hs f] with x hx
  rw [hx]
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_mul (f : Lp ℝ 2 (μ.restrict s)) (g : α → ℝ) :
    (∫ x, linearIsometry hs f x * g x ∂μ) = ∫ x in s, f x * g x ∂μ := by
  simpa only [RCLike.inner_apply,RCLike.conj_to_real,mul_comm] using integral_inner hs f g

lemma integrable [IsFiniteMeasure (μ.restrict s)] (f : Lp E 2 (μ.restrict s)) :
    Integrable (linearIsometry hs f : α → E) μ :=
  ((integrable_indicator_iff hs).mpr ((Lp.memLp f).integrable (by norm_num))).congr
    (linearIsometry_ae hs f).symm

end StrictHotSpots.LpZeroExtension
end ZeroLpPairingCombinedLayer

section ZeroLpWeakCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.LpZeroExtension
variable {Ω : Set Plane} (hΩ : IsOpen Ω)
lemma weak_of_neumann (lam : ℝ) (f : Lp ℝ 2 (volume.restrict Ω))
    (g : Lp Plane 2 (volume.restrict Ω))
    (hg : HasH1Gradient univ (linearIsometry hΩ.measurableSet f) (linearIsometry hΩ.measurableSet g))
    (he : ∀ v k, HasH1Gradient Ω v k →
      (∫ x in Ω, inner ℝ (g x) (k x)) = lam * (∫ x in Ω, f x * v x)) :
    PlaneWeakEquation univ lam (linearIsometry hΩ.measurableSet f) := by
  intro φ hφ hc hs
  rw [weak_laplacian_test hg hφ hc hs]
  simp only [Measure.restrict_univ]
  rw [integral_inner hΩ.measurableSet g (gradient φ),integral_mul hΩ.measurableSet f φ,
    he _ _ (HasH1Gradient.test hΩ hφ hc),neg_mul]

lemma zero_of_weak (hb : Bornology.IsBounded Ω) (lam : ℝ)
    (f : Lp ℝ 2 (volume.restrict Ω))
    (hz : PlaneWeakEquation univ lam (linearIsometry hΩ.measurableSet f)) : f = 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hint : IntegrableOn (linearIsometry hΩ.measurableSet f) univ := by
    rw [IntegrableOn,Measure.restrict_univ]
    exact integrable hΩ.measurableSet f
  have hcne : closure Ω ≠ univ := by
    intro hh
    exact (NormedSpace.unbounded_univ ℝ Plane) (hh ▸ hb.closure)
  obtain ⟨a,ha⟩ := (ne_univ_iff_exists_notMem _).mp hcne
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl a ha
  have hzero : ∀ᵐ x ∂volume, x ∈ univ → linearIsometry hΩ.measurableSet f x = 0 :=
    planeWeak_uniqueContinuation isOpen_univ isPreconnected_univ hint hz
      ⟨a,mem_univ a,ε,hε,by
        filter_upwards [linearIsometry_ae hΩ.measurableSet f] with x hx
        intro hxb
        rw [hx,indicator_of_notMem (fun hh => hsub hxb (subset_closure hh))]⟩
  have hzLp : linearIsometry hΩ.measurableSet f = 0 := by
    apply Lp.ext
    have ha : (linearIsometry hΩ.measurableSet f : Plane → ℝ) =ᵐ[volume] (fun _ => 0) :=
      hzero.mono fun _ hx => hx (mem_univ _)
    exact ha.trans (Lp.coeFn_zero _ _ _).symm
  apply (linearIsometry hΩ.measurableSet).injective
  exact hzLp.trans (map_zero _).symm

end StrictHotSpots.LpZeroExtension
end ZeroLpWeakCombinedLayer

section H10NeumannZeroCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)



lemma zero_of_neumann (hb : Bornology.IsBounded Ω) (lam : ℝ) (u : H10 hΩ)
    (he : ∀ v k, HasH1Gradient Ω v k →
      (∫ x in Ω, inner ℝ (grad hΩ u x) (k x)) =
        lam * (∫ x in Ω, value hΩ u x * v x)) : value hΩ u = 0 := by
  exact LpZeroExtension.zero_of_weak hΩ hb lam (value hΩ u)
    (LpZeroExtension.weak_of_neumann hΩ lam (value hΩ u) (grad hΩ u)
      (zero_hasH1Gradient hΩ u) he)

end StrictHotSpots.H10
end H10NeumannZeroCombinedLayer

section StrictGapAlgebraCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots
namespace H1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
lemma mean_corrected (φ v : H1 Ω) (hφ : mean hb φ ≠ 0) :
    mean hb (corrected hb φ v) = 0 := by
  simp only [corrected,map_sub,map_smul,smul_eq_mul]
  field_simp
  ring
lemma corrected_form (lam : ℝ) (φ v : H1 Ω) (hφ : form lam φ φ = 0)
    (hv : form lam v φ = 0) : form lam (corrected hb φ v) (corrected hb φ v) = form lam v v :=
  form_diag_sub _ _ _ _ hφ hv
end H1
namespace PlaneWaves
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)

lemma all_pair_zero {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hvol : 0 < (volume Ω).toReal) (φ : H10 hΩ)
    (he : H1.form lam φ.val φ.val = 0) (hm : H1.mean hb φ.val ≠ 0)
    {k : Plane} (hk : ‖k‖^2 = lam) {l : Plane} (hl : ‖l‖^2 = lam) :
    H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb l) = 0 ∧
      H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb l) = 0 := by
  let c := H1.corrected hb φ.val (cosH1 hΩ hb k)
  let s := H1.corrected hb φ.val (sinH1 hΩ hb k)
  have hmc : H1.mean hb c = 0 := H1.mean_corrected hb _ _ hm
  have hms : H1.mean hb s = 0 := H1.mean_corrected hb _ _ hm
  have hc : H1.form lam c c = H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb k) :=
    H1.corrected_form hb _ _ _ he (cosH1_dirichlet_pair hΩ hb hk φ)
  have hs : H1.form lam s s = H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb k) :=
    H1.corrected_form hb _ _ _ he (sinH1_dirichlet_pair hΩ hb hk φ)
  have hsum := self_sum hΩ hb hk
  have hcn := H1.form_nonneg hb hle c hmc
  have hsn := H1.form_nonneg hb hle s hms
  have hcz : H1.form lam c c = 0 := by linarith
  have hsz : H1.form lam s s = 0 := by linarith
  have hce := H1.form_zero_euler hb hle hvol c hmc hcz (cosH1 hΩ hb l)
  have hse := H1.form_zero_euler hb hle hvol s hms hsz (sinH1 hΩ hb l)
  have hcl : H1.form lam φ.val (cosH1 hΩ hb l) = 0 := by
    rw [H1.form_symm]; exact cosH1_dirichlet_pair hΩ hb hl φ
  have hsl : H1.form lam φ.val (sinH1 hΩ hb l) = 0 := by
    rw [H1.form_symm]; exact sinH1_dirichlet_pair hΩ hb hl φ
  simp only [c,s,H1.corrected,H1.form_sub_left,H1.form_smul_left,hcl,hsl,mul_zero,sub_zero]
    at hce hse
  exact ⟨hce,hse⟩
end PlaneWaves
end StrictHotSpots
end StrictGapAlgebraCombinedLayer

section NearbyFrequenciesCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots.PlaneWaves

lemma frequency_norm_sq (r θ : ℝ) : ‖frequency r θ‖^2 = r^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [frequency,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]
lemma frequency_inner (r θ : ℝ) : inner ℝ (frequency r 0) (frequency r θ) = r^2 * Real.cos θ := by
  simp [frequency,PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,pow_two]
  ring
lemma frequency_continuous (r : ℝ) : Continuous (frequency r) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi_iff.mpr
  intro i
  fin_cases i <;> fun_prop

lemma cosine_integral_continuous {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    Continuous (fun k : Plane => ∫ x in Ω, cosine k x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro k
    exact (cosine_smooth k).continuous.aestronglyMeasurable
  · intro k
    exact Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_cos_le_one _
  · exact integrable_const _
  · exact Eventually.of_forall fun x => Real.continuous_cos.comp (continuous_id.inner continuous_const)



lemma exists_nearby {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (hvol : 0 < (volume Ω).toReal) {lam : ℝ} (hlam : 0 < lam) :
    ∃ k l : Plane, ‖k‖^2 = lam ∧ ‖l‖^2 = lam ∧ inner ℝ k l ≠ lam ∧
      0 < ∫ x in Ω, cosine (k-l) x := by
  let r := Real.sqrt lam
  have hr : r^2 = lam := Real.sq_sqrt hlam.le
  have hc : Continuous (fun θ : ℝ => ∫ x in Ω, cosine (frequency r 0 - frequency r θ) x) :=
    (cosine_integral_continuous hb).comp (continuous_const.sub (frequency_continuous r))
  have h0 : 0 < ∫ x in Ω, cosine (frequency r 0 - frequency r 0) x := by
    simpa [cosine,Measure.real] using hvol
  have he : ∀ᶠ θ in 𝓝 (0 : ℝ), 0 < ∫ x in Ω, cosine (frequency r 0 - frequency r θ) x :=
    hc.continuousAt.eventually (Ioi_mem_nhds h0)
  obtain ⟨δ,hδ,hδ'⟩ := Metric.eventually_nhds_iff.mp he
  let θ := min δ (Real.pi) / 2
  have ht : 0 < θ := by dsimp [θ]; positivity
  have htd : θ < δ := by dsimp [θ]; linarith [min_le_left δ Real.pi]
  have htp : θ < Real.pi := by dsimp [θ]; linarith [min_le_right δ Real.pi,Real.pi_pos]
  refine ⟨frequency r 0,frequency r θ,(frequency_norm_sq _ _).trans hr,
    (frequency_norm_sq _ _).trans hr,?_,hδ' (by simpa [Real.dist_eq,abs_of_pos ht] using htd)⟩
  rw [frequency_inner,hr]
  intro hx
  have hc1 : Real.cos θ = 1 := by nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi ht htp
  nlinarith [Real.sin_sq_add_cos_sq θ]
end StrictHotSpots.PlaneWaves
end NearbyFrequenciesCombinedLayer

section StrictGapCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots
namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma zero_of_form_neumann (hb : Bornology.IsBounded Ω) (lam : ℝ) (φ : H10 hΩ)
    (he : ∀ v : H1 Ω, H1.form lam φ.val v = 0) : value hΩ φ = 0 := by
  apply zero_of_neumann hΩ hb lam φ
  intro v k hv
  have hh := he hv.toH1
  unfold H1.form at hh
  rw [H1.grad_toH1,H1.value_toH1,L2Inner.toLp_right,L2Inner.toLp_right] at hh
  have hf : (∫ x in Ω, inner ℝ (H1.value φ.val x) (v x)) =
      (∫ x in Ω, value hΩ φ x * v x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply,RCLike.conj_to_real]
      exact mul_comm _ _
  rw [hf,sub_eq_zero] at hh
  exact hh




lemma strict_gap (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    {lam : ℝ} (hlam : 0 < lam) (φ : H10 hΩ) (hφ : value hΩ φ ≠ 0)
    (he : ∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
      lam * inner ℝ (value hΩ φ) (value hΩ v)) :
    firstPositiveNeumannValue Ω < lam := by
  by_contra hn
  have hle : lam ≤ firstPositiveNeumannValue Ω := le_of_not_gt hn
  have hvol : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  have hform : H1.form lam φ.val φ.val = 0 := sub_eq_zero.mpr (he φ)
  have hm : H1.mean hb φ.val ≠ 0 := by
    intro hz
    apply hφ
    apply zero_of_form_neumann hΩ hb lam φ
    exact H1.form_zero_euler hb hle hvol φ.val hz hform
  obtain ⟨k,l,hk,hl,hkl,hint⟩ := PlaneWaves.exists_nearby hb hvol hlam
  obtain ⟨hc,hs⟩ := PlaneWaves.all_pair_zero hΩ hb hle hvol φ hform hm hk hl
  have hsum := PlaneWaves.pair_sum hΩ hb lam k l
  rw [hc,hs,zero_add] at hsum
  have hp : (inner ℝ k l - lam) * (∫ x in Ω, PlaneWaves.cosine (k-l) x) = 0 := hsum.symm
  exact hkl (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hint.ne'))

lemma subcritical_oai (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ lam : ℝ, 0 < lam ∧ firstPositiveNeumannValue Ω < lam ∧
      ∀ v : H10 hΩ, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2 := by
  obtain ⟨lam,φ,hl,hφ,hi,he⟩ := minimum hΩ hne hb
  exact ⟨lam,hl,strict_gap hΩ hne hb hl φ hφ he,hi⟩
end H10
end StrictHotSpots
end StrictGapCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.H10.subcritical_oai := @OAI.StrictHotSpots.H10.subcritical_oai
