-- Prove2me | solution 1 for OAI.StrictHotSpots.Helmholtz.plane_representative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:23:19.122996+00:00
-- url     : https://prove2.me/submissions/ba5cb99b-ddcf-4727-8875-a56163a8f537

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

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
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section HelmholtzUCPCombinedLayer






open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

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


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
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



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialHelmholtzUniqueness





noncomputable section
open Set
namespace StrictHotSpots.Helmholtz

lemma radial_ode_zero {f g : ℝ → ℂ} {a : ℂ} {R : ℝ}
    (hR : 0 < R) (hsmall : ‖a‖*R^2 < 1)
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hdf : ∀ r ∈ Icc 0 R, HasDerivAt f (g r) r)
    (hprod : ∀ r ∈ Icc 0 R,
      HasDerivAt (fun r : ℝ => (r:ℂ)*g r) (-(r:ℂ)*a*f r) r)
    (hf0 : f 0=0) (hg0 : g 0=0) : ∀ r ∈ Icc 0 R, f r=0 := by
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) R).Nonempty from ⟨0,le_rfl,hR.le⟩) hf.norm
  let M := ‖f x‖
  have hM : 0 ≤ M := norm_nonneg _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 R) : ‖f t‖ ≤ M := hmax ht
  have hgbound (r : ℝ) (hr : r ∈ Icc 0 R) : ‖g r‖ ≤ ‖a‖*R*M := by
    by_cases hr0 : r=0
    · rw [hr0,hg0,norm_zero]
      positivity
    have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hh := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f:=fun t : ℝ => (t:ℂ)*g t) (f':=fun t => -(t:ℂ)*a*f t)
      (C:=‖a‖*r*M) (a:=0) (b:=r)
      ((Complex.continuous_ofReal.continuousOn.mul hg).mono
        (Icc_subset_Icc le_rfl hr.2))
      (fun t ht => (hprod t ⟨ht.1,ht.2.le.trans hr.2⟩).hasDerivWithinAt)
      (fun t ht => by
        rw [norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg ht.1]
        calc
          t*‖a‖*‖f t‖ ≤ r*‖a‖*M := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _))
              (hbound t ⟨ht.1,ht.2.le.trans hr.2⟩) (norm_nonneg _) (by positivity)
          _ = ‖a‖*r*M := by ring)
      r ⟨hrp.le,le_rfl⟩
    simp only [Complex.ofReal_zero,zero_mul,sub_zero,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hrp.le] at hh
    have hgg : ‖g r‖ ≤ ‖a‖*r*M := by nlinarith
    exact hgg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr.2 (norm_nonneg _)) hM)
  have hh := norm_image_sub_le_of_norm_deriv_right_le_segment hf
    (fun t ht => (hdf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hgbound t (Ico_subset_Icc_self ht)) x hx
  rw [hf0,sub_zero,sub_zero] at hh
  have hzero : M=0 := by
    have hm : M ≤ (‖a‖*R^2)*M := by
      calc
        M ≤ (‖a‖*R*M)*x := hh
        _ ≤ (‖a‖*R*M)*R := mul_le_mul_of_nonneg_left hx.2 (by positivity)
        _ = (‖a‖*R^2)*M := by ring
    nlinarith
  intro r hr
  exact norm_eq_zero.mp (le_antisymm ((hbound r hr).trans_eq hzero) (norm_nonneg _))

end StrictHotSpots.Helmholtz
end
end RadialHelmholtzUniqueness

section ActualInteriorEigenSupport



section HelmholtzCircleMeanActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex Filter
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

lemma radial_regular_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (a : ℂ) :
    Continuous (Function.uncurry (radial u a)) ∧
    Continuous (Function.uncurry (radialDeriv u a)) ∧
    Continuous (Function.uncurry (radialSecond u a)) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by decide)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ u)) := h1.continuous_fderiv (by norm_num)
  have hp := continuous_jointCircleMap a
  have hd : Continuous (fun p : ℝ × ℝ => direction p.2) := continuous_direction.comp continuous_snd
  exact ⟨hu.continuous.comp hp,
    ((hu.continuous_fderiv (by simp)).comp hp).clm_apply hd,
    ((h2.comp hp).clm_apply hd).clm_apply hd⟩

lemma hasDerivAt_coeff_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (a : ℂ) (n : ℤ) (r : ℝ) :
    HasDerivAt (coeff u a n) (coeffDeriv u a n r) r := by
  have h := radial_regular_global hu a
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radial u a t θ)
    (F' := fun t θ => weight n θ * radialDeriv u a t θ) isOpen_univ (mem_univ _) 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).mul h.1).continuousOn
    (((continuous_weight n).comp continuous_snd).mul h.2.1).continuousOn
    (fun t _ θ => (hasDerivAt_radial (hu.differentiable (by simp) _)).const_mul _)

lemma hasDerivAt_coeffDeriv_global {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (a : ℂ) (n : ℤ) (r : ℝ) :
    HasDerivAt (coeffDeriv u a n) (coeffSecond u a n r) r := by
  have h := radial_regular_global hu a
  exact hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun t θ => weight n θ * radialDeriv u a t θ)
    (F' := fun t θ => weight n θ * radialSecond u a t θ) isOpen_univ (mem_univ _) 0 (2*Real.pi)
    (((continuous_weight n).comp continuous_snd).mul h.2.1).continuousOn
    (((continuous_weight n).comp continuous_snd).mul h.2.2).continuousOn
    (fun t _ θ => (hasDerivAt_radialDeriv
      ((hu.fderiv_right (m:=1) (by decide)).differentiable (by norm_num) _)).const_mul _)

lemma weight_zero (θ : ℝ) : weight 0 θ = 1 := by simp [weight]

lemma coeff_center (u : ℂ → ℂ) (a : ℂ) :
    coeff u a 0 0 = (2*Real.pi) • u a := by
  simp [coeff,weight_zero,radial,circleMap]

lemma integral_direction : (∫ θ in (0:ℝ)..2*Real.pi, direction θ) = 0 := by
  have he : direction = fun θ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ)*I := by
    funext θ
    simp [direction,circleMap,Complex.exp_mul_I]
  rw [he,intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal,integral_cos,integral_sin]
    simp
  · exact (Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _
  · exact ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const).intervalIntegrable _ _

lemma coeffDeriv_center (u : ℂ → ℂ) (a : ℂ) : coeffDeriv u a 0 0 = 0 := by
  simp only [coeffDeriv,weight_zero,one_mul,radialDeriv,circleMap,Complex.ofReal_zero,
    zero_mul,add_zero]
  rw [(fderiv ℝ u a).intervalIntegral_comp_comm (continuous_direction.intervalIntegrable _ _),
    integral_direction,map_zero]

lemma coeff_radial_ode {u : ℂ → ℂ} {a : ℂ} {R μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hPDE : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    {r : ℝ} (hr : r ∈ Ico 0 R) :
    HasDerivAt (fun r : ℝ => (r:ℂ)*coeffDeriv u a 0 r)
      (-(r:ℂ)*(μ:ℂ)*coeff u a 0 r) r := by
  have h := ((hasDerivAt_id r).ofReal_comp).mul (hasDerivAt_coeffDeriv_global hu a 0 r)
  have he : (1:ℂ)*coeffDeriv u a 0 r + (r:ℂ)*coeffSecond u a 0 r =
      -(r:ℂ)*(μ:ℂ)*coeff u a 0 r := by
    by_cases hr0 : r=0
    · simp [hr0,coeffDeriv_center]
    have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    rw [coeff_ode 0 (fun _ _ => (hu.of_le (by decide : (2:ℕ∞ω) ≤ ∞)).contDiffAt)
      hPDE ⟨hrp,hr.2⟩]
    simp only [Int.cast_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,zero_sub]
    have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr0
    field_simp
    ring
  simpa only [id_eq,Complex.ofReal_one,he] using! h



lemma circle_mean_comparison {u v : ℂ → ℂ} {a b : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hvp : ∀ z ∈ ball b R, (Δ v) z = -μ • v z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1)
    (hc : u a = v b) : ∀ r ∈ Icc 0 ρ, coeff u a 0 r = coeff v b 0 r := by
  let f := fun r => coeff u a 0 r - coeff v b 0 r
  let g := fun r => coeffDeriv u a 0 r - coeffDeriv v b 0 r
  have hdf (r : ℝ) : HasDerivAt f (g r) r :=
    (hasDerivAt_coeff_global hu a 0 r).sub (hasDerivAt_coeff_global hv b 0 r)
  have hdg (r : ℝ) : DifferentiableAt ℝ g r :=
    ((hasDerivAt_coeffDeriv_global hu a 0 r).sub
      (hasDerivAt_coeffDeriv_global hv b 0 r)).differentiableAt
  have hz := radial_ode_zero (a:=(μ:ℂ)) hρ (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hsmall)
    (continuous_iff_continuousAt.mpr (fun r => (hdf r).continuousAt)).continuousOn
    (continuous_iff_continuousAt.mpr (fun r => (hdg r).continuousAt)).continuousOn
    (fun r _ => hdf r) (fun r hr => ?_) (by simp [f,coeff_center,hc])
    (by simp [g,coeffDeriv_center])
  · intro r hr
    exact sub_eq_zero.mp (hz r hr)
  · have hrR : r ∈ Ico 0 R := ⟨hr.1,hr.2.trans_lt hρR⟩
    have h := (coeff_radial_ode hu hup hrR).sub (coeff_radial_ode hv hvp hrR)
    simpa only [f,g,mul_sub,Pi.sub_apply] using! h

end StrictHotSpots.Helmholtz
end
end HelmholtzCircleMeanActualInteriorLayer


section HelmholtzRadialActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex Filter Function Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz


lemma referenceReal_smooth (k : ℝ) : ContDiff ℝ ∞ (referenceReal k) :=
  ((k • Complex.reCLM).contDiff).cos
lemma referenceSin_smooth (k : ℝ) : ContDiff ℝ ∞ (referenceSin k) :=
  ((k • Complex.reCLM).contDiff).sin
lemma reference_smooth (μ : ℝ) : ContDiff ℝ ∞ (reference μ) :=
  Complex.ofRealCLM.contDiff.comp (referenceReal_smooth _)

lemma fderiv_referenceReal (k : ℝ) (z : ℂ) :
    fderiv ℝ (referenceReal k) z = (-referenceSin k z) • (k • Complex.reCLM) := by
  exact ((k • Complex.reCLM).hasFDerivAt.cos).fderiv
lemma fderiv_referenceSin (k : ℝ) (z : ℂ) :
    fderiv ℝ (referenceSin k) z = (referenceReal k z) • (k • Complex.reCLM) := by
  exact ((k • Complex.reCLM).hasFDerivAt.sin).fderiv

lemma laplacian_referenceReal (k : ℝ) (z : ℂ) :
    Δ (referenceReal k) z = -(k^2)*referenceReal k z := by
  have hc : fderiv ℝ (referenceReal k) = fun y => (-referenceSin k y) • (k • Complex.reCLM) :=
    funext (fderiv_referenceReal k)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [hc, fderiv_smul_const (c := fun y : ℂ => -(referenceSin k y))
      ((referenceSin_smooth k).differentiable (by simp) z).neg (k • Complex.reCLM),
    fderiv_fun_neg,fderiv_referenceSin]
  simp
  ring

lemma laplacian_reference {μ : ℝ} (hμ : 0 ≤ μ) (z : ℂ) :
    Δ (reference μ) z = -μ • reference μ z := by
  have hh : ContDiffAt ℝ 2 (referenceReal (Real.sqrt μ)) z := ((referenceReal_smooth (Real.sqrt μ)).of_le (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt
  change Δ (Complex.ofRealCLM ∘ referenceReal (Real.sqrt μ)) z = _
  rw [hh.laplacian_CLM_comp_left,Function.comp_apply,laplacian_referenceReal,Real.sq_sqrt hμ]
  simp [reference,real_smul]

lemma reference_zero (μ : ℝ) : reference μ 0 = 1 := by
  simp [reference,referenceReal]

lemma coeff_zero_eq_average (f : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    coeff f a 0 r = (2*Real.pi) • circleAverage f a r := by
  simp only [coeff,weight_zero,one_mul,radial,circleAverage_def,smul_smul,
    mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),one_smul]

lemma mean_eq_reference {u : ℂ → ℂ} {a : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hμ : 0 ≤ μ)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1)
    {r : ℝ} (hr : r ∈ Icc 0 ρ) :
    circleAverage u a r = u a * circleAverage (reference μ) 0 r := by
  have hv : ContDiff ℝ ∞ (fun z => u a * reference μ z) := contDiff_const.mul (reference_smooth μ)
  have hvp (z : ℂ) (_hz : z ∈ ball (0:ℂ) R) :
      Δ (fun z => u a * reference μ z) z = -μ • (u a * reference μ z) := by
    change Δ (u a • reference μ) z = _
    rw [InnerProductSpace.laplacian_smul _ ((reference_smooth μ).of_le
      (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt,laplacian_reference hμ]
    simp only [smul_eq_mul,real_smul,Complex.ofReal_neg]
    ring
  have he := circle_mean_comparison hu hv hup hvp hρ hρR hsmall
    (by simp only [reference_zero,mul_one]) r hr
  have hcoeff : coeff (fun z => u a * reference μ z) 0 0 r = u a * coeff (reference μ) 0 0 r := by
    simp only [coeff,weight_zero,one_mul,radial,intervalIntegral.integral_const_mul]
  rw [hcoeff,coeff_zero_eq_average,coeff_zero_eq_average,real_smul,real_smul] at he
  have hpi : ((2*Real.pi : ℝ):ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  apply mul_left_cancel₀ hpi
  linear_combination he

open StrictHotSpots.Weyl



lemma radial_average_helmholtz {u : ℂ → ℂ} {a : ℂ} {R ρ μ : ℝ}
    (hu : ContDiff ℝ ∞ u) (hμ : 0 ≤ μ)
    (hup : ∀ z ∈ ball a R, (Δ u) z = -μ • u z)
    (hρ : 0 < ρ) (hρR : ρ < R) (hsmall : |μ| * ρ^2 < 1) :
    (∫ z, radialBump ρ z • u (a-z)) =
      u a * (∫ z, radialBump ρ z • reference μ (-z)) := by
  rw [← integral_const_mul]
  rw [← Complex.integral_comp_polarCoord_symm,← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump ρ (Complex.polarCoord.symm p) • u (a-Complex.polarCoord.symm p))) =
    ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • (u a * (radialBump ρ (Complex.polarCoord.symm p) • reference μ (-Complex.polarCoord.symm p)))
  have hi₂ := (polar_bump_integrable hρ (reference_smooth μ).continuous (0:ℂ)).const_mul (u a)
  have hi₂' : IntegrableOn (fun p : ℝ × ℝ => p.1 •
      (u a * (radialBump ρ (Complex.polarCoord.symm p) • reference μ (-Complex.polarCoord.symm p))))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    simpa only [zero_sub,mul_smul_comm] using! hi₂
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hρ hu.continuous a),
    setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi₂')]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hpol : ∀ θ, -Complex.polarCoord.symm (r,θ) = circleMap 0 (-r) θ := by
    intro θ
    simpa only [zero_sub] using polar_circle 0 r θ
  simp_rw [radialBump_polar,polar_circle,hpol,integral_smul,integral_const_mul]
  simp_rw [integral_smul]
  by_cases hrρ : r < ρ
  · rw [angle_integral,angle_integral,circleAverage_neg_radius,circleAverage_neg_radius,
      mean_eq_reference hu hμ hup hρ hρR hsmall ⟨hr.le,hrρ.le⟩]
    simp only [mul_smul_comm]
  · have hzero : expNegInvGlue (ρ^2-r^2) = 0 := by
      apply expNegInvGlue.zero_of_nonpos
      have hr' : ρ ≤ r := le_of_not_gt hrρ
      nlinarith
    simp only [hzero,zero_smul,smul_zero,mul_zero]

end StrictHotSpots.Helmholtz
end
end HelmholtzRadialActualInteriorLayer


section HelmholtzRegularityActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz
open StrictHotSpots.Weyl

lemma regularizing_coefficient_pos {μ ρ : ℝ} (hρ : 0 < ρ)
    (hpos : ∀ z ∈ ball (0:ℂ) ρ, 0 < referenceReal (Real.sqrt μ) (-z)) :
    0 < ∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
  have hc : Continuous (fun z => radialBump ρ z * referenceReal (Real.sqrt μ) (-z)) :=
    (radialBump_contDiff ρ).continuous.mul ((referenceReal_smooth _).continuous.comp continuous_neg)
  have hcomp : HasCompactSupport (fun z => radialBump ρ z * referenceReal (Real.sqrt μ) (-z)) :=
    (radialBump_compact hρ.le).mul_right
  have hn (z : ℂ) : 0 ≤ radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
    by_cases hz : z ∈ ball (0:ℂ) ρ
    · exact mul_nonneg (expNegInvGlue.nonneg _) (hpos z hz).le
    · have hz' : ρ ≤ ‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz
      rw [radialBump_zero hρ.le hz',zero_mul]
  apply (integral_pos_iff_support_of_nonneg hn (hc.integrable_of_hasCompactSupport hcomp)).mpr
  apply (measure_ball_pos volume (0:ℂ) hρ).trans_le
  apply measure_mono
  intro z hz
  apply ne_of_gt
  apply mul_pos _ (hpos z hz)
  apply expNegInvGlue.pos_of_pos
  have hz' : ‖z‖ < ρ := by simpa only [mem_ball,dist_zero_right] using hz
  nlinarith [norm_nonneg z]

lemma exists_regularizing_radius (μ : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ |μ| * ρ^2 < 1 ∧
      0 < ∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) := by
  have hw : ∀ᶠ z : ℂ in 𝓝 0, 0 < referenceReal (Real.sqrt μ) (-z) := by
    apply ((referenceReal_smooth _).continuous.comp continuous_neg).continuousAt.eventually
      (eventually_gt_nhds (show (0:ℝ) < referenceReal (Real.sqrt μ) (-(0:ℂ)) by
        simp [referenceReal]))
  obtain ⟨r,hr,hrw⟩ := Metric.eventually_nhds_iff.mp hw
  have he : ∀ᶠ s : ℝ in 𝓝 0, |μ| * s^2 < 1 := by
    have hc : Continuous (fun s : ℝ => |μ| * s^2) := by fun_prop
    exact hc.continuousAt.eventually (eventually_lt_nhds (by simp))
  obtain ⟨ε,hε,hεw⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨ρ,hρ,hρmin⟩ := exists_between (lt_min hR (lt_min hr hε))
  have hρR := hρmin.trans_le (min_le_left _ _)
  have hρr := hρmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρε := hρmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,hρR,hεw (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hρ] using hρε),?_⟩
  apply regularizing_coefficient_pos hρ
  intro z hz
  apply hrw
  exact (mem_ball.mp hz).trans hρr

lemma regularizing_coefficient_eq (μ ρ : ℝ) :
    (∫ z, radialBump ρ z • reference μ (-z)) =
      ((∫ z, radialBump ρ z * referenceReal (Real.sqrt μ) (-z) : ℝ) : ℂ) := by
  simp only [reference,real_smul,← Complex.ofReal_mul,integral_complex_ofReal]



theorem local_representative {u : ℂ → ℂ} {a : ℂ} {R μ : ℝ}
    (hu : LocallyIntegrable u volume) (hR : 0 < R) (hμ : 0 ≤ μ)
    (hpde : WeakEquation (ball a R) μ u) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      ∀ᵐ x ∂volume, x ∈ ball a (R/4) → f x = u x := by
  obtain ⟨ρ,hρ,hρR,hsmall,hc⟩ := exists_regularizing_radius μ (show 0 < R/4 by positivity)
  let φ := radialBump ρ
  let c : ℝ := ∫ z, φ z * referenceReal (Real.sqrt μ) (-z)
  have hc' : 0 < c := hc
  have hφ : ContDiff ℝ ∞ φ := radialBump_contDiff _
  have hcφ : HasCompactSupport φ := radialBump_compact hρ.le
  let v := u ⋆[smulFlip] φ
  have hv : ContDiff ℝ ∞ v := hcφ.contDiff_convolution_right _ hu hφ
  refine ⟨fun x => c⁻¹ • v x,?_,?_⟩
  · simpa only [Pi.smul_apply] using! (contDiff_const (c := c⁻¹)).smul hv
  filter_upwards [smoothen_tendsto hu,smoothen_tendsto hv.continuous.locallyIntegrable] with x hx hxv
  intro hxa
  have he : ∀ᶠ n in atTop, smoothen v n x = c • smoothen u n x := by
    filter_upwards [(tendsto_order.1 mollifier_radius_tendsto).2 (R/2) (by positivity)] with n hn
    have hh : ∀ z ∈ ball x (R/4), Δ (smoothen u n) z = -μ • smoothen u n z := by
      intro z hz
      apply smoothen_PDE hu hpde n
      rw [mem_ball] at hz hxa ⊢
      have ht := dist_triangle z x a
      linarith
    calc
      smoothen v n x = (smoothen u n ⋆[smulFlip] φ) x :=
        (congrFun (convolution_shuffle hu (mollifier n).continuous_normed
          (mollifier n).hasCompactSupport_normed hφ.continuous hcφ) x).symm
      _ = c • smoothen u n x := by
        rw [← convolution_flip]
        change (∫ z, radialBump ρ z • smoothen u n (x-z)) = _
        rw [radial_average_helmholtz (smoothen_contDiff hu n) hμ hh hρ hρR hsmall,
          regularizing_coefficient_eq]
        exact mul_comm _ _
  have ht : Tendsto (fun n => smoothen v n x) atTop (𝓝 (c • u x)) :=
    (hx.const_smul c).congr' (he.mono (fun _ h => h.symm))
  have hvx : v x = c • u x := tendsto_nhds_unique hxv ht
  rw [hvx,smul_smul,inv_mul_cancel₀ hc'.ne',one_smul]



theorem representative {u : ℂ → ℂ} {Ω : Set ℂ} (ho : IsOpen Ω)
    (hu : LocallyIntegrable u volume) {μ : ℝ} (hμ : 0 ≤ μ) (hpde : WeakEquation Ω μ u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume, x ∈ Ω → f x = u x := by
  classical
  have hball (x : Ω) : ∃ R : ℝ, 0 < R ∧ ball (x:ℂ) R ⊆ Ω :=
    Metric.isOpen_iff.mp ho x x.property
  choose R hR hRΩ using hball
  choose f hf hfu using fun x : Ω => local_representative hu (hR x) hμ (hpde.mono (hRΩ x))
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

end StrictHotSpots.Helmholtz
end
end HelmholtzRegularityActualInteriorLayer

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Helmholtz

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



theorem plane_representative_oai {Ω : Set Plane} {u : Plane → ℝ} {μ : ℝ}
    (ho : IsOpen Ω) (hu : IntegrableOn u Ω) (hμ : 0 ≤ μ) (hp : PlaneWeakEquation Ω μ u) :
    ∃ f : Plane → ℝ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume.restrict Ω, f x = u x := by
  obtain ⟨f,hf,hfu⟩ := representative (ho.preimage coord.continuous)
    (complexExtension_integrable ho.measurableSet hu).locallyIntegrable hμ
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

end StrictHotSpots.Helmholtz


end
end ActualInteriorEigenSupport

end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Helmholtz.plane_representative_oai := @OAI.StrictHotSpots.Helmholtz.plane_representative_oai
