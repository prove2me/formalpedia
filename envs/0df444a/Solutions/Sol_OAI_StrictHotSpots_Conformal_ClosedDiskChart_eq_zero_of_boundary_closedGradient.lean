-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:19:11.019651+00:00
-- url     : https://prove2.me/submissions/693dcc67-b4db-4b39-828c-8bcdb01d865b

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
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
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
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

lemma planeWeakEquation_of_euler {Ω : Set Plane} {μ : ℝ} {u : Plane → ℝ} {g : Plane → Plane}
    (hΩ : IsOpen Ω) (hu : HasH1Gradient Ω u g)
    (he : ∀ v k, HasH1Gradient Ω v k →
      (∫ x in Ω, inner ℝ (g x) (k x)) = μ * (∫ x in Ω, u x * v x)) :
    PlaneWeakEquation Ω μ u := by
  intro φ hφ hc hs
  rw [weak_laplacian_test hu hφ hc hs, he _ _ (HasH1Gradient.test hΩ hφ hc), neg_mul]

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
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RiemannBoundaryCompatible

noncomputable section


section SmoothBoundaryGeometryCompatibleLayer

open Set Filter Metric
open scoped Topology ContDiff
namespace StrictHotSpots

lemma SmoothBoundary.exterior_ball_in_neighborhood {Ω B : Set Plane}
    (hs : SmoothBoundary Ω) {p : Plane} (hp : p ∈ frontier Ω)
    (hB : IsOpen B) (hpB : p ∈ B) :
    ∃ a ∈ B, ∃ ε > 0, ball a ε ⊆ Ωᶜ := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hp
  have hdρ : DifferentiableAt ℝ ρ p :=
    ((hρ p hpU).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  obtain ⟨v,hv⟩ : ∃ v, 0 < fderiv ℝ ρ p v := by
    have hn : ∃ v, fderiv ℝ ρ p v ≠ 0 := by
      by_contra hh
      apply hD
      ext v
      simpa using not_exists.mp hh v
    obtain ⟨v,hv⟩ := hn
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact ⟨-v,by rw [map_neg]; linarith⟩
    · exact ⟨v,hv⟩
  have hray := HasFDerivAt.eventually_lt_along_ray hdρ.hasFDerivAt.neg
    (show (-fderiv ℝ ρ p) v < 0 by simpa using hv)
  have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using tendsto_const_nhds.add ((tendsto_id'.mpr
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
  have hbt : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ B := ht (hB.mem_nhds hpB)
  have hut : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ U := ht (hU.mem_nhds hpU)
  obtain ⟨t,htρ,htB,htU⟩ := (hray.and (hbt.and hut)).exists
  have htpos : 0 < ρ (p+t•v) := by simpa only [Pi.neg_apply,hpρ,neg_zero,neg_lt_zero] using htρ
  have hopen : IsOpen (U ∩ {x | 0 < ρ x}) :=
    hρ.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨ε,hε,hεS⟩ := Metric.isOpen_iff.mp hopen (p+t•v) ⟨htU,htpos⟩
  refine ⟨p+t•v,htB,ε,hε,?_⟩
  intro y hy hyΩ
  have hyS := hεS hy
  have hy' : y ∈ Ω ∩ U := ⟨hyΩ,hyS.1⟩
  rw [hlevel] at hy'
  exact lt_asymm (show ρ y < 0 from hy'.1) (show 0 < ρ y from hyS.2)

end StrictHotSpots
end SmoothBoundaryGeometryCompatibleLayer


end
end RiemannBoundaryCompatible

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedBoundaryZeroJet

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c




theorem hasFDerivWithinAt_zero_of_closedGradient_zero {v : Plane → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvc : ContinuousOn v (closure Ω))
    {Y : Plane → Plane} (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ closure Ω) (hz : Y p = 0) :
    HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) p := by
  have hGp := c.inverse_maps_closed hp
  have hYG : Tendsto (fun z => Y (c.F z)) (𝓝[disk] (c.G p)) (𝓝 (0 : Plane)) := by
    have hc := (hY.comp c.continuous_closed c.maps_closed (c.G p) hGp).mono subset_closure
    change Tendsto (Y ∘ c.F) (𝓝[disk] c.G p) (𝓝 (Y (c.F (c.G p)))) at hc
    rw [c.right_inverse p hp,hz] at hc
    exact hc
  have hlim : Tendsto (fun z => fderiv ℝ (c.pullDatum v) z)
      (𝓝[disk] (c.G p)) (𝓝 (0 : Plane →L[ℝ] ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (g := fun z => c.bound * ‖Y (c.F z)‖) (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with z hzD
      have hn : ‖fderiv ℝ (c.pullDatum v) z‖ = ‖gradient (c.pullDatum v) z‖ := by
        simp only [gradient,LinearIsometryEquiv.norm_map]
      rw [hn,c.pullDatum_grad_norm (hv.differentiableOn (by simp)) hzD,
        he (c.diskMap.map_source hzD),c.diskMap_agrees hzD]
      exact mul_le_mul_of_nonneg_right (c.bounded_deriv z (c.source_eq.symm ▸ hzD)) (norm_nonneg _)
    · simpa only [norm_zero,mul_zero] using tendsto_const_nhds.mul hYG.norm
  have hD : HasFDerivWithinAt (c.pullDatum v) (0 : Plane →L[ℝ] ℝ)
      (closure disk) (c.G p) :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv
      ((c.pullDatum_smooth hv).differentiableOn (by simp))
      (convex_ball (0:Plane) 1) diskOpen
      (fun z hzD => (c.pullDatum_continuous hvc z hzD).mono subset_closure) hlim
  have ht : Tendsto c.G (𝓝[closure Ω] p) (𝓝[closure disk] (c.G p)) :=
    c.inverse_lipschitz.continuous.continuousWithinAt.tendsto_nhdsWithin c.inverse_maps_closed
  have hsmall := (hasFDerivWithinAt_iff_isLittleO.mp hD).comp_tendsto ht
  have hbig : (fun x => c.G x-c.G p) =O[𝓝[closure Ω] p] (fun x => x-p) :=
    Asymptotics.IsBigO.of_bound c.InvLip (Eventually.of_forall (fun x => c.inverse_lipschitz.norm_sub_le x p))
  have hh := hsmall.trans_isBigO hbig
  apply hasFDerivWithinAt_iff_isLittleO.mpr
  apply hh.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply,zero_apply,sub_zero,pullDatum,
    c.right_inverse x hx,c.right_inverse p hp]

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedBoundaryZeroJet


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Cauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualBoundaryCauchySupport

section ActualZeroExtensionLayer
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace Laplacian
namespace StrictHotSpots



lemma zeroExtension_hasFDerivAt {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    {x : Plane} (hx : x ∈ B) :
    HasFDerivAt (Ω.indicator u) (Ω.indicator D x) x := by
  classical
  by_cases hxi : x ∈ Ω
  · rw [indicator_of_mem hxi]
    apply ((hD x ⟨hx,subset_closure hxi⟩).hasFDerivAt
      (mem_of_superset (hΩ.mem_nhds hxi) subset_closure)).congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hxi] with y hy
    exact indicator_of_mem hy _
  · rw [indicator_of_notMem hxi]
    by_cases hxc : x ∈ closure Ω
    · have hxf : x ∈ frontier Ω := ⟨hxc,by simpa only [hΩ.interior_eq] using hxi⟩
      have hzx := hz x ⟨hx,hxf⟩
      have heq : EqOn (Ω.indicator u) u (closure Ω ∩ B) := by
        intro y hy
        by_cases hyΩ : y ∈ Ω
        · exact indicator_of_mem hyΩ _
        · rw [indicator_of_notMem hyΩ]
          exact (hz y ⟨hy.2,hy.1,by simpa only [hΩ.interior_eq] using hyΩ⟩).1.symm
      have hh : HasFDerivWithinAt (Ω.indicator u) (0 : Plane →L[ℝ] ℝ) (closure Ω ∩ B) x := by
        rw [← hzx.2]
        exact ((hD x ⟨hx,hxc⟩).mono inter_subset_left).congr heq
          (by rw [indicator_of_notMem hxi,hzx.1])
      have hc : HasFDerivWithinAt (Ω.indicator u) (0 : Plane →L[ℝ] ℝ) (Ωᶜ ∩ B) x := by
        exact (hasFDerivWithinAt_const (𝕜 := ℝ) (s := Ωᶜ ∩ B) (0 : ℝ) x).congr
          (fun y hy => indicator_of_notMem hy.1 _) (indicator_of_notMem hxi _)
      apply (hh.union hc).hasFDerivAt
      apply mem_of_superset (hB.mem_nhds hx)
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact Or.inl ⟨subset_closure hyΩ,hy⟩
      · exact Or.inr ⟨hyΩ,hy⟩
    · apply (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact indicator_of_notMem (fun hyΩ => hy (subset_closure hyΩ)) _

lemma zeroExtension_continuousOn {E : Type*} [NormedAddCommGroup E]
    {Ω B : Set Plane} {f : Plane → E}
    (hf : ContinuousOn f (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, f x = 0) : ContinuousOn (Ω.indicator f) B := by
  classical
  exact ContinuousOn.piecewise hz hf continuousOn_const

lemma weakGradient_of_continuous_derivative {B : Set Plane} {v : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hB : IsOpen B)
    (hv : ∀ x ∈ B, HasFDerivAt v (D x) x) (hD : ContinuousOn D B)
    (hmv : MemLp v 2 (volume.restrict B))
    (hmg : MemLp (fun x => (InnerProductSpace.toDual ℝ Plane).symm (D x)) 2 (volume.restrict B)) :
    HasH1Gradient B v (fun x => (InnerProductSpace.toDual ℝ Plane).symm (D x)) := by
  refine ⟨hmv,hmg,?_⟩
  have hvc : ContinuousOn v B := fun x hx => (hv x hx).continuousAt.continuousWithinAt
  intro φ hφ hc hs e
  have he (x) : inner ℝ ((InnerProductSpace.toDual ℝ Plane).symm (D x)) e = D x e :=
    InnerProductSpace.toDual_symm_apply
  simp_rw [he]
  have hdφ : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : tsupport (fun x => fderiv ℝ φ x e) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  rw [setIntegral_mul_test hds,setIntegral_mul_test hs]
  have hd : Integrable (fun x => fderiv ℝ v x e * φ x) volume := by
    apply (integrable_mul_test hB (hD.clm_apply (continuousOn_const (c := e))) hφ.continuous hc hs).congr
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ B
      · rw [(hv x hx).fderiv]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; simp
  have hEq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hd
    (integrable_mul_test hB hvc hdφ (hc.fderiv_apply ℝ e) hds)
    (integrable_mul_test hB hvc hφ.continuous hc hs)
    (fun x hx => (hv x (hs hx)).differentiableAt)
    (fun x _ => hφ.differentiable (by simp) x)
  rw [hEq]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : x ∈ B
    · rw [(hv x hx).fderiv]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; simp

end StrictHotSpots

namespace StrictHotSpots

lemma zeroExtension_H1 {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hDc : ContinuousOn D (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    (hu : HasH1Gradient Ω u (gradient u)) :
    HasH1Gradient B (Ω.indicator u) (Ω.indicator (gradient u)) := by
  classical
  let d (x : Plane) := (InnerProductSpace.toDual ℝ Plane).symm (Ω.indicator D x)
  have hd : d =ᵐ[volume.restrict B] Ω.indicator (gradient u) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    by_cases hxΩ : x ∈ Ω
    · have hdu := (hD x ⟨hx,subset_closure hxΩ⟩).hasFDerivAt
        (mem_of_superset (hΩ.mem_nhds hxΩ) subset_closure)
      simp only [d,indicator_of_mem hxΩ,gradient,hdu.fderiv]
    · simp only [d,indicator_of_notMem hxΩ,map_zero]
  have hmv : MemLp (Ω.indicator u) 2 (volume.restrict B) :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hu.1).mono_measure Measure.restrict_le_self
  have hmg : MemLp (Ω.indicator (gradient u)) 2 (volume.restrict B) :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hu.2.1).mono_measure Measure.restrict_le_self
  have hh := weakGradient_of_continuous_derivative hB
    (fun x hx => zeroExtension_hasFDerivAt hΩ hB hD hz hx)
    (zeroExtension_continuousOn hDc (fun x hx => (hz x hx).2)) hmv ((memLp_congr_ae hd).mpr hmg)
  refine ⟨hmv,hmg,?_⟩
  intro φ hφ hc hs e
  rw [hh.2.2 _ hφ hc hs e]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd] with x hx
  rw [show (InnerProductSpace.toDual ℝ Plane).symm (Ω.indicator D x) =
    Ω.indicator (gradient u) x from hx]

lemma integral_indicator_local {Ω B : Set Plane} (hΩ : MeasurableSet Ω)
    {f : Plane → ℝ} (hf : ∀ x ∉ B, f x = 0) :
    (∫ x in B, Ω.indicator f x) = ∫ x in Ω, f x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,integral_indicator hΩ]
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ,hf x hx]
  · rw [indicator_of_notMem hxΩ]

lemma zeroExtension_weakEquation {Ω B : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hh : HasH1Gradient B (Ω.indicator u) (Ω.indicator (gradient u))) :
    PlaneWeakEquation B (firstPositiveNeumannValue Ω) (Ω.indicator u) := by
  classical
  intro φ hφ hc hs
  rw [weak_laplacian_test hh hφ hc hs]
  have hgφ (x : Plane) (hx : x ∉ B) : gradient φ x = 0 := by
    unfold gradient
    rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ φ)
      (fun h => hx (hs (tsupport_fderiv_subset ℝ h))),map_zero]
  have h1 : (fun x => inner ℝ (Ω.indicator (gradient u) x) (gradient φ x)) =
      Ω.indicator (fun x => inner ℝ (gradient u x) (gradient φ x)) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,inner_zero_left]
  have h2 : (fun x => Ω.indicator u x * φ x) = Ω.indicator (fun x => u x * φ x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,zero_mul]
  rw [h1,h2,integral_indicator_local hΩ.measurableSet
    (fun x hx => by rw [hgφ x hx,inner_zero_right]),
    integral_indicator_local hΩ.measurableSet
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]),
    hu.2.2.2 φ (gradient φ) (HasH1Gradient.test hΩ hφ hc),neg_mul]




theorem interior_eigenfunction_zero_of_boundary_jet {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hcΩ : IsPreconnected Ω)
    (hbΩ : Bornology.IsBounded Ω) (hB : IsOpen B) (hcB : IsPreconnected B)
    (hbB : Bornology.IsBounded B) (hu : InInteriorNeumannEigenspace Ω u)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hDc : ContinuousOn D (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    (hin : (B ∩ Ω).Nonempty)
    (hout : ∃ a ∈ B, ∃ ε > 0, ball a ε ⊆ Ωᶜ) :
    EqOn u 0 Ω := by
  classical
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hbB.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hbΩ.measure_lt_top.ne
  have hh := zeroExtension_H1 hΩ hB hD hDc hz hu.2.1
  have hW := zeroExtension_weakEquation hΩ hu hh
  have hext : ∀ᵐ x ∂volume, x ∈ B → Ω.indicator u x = 0 := by
    apply planeWeak_uniqueContinuation hB hcB (hh.1.integrable (by norm_num)) hW
    obtain ⟨a,ha,ε,hε,hs⟩ := hout
    refine ⟨a,ha,ε,hε,Eventually.of_forall fun x hx => ?_⟩
    exact indicator_of_notMem (hs hx) _
  have hu0 : ∀ᵐ x ∂volume, x ∈ Ω → u x = 0 := by
    apply planeWeak_uniqueContinuation hΩ hcΩ (hu.2.1.1.integrable (by norm_num))
      (planeWeakEquation_of_euler hΩ hu.2.1 hu.2.2.2)
    obtain ⟨a,ha⟩ := hin
    obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp (hB.inter hΩ) a ha
    refine ⟨a,ha.2,ε,hε,?_⟩
    filter_upwards [hext] with x hx hxball
    have hm := hs hxball
    simpa only [indicator_of_mem hm.2] using hx hm.1
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩ.measurableSet).mpr hu0) hΩ
    hu.1.continuousOn continuousOn_const

end StrictHotSpots

end
end ActualZeroExtensionLayer
end ActualBoundaryCauchySupport

section ClosedEigenLocalRank

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c



theorem eq_zero_of_boundary_closedGradient_oai (hΩ : AdmissibleDomain Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
    (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ frontier Ω) {U : Set Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hz : ∀ x ∈ U ∩ frontier Ω, v x = 0 ∧ Y x = 0) : EqOn v 0 Ω := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU p hpU
  let D : Plane → Plane →L[ℝ] ℝ := fun x => InnerProductSpace.toDual ℝ Plane (Y x)
  apply interior_eigenfunction_zero_of_boundary_jet hΩ.2.1
    hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected hΩ.2.2.1
    isOpen_ball (convex_ball p ε).isPreconnected isBounded_ball hv (D := D)
  · intro x hx
    by_cases hxi : x ∈ Ω
    · have hd := (hv.differentiableAt hΩ.2.1 hxi).hasFDerivAt.hasFDerivWithinAt (s := closure Ω)
      have hh : fderiv ℝ v x = D x := by
        change fderiv ℝ v x = InnerProductSpace.toDual ℝ Plane (Y x)
        rw [← he hxi]
        exact (InnerProductSpace.toDual ℝ Plane).apply_symm_apply _ |>.symm
      rwa [hh] at hd
    · have hxf : x ∈ frontier Ω := ⟨hx.2,by simpa only [hΩ.2.1.interior_eq] using hxi⟩
      have hh := (hz x ⟨hεU hx.1,hxf⟩).2
      have hd := c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.2 hh
      simpa only [D,hh,map_zero] using hd
  · exact ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn hY).mono inter_subset_right
  · intro x hx
    have hh := hz x ⟨hεU hx.1,hx.2⟩
    exact ⟨hh.1,by simp only [D,hh.2,map_zero]⟩
  · obtain ⟨x,hx,hxp⟩ := Metric.mem_closure_iff.mp hp.1 ε hε
    exact ⟨x,by simpa only [mem_ball,dist_comm] using hxp,hx⟩
  · exact hΩ.2.2.2.2.exterior_ball_in_neighborhood hp isOpen_ball (mem_ball_self hε)
end Conformal.ClosedDiskChart


end StrictHotSpots
end
end ClosedEigenLocalRank



end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient_oai
