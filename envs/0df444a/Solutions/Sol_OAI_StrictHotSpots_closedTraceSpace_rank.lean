-- Prove2me | solution 1 for OAI.StrictHotSpots.closedTraceSpace_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:45:52.607991+00:00
-- url     : https://prove2.me/submissions/f7113b57-aac3-46e1-9d6c-1dc8f00a1ed8

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_CircleSigns_disk_family_finrank_le_two
import Theorems.Thm_OAI_StrictHotSpots_InteriorBoundarySign_exists_boundary_pos

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



lemma minimizer_euler_mean_zero {Ω : Set Plane} {u v : Plane → ℝ}
    {g k : Plane → Plane} (hb : Bornology.IsBounded Ω)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0) (hmv : (∫ x in Ω, v x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hvar (t : ℝ) := rayleigh_inequality_all (hu.add (hv.smul t)) (by
    show (∫ x in Ω, u x + t * v x) = 0
    rw [integral_add hui (hvi.const_mul t), integral_const_mul, hmu, hmv]
    ring)
  have hpoly : ∀ t : ℝ, 0 ≤
      ((∫ x in Ω, ‖k x‖ ^ 2) - firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2)) * (t * t) +
      (2 * ((∫ x in Ω, inner ℝ (g x) (k x)) -
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x))) * t + 0 := by
    intro t
    have ht := hvar t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
    rw [integral_norm_add_smul_sq hu.2.1 hv.2.1 t,
      integral_sq_add_mul hu.1 hv.1 t, he] at ht
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg ((∫ x in Ω, inner ℝ (g x) (k x)) -
    firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x))]



lemma minimizer_euler {Ω : Set Plane} {u v : Plane → ℝ} {g k : Plane → Plane}
    (hb : Bornology.IsBounded Ω) (hvol : 0 < (volume Ω).toReal)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x) := by
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
  have hh := minimizer_euler_mean_zero hb hu hw hmu hm he
  have hi : (∫ x in Ω, u x * (v x - c)) = (∫ x in Ω, u x * v x) := by
    simp only [mul_sub]
    have huv : Integrable (fun x => u x * v x) (volume.restrict Ω) := hu.1.integrable_mul hv.1
    rw [integral_sub huv (hui.mul_const c),
      integral_mul_const, hmu, zero_mul, sub_zero]
  rwa [hi] at hh


end StrictHotSpots
end MainVariationalCombinedLayer


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
-- module Solutions.OAIQ3_Hot.HotSpots_Trace
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section NodalRestrictionWeightedCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Nodal

variable {Ω U : Set Plane} {u : Plane → ℝ}

lemma positive_component_frontier_zero (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (a : Plane) {x : Plane} (hx : x ∈ frontier (connectedComponentIn (Ω ∩ {x | 0 < u x}) a) ∩ Ω) : u x = 0 := by
  let P := Ω ∩ {x | 0 < u x}
  let U := connectedComponentIn P a
  have hP : IsOpen P := positive_set_open hΩ hu
  have hU : IsOpen U := hP.connectedComponentIn
  have hxc : x ∈ closure U := hx.1.1
  have hxU : x ∉ U := by
    have hh : x ∉ interior U := hx.1.2
    simpa only [hU.interior_eq] using hh
  have hux : ContinuousAt u x := (hu x hx.2).continuousAt (hΩ.mem_nhds hx.2)
  have hnonneg : 0 ≤ u x := by
    by_contra h
    have hneg : u x < 0 := lt_of_not_ge h
    have hn : {y | u y < 0} ∈ 𝓝 x := hux.eventually (gt_mem_nhds hneg)
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hn
    obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hyneg : u y < 0 := he (by simpa [mem_ball,dist_comm] using hd)
    have hypos : 0 < u y := (connectedComponentIn_subset P a hy).2
    linarith
  apply le_antisymm _ hnonneg
  by_contra h
  have hpos : 0 < u x := lt_of_not_ge h
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds ⟨hx.2,hpos⟩)
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hxc ε hε
  have hyball : y ∈ ball x ε := by simpa [mem_ball,dist_comm] using hd
  have hbsub : ball x ε ⊆ connectedComponentIn P y :=
    (convex_ball x ε).isPreconnected.subset_connectedComponentIn hyball he
  rw [← connectedComponentIn_eq hy] at hbsub
  exact hxU (hbsub (mem_ball_self hε))

lemma positive_component_hasH1Gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hH : HasH1Gradient Ω u (gradient u)) (a : Plane) :
    HasH1Gradient Ω ((connectedComponentIn (Ω ∩ {x | 0 < u x}) a).indicator u)
      ((connectedComponentIn (Ω ∩ {x | 0 < u x}) a).indicator (gradient u)) := by
  apply hasH1Gradient_indicator hΩ hu hH (positive_set_open hΩ hu.continuousOn).connectedComponentIn
  · exact fun x hx => positive_component_frontier_zero hΩ hu.continuousOn a hx
  · intro x hx
    exact (connectedComponentIn_subset _ a hx).2

end StrictHotSpots.Nodal
end NodalRestrictionWeightedCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedChartTopology

noncomputable section
open Set Metric
open scoped Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma complex_maps_disk {z : ℂ} (hz : z ∈ ball 0 1) : c.F (complexIso z) ∈ Ω := by
  have hx : complexIso z ∈ disk := by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hz
  rw [← c.diskMap_agrees hx]
  exact c.diskMap.map_source hx

lemma complex_maps_closed {z : ℂ} (hz : z ∈ closedBall 0 1) : c.F (complexIso z) ∈ closure Ω := by
  apply c.maps_closed
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),mem_closedBall_zero_iff,
    LinearIsometryEquiv.norm_map] using hz

lemma complex_inverse_disk {x : Plane} (hx : x ∈ Ω) : complexIso.symm (c.G x) ∈ ball 0 1 := by
  have hh := c.diskMap.map_target hx
  change c.diskMap.symm x ∈ disk at hh
  rw [c.diskMap_inverse_agrees hx] at hh
  simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hh

lemma complex_inverse_image (S : Set Plane) (hs : S ⊆ Ω) :
    (fun x => complexIso.symm (c.G x)) '' S = ball 0 1 ∩ (fun z => c.F (complexIso z)) ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨c.complex_inverse_disk (hs hx),?_⟩
    simpa only [mem_preimage,LinearIsometryEquiv.apply_symm_apply,c.right_inverse x (subset_closure (hs hx))] using hx
  · rintro ⟨hz,hx⟩
    refine ⟨c.F (complexIso z),hx,?_⟩
    have hd : complexIso z ∈ closure disk := by
      exact subset_closure (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hz)
    change complexIso.symm (c.G (c.F (complexIso z))) = z
    rw [c.left_inverse _ (c.source_eq.symm ▸ hd),LinearIsometryEquiv.symm_apply_apply]

lemma connected_complex_pull {v : Plane → ℝ} {P : Set ℝ}
    (hcon : IsConnected (Ω ∩ v ⁻¹' P)) :
    IsConnected (ball (0:ℂ) 1 ∩ (fun z => v (c.F (complexIso z))) ⁻¹' P) := by
  have hh := hcon.image (fun x => complexIso.symm (c.G x))
    (complexIso.symm.continuous.comp c.inverse_lipschitz.continuous).continuousOn
  rw [c.complex_inverse_image _ inter_subset_left] at hh
  convert hh using 1
  ext z
  constructor
  · rintro ⟨hz,hv⟩
    exact ⟨hz,c.complex_maps_disk hz,hv⟩
  · rintro ⟨hz,_,hv⟩
    exact ⟨hz,hv⟩


end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedChartTopology


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenAlgebra

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace StrictHotSpots

lemma closedEigenJet_eq_zero_of_eqOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {Y : Plane → Plane} (hv : ContinuousOn v (closure Ω))
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hz : EqOn v 0 Ω) : closedEigenJet Ω v Y = 0 := by
  have hzc := hz.of_subset_closure hv continuousOn_const subset_closure (Subset.refl _)
  have hgz : EqOn Y 0 Ω := by
    intro x hx
    rw [← he hx]
    unfold gradient
    rw [(show v =ᶠ[𝓝 x] 0 from eventually_of_mem (ho.mem_nhds hx) (fun y hy => hz hy)).fderiv_eq]
    simp
  have hgc := hgz.of_subset_closure hY continuousOn_const subset_closure (Subset.refl _)
  exact Prod.ext (funext fun x => hzc x.property) (funext fun x => hgc x.property)


lemma closedEigenJet_nonzero_interior {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {Y : Plane → Plane} (hv : ContinuousOn v (closure Ω))
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hn : closedEigenJet Ω v Y ≠ 0) : ∃ x ∈ Ω, v x ≠ 0 := by
  by_contra! h
  exact hn (closedEigenJet_eq_zero_of_eqOn ho hv hY he h)

end StrictHotSpots
end
end ClosedEigenAlgebra

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorNodal

noncomputable section NodalVariationalInteriorLayer
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.InteriorNodal
open StrictHotSpots.Nodal

lemma minimizer_zero_of_open_zero {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hb : Bornology.IsBounded Ω)
    (hv : 0 < (volume Ω).toReal) (hu : HasH1Gradient Ω u g)
    (hm : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖^2) = firstPositiveNeumannValue Ω * (∫ x in Ω, (u x)^2))
    (hz : ∃ a ∈ Ω, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ ball a ε → u x = 0) :
    u =ᵐ[volume.restrict Ω] 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hi : IntegrableOn u Ω := hu.1.integrable (by norm_num)
  have hp := planeWeakEquation_of_euler hΩ hu (fun v k hvk =>
    minimizer_euler hb hv hu hvk hm he)
  exact (ae_restrict_iff' hΩ.measurableSet).mpr (planeWeak_uniqueContinuation hΩ hc hi hp hz)

lemma integral_indicator_pos {Ω U : Set Plane} {u : Plane → ℝ}
    (_hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hU : IsOpen U)
    (hs : U ⊆ Ω) (hne : U.Nonempty) (hc : ContinuousOn u Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hp : ∀ x ∈ U, 0 < u x) :
    0 < ∫ x in Ω, U.indicator u x := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hi := (hu.indicator hU.measurableSet).integrable (by norm_num : 1 ≤ (2:ENNReal))
  have hn (x : Plane) : 0 ≤ U.indicator u x := by
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx] using (hp x hx).le
    · simp only [indicator_of_notMem hx,le_refl]
  have hnn : 0 ≤ ∫ x in Ω, U.indicator u x := integral_nonneg hn
  by_contra hf
  have hz : (∫ x in Ω, U.indicator u x) = 0 := le_antisymm (le_of_not_gt hf) hnn
  have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
  have he : u =ᵐ[volume.restrict U] 0 := by
    have hh := ae_restrict_of_ae_restrict_of_subset hs hae
    filter_upwards [hh,ae_restrict_mem hU.measurableSet] with x hx hxm
    simpa only [indicator_of_mem hxm,Pi.zero_apply] using hx
  have hh := Measure.eqOn_open_of_ae_eq he hU (hc.mono hs) continuousOn_const
  obtain ⟨x,hx⟩ := hne
  have hp' := hp x hx
  simp only [hh hx,Pi.zero_apply,lt_self_iff_false] at hp'

lemma restriction_energy {Ω U : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u)
    (hH : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u))) :
    (∫ x in Ω, ‖U.indicator (gradient u) x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (U.indicator u x)^2) := by
  have he := hu.2.2.2 _ _ hH
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,real_inner_self_eq_norm_sq]
      · simp only [indicator_of_notMem hx,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),inner_zero_right]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,pow_two]
      · simp only [indicator_of_notMem hx,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

lemma disjoint_indicator_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set Plane} (hd : Disjoint U V) (g : Plane → E) (a b : ℝ) (x : Plane) :
    ‖a • U.indicator g x + b • V.indicator g x‖^2 =
      a^2 * ‖U.indicator g x‖^2 + b^2 * ‖V.indicator g x‖^2 := by
  by_cases hxU : x ∈ U
  · have hxV : x ∉ V := fun hxV => Set.disjoint_left.mp hd hxU hxV
    simp only [indicator_of_mem hxU,indicator_of_notMem hxV,smul_zero,add_zero,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  · simp only [indicator_of_notMem hxU,smul_zero,zero_add,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma disjoint_restriction_combination_energy {Ω U V : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (hd : Disjoint U V)
    (hU : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)))
    (hV : HasH1Gradient Ω (V.indicator u) (V.indicator (gradient u))) (a b : ℝ) :
    (∫ x in Ω, ‖a • U.indicator (gradient u) x + b • V.indicator (gradient u) x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (a * U.indicator u x + b * V.indicator u x)^2) := by
  have ha : (∫ x in Ω, ‖a • U.indicator (gradient u) x + b • V.indicator (gradient u) x‖^2) =
      a^2 * (∫ x in Ω, ‖U.indicator (gradient u) x‖^2) +
        b^2 * (∫ x in Ω, ‖V.indicator (gradient u) x‖^2) := by
    simp_rw [disjoint_indicator_norm_sq hd]
    rw [integral_add (hU.2.1.norm.integrable_sq.const_mul _) (hV.2.1.norm.integrable_sq.const_mul _),
      integral_const_mul,integral_const_mul]
  have hb : (∫ x in Ω, (a * U.indicator u x + b * V.indicator u x)^2) =
      a^2 * (∫ x in Ω, (U.indicator u x)^2) + b^2 * (∫ x in Ω, (V.indicator u x)^2) := by
    have he (x : Plane) := disjoint_indicator_norm_sq hd u a b x
    simp only [smul_eq_mul,Real.norm_eq_abs,sq_abs] at he
    simp_rw [he]
    rw [integral_add (hU.1.integrable_sq.const_mul _) (hV.1.integrable_sq.const_mul _),
      integral_const_mul,integral_const_mul]
  rw [ha,hb,restriction_energy hu hU,restriction_energy hu hV]
  ring

end StrictHotSpots.InteriorNodal

end NodalVariationalInteriorLayer


noncomputable section NodalConnectedInteriorLayer
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.InteriorNodal
open StrictHotSpots.Nodal

lemma gradient_neg_fun (u : Plane → ℝ) : gradient (-u) = -gradient u := by
  funext x
  simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]

lemma eigenfunction_neg {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω (-u) := by
  refine ⟨hu.1.neg,?_,?_,?_⟩
  · simpa only [gradient_neg_fun,neg_one_smul] using hu.2.1.smul (-1)
  · simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  · intro v g hv
    simp only [gradient_neg_fun,Pi.neg_apply,inner_neg_left,neg_mul,integral_neg]
    rw [hu.2.2.2 v g hv]
    ring

lemma eigenfunction_has_negative {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : ∃ x ∈ Ω, u x < 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.2.2.1.measure_lt_top.ne
  by_contra hn
  push Not at hn
  have hae : 0 ≤ᵐ[volume.restrict Ω] u :=
    (ae_restrict_iff' hΩ.2.1.measurableSet).mpr (Eventually.of_forall hn)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hae (hu.2.1.1.integrable (by norm_num))).mp hu.2.2.1
  have hall := Measure.eqOn_open_of_ae_eq hz hΩ.2.1 hu.1.continuousOn continuousOn_const
  obtain ⟨x,hx,hux⟩ := hne
  exact hux (hall hx)

lemma eigenfunction_has_positive {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : ∃ x ∈ Ω, 0 < u x := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  obtain ⟨x,hx,hux⟩ := eigenfunction_has_negative hΩ (eigenfunction_neg hu) hn
  exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_lt_zero] using hux⟩

lemma no_two_positive_regions {Ω U V : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hU : IsOpen U) (hV : IsOpen V) (hsU : U ⊆ Ω) (hsV : V ⊆ Ω)
    (hnU : U.Nonempty) (hnV : V.Nonempty) (hd : Disjoint U V)
    (hpU : ∀ x ∈ U, 0 < u x) (hpV : ∀ x ∈ V, 0 < u x)
    (hhU : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)))
    (hhV : HasH1Gradient Ω (V.indicator u) (V.indicator (gradient u)))
    (hneg : ∃ x ∈ Ω, u x < 0) : False := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.2.2.1.measure_lt_top.ne
  let A := ∫ x in Ω, U.indicator u x
  let B := ∫ x in Ω, V.indicator u x
  have hB : 0 < B := integral_indicator_pos hΩ.2.1 hΩ.2.2.1 hV hsV hnV
    hu.1.continuousOn hu.2.1.1 hpV
  let w := B • U.indicator u + (-A) • V.indicator u
  let g := B • U.indicator (gradient u) + (-A) • V.indicator (gradient u)
  have hw : HasH1Gradient Ω w g := (hhU.smul B).add (hhV.smul (-A))
  have hm : (∫ x in Ω, w x) = 0 := by
    change (∫ x in Ω, B * U.indicator u x + (-A) * V.indicator u x) = 0
    rw [integral_add ((hhU.1.integrable (by norm_num)).const_mul B)
      ((hhV.1.integrable (by norm_num)).const_mul (-A)),integral_const_mul,integral_const_mul]
    change B*A+(-A)*B=0
    ring
  have he : (∫ x in Ω, ‖g x‖^2) = firstPositiveNeumannValue Ω * (∫ x in Ω, (w x)^2) :=
    disjoint_restriction_combination_energy hu hd hhU hhV B (-A)
  have hz : ∃ a ∈ Ω, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ ball a ε → w x = 0 := by
    obtain ⟨a,ha,han⟩ := hneg
    have haU : {x | u x < 0} ∈ 𝓝 a :=
      (hu.1.continuousOn a ha).continuousAt (hΩ.2.1.mem_nhds ha) |>.eventually (gt_mem_nhds han)
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp haU
    refine ⟨a,ha,ε,hε,Eventually.of_forall fun x hx => ?_⟩
    have hn : u x < 0 := he hx
    have hxu : x ∉ U := fun hxu => (not_lt_of_ge (hpU x hxu).le) hn
    have hxv : x ∉ V := fun hxv => (not_lt_of_ge (hpV x hxv).le) hn
    simp only [w,Pi.add_apply,Pi.smul_apply,indicator_of_notMem hxu,indicator_of_notMem hxv,smul_zero,add_zero]
  have hv : 0 < (volume Ω).toReal := ENNReal.toReal_pos
    (ne_of_gt (hΩ.2.1.measure_pos volume hΩ.1)) hΩ.2.2.1.measure_lt_top.ne
  have hall := minimizer_zero_of_open_zero hΩ.2.1
    hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected hΩ.2.2.1 hv hw hm he hz
  have hvu : (fun x => B * u x) =ᵐ[volume.restrict U] 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsU hall,ae_restrict_mem hU.measurableSet] with x hx hxm
    have hxv : x ∉ V := fun hxv => Set.disjoint_left.mp hd hxm hxv
    simpa only [w,Pi.add_apply,Pi.smul_apply,indicator_of_mem hxm,indicator_of_notMem hxv,
      smul_zero,add_zero,smul_eq_mul,mul_zero] using hx
  have hcont : ContinuousOn (fun x => B*u x) U :=
    continuousOn_const.mul (hu.1.continuousOn.mono hsU)
  have hh := Measure.eqOn_open_of_ae_eq hvu hU hcont continuousOn_const
  obtain ⟨x,hx⟩ := hnU
  have hp := mul_pos hB (hpU x hx)
  have hzero : B*u x = 0 := hh hx
  linarith



lemma positive_set_connected {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : IsConnected (Ω ∩ {x | 0 < u x}) := by
  let P := Ω ∩ {x | 0 < u x}
  have hopen : IsOpen P := positive_set_open hΩ.2.1 hu.1.continuousOn
  obtain ⟨a,ha,hua⟩ := eigenfunction_has_positive hΩ hu hne
  have hap : a ∈ P := ⟨ha,hua⟩
  have heq : P = connectedComponentIn P a := by
    apply subset_antisymm _ (connectedComponentIn_subset P a)
    intro b hb
    by_contra hba
    let U := connectedComponentIn P a
    let V := connectedComponentIn P b
    have hd : Disjoint U V := by
      apply Set.disjoint_left.mpr
      intro x hxU hxV
      have heq : U = V := (connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm
      have hbV : b ∈ V := mem_connectedComponentIn hb
      have hbU : b ∈ U := heq.symm ▸ hbV
      exact hba hbU
    exact no_two_positive_regions hΩ hu hopen.connectedComponentIn hopen.connectedComponentIn
      ((connectedComponentIn_subset P a).trans inter_subset_left)
      ((connectedComponentIn_subset P b).trans inter_subset_left)
      ⟨a,mem_connectedComponentIn hap⟩ ⟨b,mem_connectedComponentIn hb⟩ hd
      (fun x hx => (connectedComponentIn_subset P a hx).2)
      (fun x hx => (connectedComponentIn_subset P b hx).2)
      (positive_component_hasH1Gradient hΩ.2.1 hu.1 hu.2.1 a)
      (positive_component_hasH1Gradient hΩ.2.1 hu.1 hu.2.1 b)
      (eigenfunction_has_negative hΩ hu hne)
  rw [show Ω ∩ {x | 0 < u x} = P from rfl,heq]
  exact isConnected_connectedComponentIn_iff.mpr hap

lemma negative_set_connected {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : IsConnected (Ω ∩ {x | u x < 0}) := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  simpa only [Pi.neg_apply,neg_pos] using positive_set_connected hΩ (eigenfunction_neg hu) hn

end StrictHotSpots.InteriorNodal

end NodalConnectedInteriorLayer

end ActualInteriorNodal

section ClosedEigenMultiplicity

noncomputable section
open Set Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots
open PlaneGreen DiskH10




theorem closedEigenSpace_family_card {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {n : ℕ}
    (f : Fin n → closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) (hf : LinearIndependent ℝ f) : n ≤ 2 := by
  classical
  choose u Y hu huc hY he hjet using fun i => (f i).property
  let J (a : EuclideanSpace ℝ (Fin n)) : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 := ∑ i, a i • f i
  have hjnz (a : EuclideanSpace ℝ (Fin n)) (ha : a ≠ 0) : J a ≠ 0 := by
    intro hz
    have hh := Fintype.linearIndependent_iff.mp hf (fun i => a i) hz
    exact ha (by ext i; exact hh i)
  have hcombo (a : EuclideanSpace ℝ (Fin n)) (x : closure Ω) :
      (J a).val.1 x = ∑ i, a i * u i x := by
    change closedScalarEval hΩ.2.1 hΩ.2.2.1 x (∑ i, a i • f i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change a i * (f i).val.1 x = a i * u i x
    rw [← hjet i]
    rfl
  let F (z : ℂ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => u i (c.F (complexIso z)))
  have hc : ContinuousOn F (closedBall 0 1) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (huc i).comp (c.lipschitz.continuous.comp complexIso.continuous).continuousOn (fun _ hz => c.complex_maps_closed hz)
  have hval (a : EuclideanSpace ℝ (Fin n)) {v : Plane → ℝ} {Z : Plane → Plane}
      (hv : closedEigenJet Ω v Z = (J a).val) (z : ℂ) (hz : z ∈ closedBall 0 1) :
      inner ℝ a (F z) = v (c.F (complexIso z)) := by
    let x : closure Ω := ⟨c.F (complexIso z),c.complex_maps_closed hz⟩
    calc
      inner ℝ a (F z) = ∑ i, a i * u i x := by
        simp only [F,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = (J a).val.1 x := (hcombo a x).symm
      _ = v (c.F (complexIso z)) := by rw [← hv]; rfl
  have hdim := CircleSigns.disk_family_finrank_le_two F hc ?_ ?_ ?_
  · simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    obtain ⟨x,hx,hvx⟩ := InteriorBoundarySign.exists_boundary_pos hΩ.2.1 hΩ.2.2.1 hv hvc hn
    let s : Circle := c.circleBoundaryHomeomorph.symm ⟨x,hx⟩
    have hs : c.F (complexIso (s:ℂ)) = x := congrArg Subtype.val (c.circleBoundaryHomeomorph.apply_symm_apply ⟨x,hx⟩)
    refine ⟨s,?_⟩
    rw [hval a hvjet s (by simp only [mem_closedBall_zero_iff,Circle.norm_coe,le_refl]),hs]
    exact hvx
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    have hcon := c.connected_complex_pull (P := Ioi 0) (InteriorNodal.positive_set_connected hΩ hv hn)
    convert hcon using 1
    ext z
    constructor
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      simpa only [mem_ofPred_eq,mem_preimage,mem_Ioi,mem_Iio,← hval a hvjet z (ball_subset_closedBall hz)] using hp
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      change (0:ℝ) < inner ℝ a (F z)
      rw [hval a hvjet z (ball_subset_closedBall hz)]
      exact hp
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    have hcon := c.connected_complex_pull (P := Iio 0) (InteriorNodal.negative_set_connected hΩ hv hn)
    convert hcon using 1
    ext z
    constructor
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      simpa only [mem_ofPred_eq,mem_preimage,mem_Ioi,mem_Iio,← hval a hvjet z (ball_subset_closedBall hz)] using hp
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      change inner ℝ a (F z) < (0:ℝ)
      rw [hval a hvjet z (ball_subset_closedBall hz)]
      exact hp


theorem closedEigenSpace_finrank_le_two {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) ∧
      Module.finrank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) ≤ 2 := by
  have hr : Module.rank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) < 3 := by
    by_contra hn
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_rank (n := 3) (le_of_not_gt hn)
    have hh := closedEigenSpace_family_card c hΩ f hf
    norm_num at hh
  have hfinite : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) :=
    Module.rank_lt_aleph0_iff.mp (hr.trans (Cardinal.natCast_lt_aleph0 (n := 3)))
  let : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) := hfinite
  refine ⟨hfinite,?_⟩
  have he := Module.finrank_eq_rank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1)
  rw [← he] at hr
  exact Nat.le_of_lt_succ (by exact_mod_cast hr)
end StrictHotSpots
end
end ClosedEigenMultiplicity


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedTraceRank

noncomputable section
open Set Function Module
open scoped Topology
namespace StrictHotSpots
open HilbertMultipliers


lemma closedTraceSpace_rank_oai {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedTraceSpace c hΩ) ∧
      finrank ℝ (closedTraceSpace c hΩ) ≤ 2 := by
  obtain ⟨hf,hr⟩ := closedEigenSpace_finrank_le_two c hΩ
  let : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) := hf
  refine ⟨?_,(LinearMap.finrank_range_le (closedGradientTrace c hΩ)).trans hr⟩
  change Module.Finite ℝ (closedGradientTrace c hΩ).range
  infer_instance

end StrictHotSpots
end
end ClosedTraceRank



end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.closedTraceSpace_rank_oai := @OAI.StrictHotSpots.closedTraceSpace_rank_oai
