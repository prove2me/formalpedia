-- Prove2me | solution 1 for HighDimProb.Isoperimetry.lipschitz_concentration_sphere
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T12:40:06.563721+00:00
-- url     : https://prove2.me/submissions/befa55cf-ad0d-4c94-a74d-2d05dfc8b6f7

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_SubgaussianNorm
import Definitions.Def_HighDimProb_Isoperimetry_UniformOnSphere

open MeasureTheory

section

open MeasureTheory ContinuousLinearMap Metric Set
open scoped Convolution ContDiff

namespace HighDimProb.Isoperimetry.Fresh

lemma smooth_lipschitz_approximation {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : NNReal) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ x, |F x| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ G ∧ LipschitzWith K G ∧
      (∀ x, |G x| ≤ B) ∧ ∀ x, |G x - F x| ≤ (K : ℝ) * ε := by
  let E := EuclideanSpace ℝ (Fin n)
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let k := φ.normed (volume : Measure E)
  have hk (x : E) : 0 ≤ k x := φ.nonneg_normed x
  have hki : Integrable k (volume : Measure E) := φ.integrable_normed
  have hk1 : (∫ x : E, k x) = 1 := φ.integral_normed
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi (x : E) : Integrable (fun t => k t * F (x - t)) (volume : Measure E) := by
    apply (hki.mul_const B).mono' (((φ.contDiff_normed (n := 0)).continuous.mul (hF.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖k t * F (x - t)‖ ≤ k t * B
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk t)]
    exact mul_le_mul_of_nonneg_left (hB _) (hk t)
  let G : E → ℝ := k ⋆[lsmul ℝ ℝ, volume] F
  have hg (x : E) : G x = ∫ t, k t * F (x - t) := by
    simp only [G, convolution_def, lsmul_apply, smul_eq_mul]
  have hbound (x : E) : |G x| ≤ B := by
    rw [hg]
    calc
      |∫ t, k t * F (x - t)| ≤ ∫ t, |k t * F (x - t)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t => k t * F (x - t))
      _ ≤ ∫ t, k t * B := integral_mono (hi x).abs (hki.mul_const B) fun t => by
        rw [abs_mul, abs_of_nonneg (hk t)]
        exact mul_le_mul_of_nonneg_left (hB _) (hk t)
      _ = B := by rw [integral_mul_const, hk1, one_mul]
  have hlip : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, hg, hg, ← integral_sub (hi x) (hi y)]
    calc
      |∫ t, k t * F (x - t) - k t * F (y - t)| ≤
          ∫ t, |k t * F (x - t) - k t * F (y - t)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun t => k t * F (x - t) - k t * F (y - t))
      _ ≤ ∫ t, k t * ((K : ℝ) * dist x y) :=
        integral_mono ((hi x).sub (hi y)).abs (hki.mul_const _) fun t => by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hk t)]
          apply mul_le_mul_of_nonneg_left _ (hk t)
          simpa only [Real.dist_eq, dist_sub_right] using hF.dist_le_mul (x - t) (y - t)
      _ = (K : ℝ) * dist x y := by rw [integral_mul_const, hk1, one_mul]
  refine ⟨G, ?_, hlip, hbound, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hF.continuous.locallyIntegrable
  · intro x
    have hh := φ.dist_normed_convolution_le (μ := (volume : Measure E))
      hF.continuous.aestronglyMeasurable (x₀ := x) (ε := (K : ℝ) * ε) (fun y hy =>
        (hF.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.coe_nonneg))
    simpa only [Real.dist_eq] using hh

end HighDimProb.Isoperimetry.Fresh
end

section

open Filter
open scoped Topology

namespace HighDimProb.Isoperimetry.Fresh

noncomputable def clipReal (b x : ℝ) : ℝ := min b (max (-b) x)

lemma clipReal_abs_bound {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clipReal b x| ≤ b := by
  apply abs_le.mpr
  exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩

lemma clipReal_abs_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clipReal b x| ≤ |x| := by
  apply abs_le.mpr
  constructor
  · exact le_min (by nlinarith [abs_nonneg x]) ((neg_abs_le x).trans (le_max_right _ _))
  · exact (min_le_right _ _).trans (max_le (by nlinarith [abs_nonneg x]) (le_abs_self x))

lemma clipReal_eq {b x : ℝ} (h : |x| ≤ b) : clipReal b x = x := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [clipReal, max_eq_right hl, min_eq_right hu]

lemma clipReal_lipschitz {α : Type*} [PseudoMetricSpace α] {F : α → ℝ}
    {K : NNReal} (hF : LipschitzWith K F) (b : ℝ) :
    LipschitzWith K (fun x => clipReal b (F x)) := by
  simpa only [clipReal, max_comm, min_comm] using (hF.max_const (-b)).min_const b

lemma clipReal_nat_tendsto (x : ℝ) :
    Tendsto (fun j : ℕ => clipReal j x) atTop (𝓝 x) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with j hj
  exact (clipReal_eq (hN.trans (by exact_mod_cast hj))).symm

end HighDimProb.Isoperimetry.Fresh
end

section

open Filter
open scoped Topology ContDiff

namespace HighDimProb.Isoperimetry.Fresh

lemma exists_smooth_lipschitz_sequence {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : NNReal) (hF : LipschitzWith K F) :
    ∃ G : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ ∞ (G j)) ∧ (∀ j, LipschitzWith K (G j)) ∧
      (∀ x, Tendsto (fun j => G j x) atTop (𝓝 (F x))) ∧
      ∀ j x, |G j x| ≤ |F x| + (K : ℝ) := by
  have hh (j : ℕ) := smooth_lipschitz_approximation (fun x => clipReal j (F x)) K
    (clipReal_lipschitz hF j) j (fun x => clipReal_abs_bound (by positivity) (F x))
    (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity)
  choose G hGs hGl _hGb hGa using hh
  refine ⟨G, hGs, hGl, ?_, ?_⟩
  · intro x
    have he : Tendsto (fun j : ℕ => (K : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hn : Tendsto (fun j => |G j x - clipReal j (F x)|) atTop (𝓝 0) :=
      squeeze_zero (fun j => abs_nonneg _) (fun j => hGa j x) he
    have hz : Tendsto (fun j => G j x - clipReal j (F x)) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hn)
    simpa only [sub_add_cancel, zero_add] using hz.add (clipReal_nat_tendsto (F x))
  · intro j x
    have hc := clipReal_abs_le (show (0 : ℝ) ≤ j by positivity) (F x)
    have he := hGa j x
    have hp : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have ht : |G j x| ≤ |G j x - clipReal j (F x)| + |clipReal j (F x)| :=
      by simpa only [sub_add_cancel] using abs_add_le (G j x - clipReal j (F x)) (clipReal j (F x))
    nlinarith [mul_le_mul_of_nonneg_left hp K.coe_nonneg]

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace HighDimProb.Isoperimetry.Fresh

lemma gaussian_square_quarter :
    Integrable (fun x : ℝ => Real.exp (x ^ 2 / 4)) (gaussianReal 0 1) ∧
    (∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂gaussianReal 0 1) ≤ 2 := by
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (x ^ 2 / 4) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (x ^ 2 / 4)) := by
    simp_rw [he]
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  have hig : Integrable (fun x : ℝ => Real.exp (x ^ 2 / 4)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hi
  refine ⟨hig, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  have hp := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have ht := Real.sq_sqrt (show 0 ≤ Real.pi / (1 / 4 : ℝ) by positivity)
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [inv_mul_eq_div, div_le_iff₀ hsp]
  nlinarith [Real.sqrt_nonneg (Real.pi / (1 / 4 : ℝ))]

lemma gaussian_square_small {c : ℝ} (hc : |c| ≤ 1 / 2) :
    Integrable (fun x : ℝ => Real.exp ((c * x) ^ 2)) (gaussianReal 0 1) ∧
    (∫ x : ℝ, Real.exp ((c * x) ^ 2) ∂gaussianReal 0 1) ≤ 2 := by
  have hpoint (x : ℝ) : Real.exp ((c * x) ^ 2) ≤ Real.exp (x ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    have hcs : c ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (sq_nonneg x)]
  have hi : Integrable (fun x : ℝ => Real.exp ((c * x) ^ 2)) (gaussianReal 0 1) := gaussian_square_quarter.1.mono' (by fun_prop)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint x)
  exact ⟨hi, (integral_mono hi gaussian_square_quarter.1 hpoint).trans gaussian_square_quarter.2⟩

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace HighDimProb.Isoperimetry.Fresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_linear_square (L : E →L[ℝ] ℝ) {A : ℝ} (hA : 0 < A)
    (hL : ‖L‖ ^ 2 ≤ A / 4) :
    Integrable (fun x => Real.exp ((L x) ^ 2 / A)) (stdGaussian E) ∧
    (∫ x, Real.exp ((L x) ^ 2 / A) ∂stdGaussian E) ≤ 2 := by
  by_cases hz : L = 0
  · subst L
    simp
  have hn : 0 < ‖L‖ := norm_pos_iff.mpr hz
  let M : E →L[ℝ] ℝ := ‖L‖⁻¹ • L
  have hM : ‖M‖ = 1 := by simp [M, norm_smul, hn.ne']
  have hlaw : (stdGaussian E).map M = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hM]
    norm_num
  let c : ℝ := ‖L‖ / Real.sqrt A
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hc : |c| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by dsimp [c]; positivity)]
    dsimp [c]
    apply (div_le_iff₀ hs).mpr
    nlinarith [Real.sq_sqrt hA.le]
  have he (x : E) : Real.exp ((c * M x) ^ 2) = Real.exp ((L x) ^ 2 / A) := by
    congr 1
    dsimp [c, M]
    simp only [smul_apply, smul_eq_mul]
    field_simp
    nlinarith [Real.sq_sqrt hA.le]
  have hg := gaussian_square_small hc
  have him : Integrable (fun x : E => Real.exp ((c * M x) ^ 2)) (stdGaussian E) := by
    have hh : Integrable (fun x : ℝ => Real.exp ((c * x) ^ 2)) ((stdGaussian E).map M) := by
      rw [hlaw]
      exact hg.1
    exact hh.comp_measurable (by fun_prop)
  refine ⟨him.congr (ae_of_all _ he), ?_⟩
  calc
    (∫ x, Real.exp ((L x) ^ 2 / A) ∂stdGaussian E) =
        ∫ x, Real.exp ((c * M x) ^ 2) ∂stdGaussian E := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (he x).symm
    _ = ∫ x : ℝ, Real.exp ((c * x) ^ 2) ∂gaussianReal 0 1 := by
      rw [← hlaw, integral_map (by fun_prop) (by fun_prop)]
    _ ≤ 2 := hg.2

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory

namespace HighDimProb.Isoperimetry.Fresh

lemma nonnegative_product_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hm : AEStronglyMeasurable f (μ.prod ν))
    (hn : ∀ p, 0 ≤ f p) (B : ℝ)
    (hi : ∀ x, Integrable (fun y => f (x, y)) ν)
    (hb : ∀ x, (∫ y, f (x, y) ∂ν) ≤ B) :
    Integrable f (μ.prod ν) ∧ (∫ p, f p ∂μ.prod ν) ≤ B := by
  have he (x : α) : (∫ y, ‖f (x, y)‖ ∂ν) = ∫ y, f (x, y) ∂ν := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
  have hin : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
    apply (integrable_const B).mono' hm.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
    exact hb x
  have hif : Integrable f (μ.prod ν) :=
    (integrable_prod_iff hm).mpr ⟨ae_of_all _ hi, hin⟩
  refine ⟨hif, ?_⟩
  rw [integral_prod _ hif]
  exact (integral_mono hif.integral_prod_left (integrable_const B) hb).trans_eq (by simp)

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ContDiff

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma gaussian_gradient_bound (F : E → ℝ) (K : NNReal) (hK : 0 < K)
    (hF : LipschitzWith K F) (hs : ContDiff ℝ ∞ F) :
    Integrable (fun p : E × E => Real.exp (((Real.pi / 2) *
      (fderiv ℝ F p.1) p.2) ^ 2 / (32 * (K : ℝ) ^ 2)))
      ((stdGaussian E).prod (stdGaussian E)) ∧
    (∫ p : E × E, Real.exp (((Real.pi / 2) * (fderiv ℝ F p.1) p.2) ^ 2 /
      (32 * (K : ℝ) ^ 2)) ∂(stdGaussian E).prod (stdGaussian E)) ≤ 2 := by
  have hk : 0 < (K : ℝ) := hK
  have hA : 0 < 32 * (K : ℝ) ^ 2 := by positivity
  have hi (x : E) := gaussian_linear_square ((Real.pi / 2) • fderiv ℝ F x) hA (by
    have hd := norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.pi / 2)]
    have hb : (Real.pi / 2) * ‖fderiv ℝ F x‖ ≤ 2 * (K : ℝ) := by
      have hp := Real.pi_lt_four
      nlinarith [norm_nonneg (fderiv ℝ F x)]
    have hnn : 0 ≤ (Real.pi / 2) * ‖fderiv ℝ F x‖ := by positivity
    nlinarith [sq_nonneg (K : ℝ)])
  have hm : Continuous (fun p : E × E => Real.exp (((Real.pi / 2) *
      (fderiv ℝ F p.1) p.2) ^ 2 / (32 * (K : ℝ) ^ 2))) := by
    have hd : Continuous (fun p : E × E => fderiv ℝ F p.1) :=
      (hs.continuous_fderiv (by norm_num)).comp continuous_fst
    fun_prop
  apply nonnegative_product_bound (stdGaussian E) (stdGaussian E) _ hm.aestronglyMeasurable
    (fun p => (Real.exp_pos _).le) 2
  · intro x
    simpa only [smul_apply, smul_eq_mul] using (hi x).1
  · intro x
    simpa only [smul_apply, smul_eq_mul] using (hi x).2

end HighDimProb.Isoperimetry.Fresh
end

section

open Set
namespace HighDimProb.Isoperimetry.Fresh

lemma convex_exp_square (A : ℝ) (hA : 0 < A) :
    ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (x ^ 2 / A)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs := (even_two.convexOn_pow : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2)).2
    hx hy ha hb hab
  have hd : (a • x + b • y) ^ 2 / A ≤ a • (x ^ 2 / A) + b • (y ^ 2 / A) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, add_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hA.le)
  exact (Real.exp_le_exp.mpr hd).trans
    (convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)

lemma exp_square_midpoint (A x y : ℝ) (hA : 0 < A) :
    Real.exp ((x + y) ^ 2 / (4 * A)) ≤
      (Real.exp (x ^ 2 / A) + Real.exp (y ^ 2 / A)) / 2 := by
  have h := (convex_exp_square A hA).2 (Set.mem_univ x) (Set.mem_univ y)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ^ 2 / A = (x + y) ^ 2 / (4 * A) := by
    field_simp [hA.ne']
    ring
  rw [he] at h
  linarith

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory Set Real
open scoped Topology ContDiff

namespace HighDimProb.Isoperimetry.Fresh

noncomputable def angleMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance angleMeasure_probability : IsProbabilityMeasure angleMeasure where
  measure_univ := by simp [angleMeasure]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rotationPos (x y : E) (t : ℝ) : E :=
  Real.cos (Real.pi / 2 * t) • x + Real.sin (Real.pi / 2 * t) • y

noncomputable def rotationVel (x y : E) (t : ℝ) : E :=
  -Real.sin (Real.pi / 2 * t) • x + Real.cos (Real.pi / 2 * t) • y

lemma rotationPos_deriv (x y : E) (t : ℝ) :
    HasDerivAt (rotationPos x y) ((Real.pi / 2) • rotationVel x y t) t := by
  have hc := ((Real.hasDerivAt_cos (Real.pi / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (Real.pi / 2))).smul_const x
  have hs := ((Real.hasDerivAt_sin (Real.pi / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (Real.pi / 2))).smul_const y
  unfold rotationPos
  simpa only [rotationVel, Function.comp_def, mul_one, one_mul, smul_add, smul_smul, mul_comm] using! hc.fun_add hs

lemma continuous_rotationVel (x y : E) : Continuous (rotationVel x y) := by
  unfold rotationVel
  fun_prop

lemma continuous_rotationPos (x y : E) : Continuous (rotationPos x y) := by
  unfold rotationPos
  fun_prop

lemma smooth_rotation_integral {F : E → ℝ} (hF : ContDiff ℝ ∞ F) (x y : E) :
    (∫ t, (Real.pi / 2) * (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)
      ∂angleMeasure) = F y - F x := by
  have hc : Continuous (fun t => (Real.pi / 2) *
      (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)) := by
    exact continuous_const.mul ((hF.continuous_fderiv (by norm_num)).comp
      (continuous_rotationPos x y) |>.clm_apply (continuous_rotationVel x y))
  have hd (t : ℝ) : HasDerivAt (fun t => F (rotationPos x y t))
      ((Real.pi / 2) * (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)) t := by
    simpa only [map_smul, smul_eq_mul] using!
      (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (rotationPos_deriv x y t)
  rw [angleMeasure, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)]
  simp [rotationPos]

lemma smooth_rotation_jensen {F : E → ℝ} (hF : ContDiff ℝ ∞ F) (x y : E)
    {A : ℝ} (hA : 0 < A) :
    Real.exp ((F y - F x) ^ 2 / A) ≤
      ∫ t, Real.exp (((Real.pi / 2) * (fderiv ℝ F (rotationPos x y t))
        (rotationVel x y t)) ^ 2 / A) ∂angleMeasure := by
  have hc : Continuous (fun t => (Real.pi / 2) *
      (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)) := by
    exact continuous_const.mul ((hF.continuous_fderiv (by norm_num)).comp
      (continuous_rotationPos x y) |>.clm_apply (continuous_rotationVel x y))
  have hi : Integrable (fun t => (Real.pi / 2) *
      (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)) angleMeasure :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hei : Integrable (fun t => Real.exp (((Real.pi / 2) *
      (fderiv ℝ F (rotationPos x y t)) (rotationVel x y t)) ^ 2 / A)) angleMeasure :=
    (Real.continuous_exp.comp ((hc.pow 2).div_const A)).continuousOn.integrableOn_compact isCompact_Icc
  have h := (convex_exp_square A hA).map_integral_le (by fun_prop) isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hi hei
  rwa [smooth_rotation_integral hF x y] at h

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ContDiff

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma gaussian_difference_square (F : E → ℝ) (K : NNReal) (hK : 0 < K)
    (hF : LipschitzWith K F) (hs : ContDiff ℝ ∞ F) :
    Integrable (fun p : E × E => Real.exp ((F p.2 - F p.1) ^ 2 /
      (32 * (K : ℝ) ^ 2))) ((stdGaussian E).prod (stdGaussian E)) ∧
    (∫ p : E × E, Real.exp ((F p.2 - F p.1) ^ 2 / (32 * (K : ℝ) ^ 2))
      ∂(stdGaussian E).prod (stdGaussian E)) ≤ 2 := by
  let μ := (stdGaussian E).prod (stdGaussian E)
  let A := 32 * (K : ℝ) ^ 2
  let q : E × E → ℝ := fun p => Real.exp (((Real.pi / 2) *
      (fderiv ℝ F p.1) p.2) ^ 2 / A)
  let R : ℝ → E × E → E × E := fun t => ContinuousLinearMap.rotation (Real.pi / 2 * t)
  have hq := gaussian_gradient_bound F K hK hF hs
  have hqc : Continuous q := by
    have hd : Continuous (fun p : E × E => fderiv ℝ F p.1) :=
      (hs.continuous_fderiv (by norm_num)).comp continuous_fst
    dsimp [q]
    fun_prop
  have hR (t : ℝ) : μ.map (R t) = μ :=
    IsGaussian.map_rotation_eq_self integral_id_stdGaussian _
  have hi (t : ℝ) : Integrable (fun p => q (R t p)) μ := by
    have hh : Integrable q (μ.map (R t)) := by rw [hR]; exact hq.1
    exact hh.comp_measurable (by dsimp [R]; fun_prop)
  have hb (t : ℝ) : (∫ p, q (R t p) ∂μ) ≤ 2 := by
    rw [← integral_map (by dsimp [R]; fun_prop) hqc.aestronglyMeasurable, hR]
    exact hq.2
  have hmc : Continuous (fun z : ℝ × (E × E) => q (R z.1 z.2)) := by
    apply hqc.comp
    dsimp [R]
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have ht := nonnegative_product_bound angleMeasure μ
    (fun z : ℝ × (E × E) => q (R z.1 z.2)) hmc.aestronglyMeasurable
    (fun _ => (Real.exp_pos _).le) 2 hi hb
  have hdom : Integrable (fun p => ∫ t, q (R t p) ∂angleMeasure) μ := ht.1.integral_prod_right
  have hpoint (p : E × E) : Real.exp ((F p.2 - F p.1) ^ 2 / A) ≤
      ∫ t, q (R t p) ∂angleMeasure := by
    have hh := smooth_rotation_jensen hs p.1 p.2 (A := A) (by dsimp [A]; positivity)
    simpa only [q, R, ContinuousLinearMap.rotation_apply, rotationPos, rotationVel] using hh
  have hdiff : Integrable (fun p : E × E => Real.exp ((F p.2 - F p.1) ^ 2 / A)) μ :=
    hdom.mono' (by fun_prop) (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint p)
  refine ⟨hdiff, ?_⟩
  calc
    (∫ p : E × E, Real.exp ((F p.2 - F p.1) ^ 2 / A) ∂μ) ≤
        ∫ p, (∫ t, q (R t p) ∂angleMeasure) ∂μ := integral_mono hdiff hdom hpoint
    _ = ∫ z, q (R z.1 z.2) ∂angleMeasure.prod μ :=
      (integral_prod_symm _ ht.1).symm
    _ ≤ 2 := ht.2

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ContDiff

namespace HighDimProb.Isoperimetry.Fresh

lemma gaussian_lipschitz_integrable {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal) (hF : LipschitzWith K F) : Integrable F (stdGaussian _) := by
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => |F 0| + (K : ℝ) * ‖x‖)
      (stdGaussian _) := (integrable_const _).add (IsGaussian.integrable_id.norm.const_mul _)
  apply hi.mono' hF.continuous.aestronglyMeasurable
  filter_upwards [] with x
  have hh := hF.dist_le_mul x 0
  have ht := norm_le_norm_sub_add (F x) (F 0)
  simp only [Real.dist_eq, dist_zero_right] at hh
  simp only [Real.norm_eq_abs] at ht ⊢
  linarith

lemma exp_square_center_of_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hi : Integrable F μ)
    {A : ℝ} (hA : 0 < A)
    (hd : Integrable (fun p : Ω × Ω => Real.exp ((F p.2 - F p.1) ^ 2 / A)) (μ.prod μ))
    (hb : (∫ p : Ω × Ω, Real.exp ((F p.2 - F p.1) ^ 2 / A) ∂μ.prod μ) ≤ 2) :
    Integrable (fun x => Real.exp ((F x - ∫ y, F y ∂μ) ^ 2 / A)) μ ∧
    (∫ x, Real.exp ((F x - ∫ y, F y ∂μ) ^ 2 / A) ∂μ) ≤ 2 := by
  have hpoint : ∀ᵐ x ∂μ, Real.exp ((F x - ∫ y, F y ∂μ) ^ 2 / A) ≤
      ∫ y, Real.exp ((F y - F x) ^ 2 / A) ∂μ := by
    filter_upwards [hd.prod_right_ae] with x hx
    have hh := (convex_exp_square A hA).map_integral_le (by fun_prop) isClosed_univ
      (ae_of_all _ fun _ => mem_univ _) (hi.sub (integrable_const (F x))) hx
    have he : (∫ y, F y - F x ∂μ) = (∫ y, F y ∂μ) - F x := by
      rw [integral_sub hi (integrable_const _)]
      simp
    simpa only [Pi.sub_apply, he, sub_sq_comm] using hh
  have hdom := hd.integral_prod_left
  have hmeas : AEStronglyMeasurable (fun x => Real.exp ((F x - ∫ y, F y ∂μ) ^ 2 / A)) μ := by
    exact ((hi.aemeasurable.sub_const _).pow_const 2 |>.div_const A |>
      Real.continuous_exp.measurable.comp_aemeasurable).aestronglyMeasurable
  have hc : Integrable (fun x => Real.exp ((F x - ∫ y, F y ∂μ) ^ 2 / A)) μ :=
    hdom.mono' hmeas (hpoint.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx)
  refine ⟨hc, ?_⟩
  have hh := integral_mono_ae hc hdom hpoint
  rw [← integral_prod _ hd] at hh
  exact hh.trans hb

lemma gaussian_smooth_exp_square {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal) (hK : 0 < K) (hF : LipschitzWith K F) (hs : ContDiff ℝ ∞ F) :
    Integrable (fun x => Real.exp ((F x - ∫ y, F y ∂stdGaussian _) ^ 2 /
      (32 * (K : ℝ) ^ 2))) (stdGaussian _) ∧
    (∫ x, Real.exp ((F x - ∫ y, F y ∂stdGaussian _) ^ 2 /
      (32 * (K : ℝ) ^ 2)) ∂stdGaussian _) ≤ 2 := by
  obtain ⟨hd, hb⟩ := gaussian_difference_square F K hK hF hs
  exact exp_square_center_of_difference (stdGaussian _) F (gaussian_lipschitz_integrable F K hF)
    (by positivity) hd hb

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace HighDimProb.Isoperimetry.Fresh

lemma gaussian_smooth_centered_sequence {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (K : NNReal) (hK : 0 < K)
    (hF : LipschitzWith K F) :
    ∃ G : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, Continuous (G j)) ∧
      (∀ x, Tendsto (fun j => G j x) atTop (𝓝 (F x - ∫ y, F y ∂stdGaussian _))) ∧
      (∀ j, Integrable (fun x => Real.exp ((G j x) ^ 2 / (32 * (K : ℝ) ^ 2))) (stdGaussian _)) ∧
      ∀ j, (∫ x, Real.exp ((G j x) ^ 2 / (32 * (K : ℝ) ^ 2)) ∂stdGaussian _) ≤ 2 := by
  obtain ⟨S, hSs, hSl, hSt, hSb⟩ := exists_smooth_lipschitz_sequence F K hF
  have hi := gaussian_lipschitz_integrable F K hF
  have hm : Tendsto (fun j => ∫ x, S j x ∂stdGaussian _) atTop
      (𝓝 (∫ x, F x ∂stdGaussian _)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |F x| + (K : ℝ))
      (fun j => (hSs j).continuous.aestronglyMeasurable)
      (hi.abs.add (integrable_const _))
    · intro j
      exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hSb j x
    · exact ae_of_all _ hSt
  refine ⟨fun j x => S j x - ∫ y, S j y ∂stdGaussian _, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hSs j).continuous.sub continuous_const
  · intro x
    exact (hSt x).sub hm
  · intro j
    exact (gaussian_smooth_exp_square (S j) K hK (hSl j) (hSs j)).1
  · intro j
    exact (gaussian_smooth_exp_square (S j) K hK (hSl j) (hSs j)).2

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HighDimProb.Isoperimetry.Fresh

lemma exp_square_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (A : ℝ)
    (hm : AEMeasurable f μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (hi : ∀ j, Integrable (fun x => Real.exp ((F j x) ^ 2 / A)) μ)
    (hb : ∀ j, (∫ x, Real.exp ((F j x) ^ 2 / A) ∂μ) ≤ 2) :
    Integrable (fun x => Real.exp ((f x) ^ 2 / A)) μ ∧
    (∫ x, Real.exp ((f x) ^ 2 / A) ∂μ) ≤ 2 := by
  have hn (j : ℕ) : (0 : Ω → ℝ) ≤ᵐ[μ] (fun x => Real.exp ((F j x) ^ 2 / A)) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  have hfn : (0 : Ω → ℝ) ≤ᵐ[μ] (fun x => Real.exp ((f x) ^ 2 / A)) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  have hlim : ∀ᵐ x ∂μ, liminf (fun j => ENNReal.ofReal (Real.exp ((F j x) ^ 2 / A))) atTop =
      ENNReal.ofReal (Real.exp ((f x) ^ 2 / A)) := by
    filter_upwards [ht] with x hx
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_exp.continuousAt.tendsto.comp ((hx.pow 2).div_const A))).liminf_eq
  have hle : (∫⁻ x, ENNReal.ofReal (Real.exp ((f x) ^ 2 / A)) ∂μ) ≤ ENNReal.ofReal 2 := by
    calc
      _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal (Real.exp ((F j x) ^ 2 / A))) atTop ∂μ :=
        lintegral_congr_ae (Filter.EventuallyEq.symm hlim)
      _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal (Real.exp ((F j x) ^ 2 / A)) ∂μ) atTop :=
        lintegral_liminf_le' (fun j => (hi j).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal 2 := by
        have hh : liminf (fun j => ∫⁻ x, ENNReal.ofReal (Real.exp ((F j x) ^ 2 / A)) ∂μ) atTop ≤ liminf (fun _ : ℕ => ENNReal.ofReal 2) atTop := Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun j =>
          (ofReal_integral_eq_lintegral_ofReal (hi j) (hn j)).symm.trans_le
            (ENNReal.ofReal_le_ofReal (hb j))))
        simpa using hh
  have hif : Integrable (fun x => Real.exp ((f x) ^ 2 / A)) μ := by
    refine ⟨(Real.continuous_exp.measurable.comp_aemeasurable ((hm.pow_const 2).div_const A)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hfn).mpr (hle.trans_lt (by simp))
  refine ⟨hif, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hif hfn] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hle

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace HighDimProb.Isoperimetry.Fresh

lemma gaussian_lipschitz_exp_square {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : NNReal) (hK : 0 < K) (hF : LipschitzWith K F) :
    Integrable (fun x => Real.exp ((F x - ∫ y, F y ∂stdGaussian _) ^ 2 /
      (32 * (K : ℝ) ^ 2))) (stdGaussian _) ∧
    (∫ x, Real.exp ((F x - ∫ y, F y ∂stdGaussian _) ^ 2 /
      (32 * (K : ℝ) ^ 2)) ∂stdGaussian _) ≤ 2 := by
  obtain ⟨G, hGc, hGt, hGi, hGb⟩ := gaussian_smooth_centered_sequence F K hK hF
  exact exp_square_limit (stdGaussian _) G _ _
    ((hF.continuous.sub continuous_const).measurable.aemeasurable)
    (ae_of_all _ hGt) hGi hGb

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem gaussian_norm_integrable : Integrable (fun x : E => ‖x‖) (stdGaussian E) :=
  IsGaussian.integrable_id.norm

theorem gaussian_norm_sq_integrable : Integrable (fun x : E => ‖x‖ ^ 2) (stdGaussian E) := by
  simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq

theorem gaussian_norm_sq_integral : (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = n := by
  have hs : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq
  have hi : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at h
    simpa using h
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ (f := fun (i : Fin n) (x : Fin n → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1)
      (i := i) (f := fun x : ℝ => x ^ 2) hs)]
  have hv (i : Fin n) :
      (∫ x : Fin n → ℝ, (x i) ^ 2 ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = 1 :=
    (integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1)
      (i := i) (f := fun x : ℝ => x ^ 2) hs.aestronglyMeasurable).trans hi
  simp only [hv, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory
namespace HighDimProb.Isoperimetry.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma exp_square_aemeasurable (X : Ω → ℝ) (hX : AEMeasurable X P) (A : ℝ) :
    AEStronglyMeasurable (fun ω => Real.exp ((X ω) ^ 2 / A)) P := by
  exact (Real.continuous_exp.measurable.comp_aemeasurable
    ((hX.pow_const 2).div_const A)).aestronglyMeasurable

omit [IsProbabilityMeasure P] in
lemma exp_square_weaken (X : Ω → ℝ) (hX : AEMeasurable X P)
    (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hi : Integrable (fun ω => Real.exp ((X ω) ^ 2 / A)) P)
    (hb : (∫ ω, Real.exp ((X ω) ^ 2 / A) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / B)) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / B) ∂P) ≤ 2 := by
  have hpoint : ∀ ω, Real.exp ((X ω) ^ 2 / B) ≤ Real.exp ((X ω) ^ 2 / A) := by
    intro ω
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg _) hA hAB
  have hiB : Integrable (fun ω => Real.exp ((X ω) ^ 2 / B)) P :=
    hi.mono' (exp_square_aemeasurable P X hX B) (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω))
  exact ⟨hiB, (integral_mono hiB hi hpoint).trans hb⟩

omit [IsProbabilityMeasure P] in
lemma exp_square_add (X Y : Ω → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (A : ℝ) (hA : 0 < A)
    (hXi : Integrable (fun ω => Real.exp ((X ω) ^ 2 / A)) P)
    (hYi : Integrable (fun ω => Real.exp ((Y ω) ^ 2 / A)) P)
    (hXb : (∫ ω, Real.exp ((X ω) ^ 2 / A) ∂P) ≤ 2)
    (hYb : (∫ ω, Real.exp ((Y ω) ^ 2 / A) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω + Y ω) ^ 2 / (4 * A))) P ∧
      (∫ ω, Real.exp ((X ω + Y ω) ^ 2 / (4 * A)) ∂P) ≤ 2 := by
  have hdom : Integrable (fun ω => (Real.exp ((X ω) ^ 2 / A) +
      Real.exp ((Y ω) ^ 2 / A)) / 2) P := (hXi.add hYi).div_const 2
  have hzi : Integrable (fun ω => Real.exp ((X ω + Y ω) ^ 2 / (4 * A))) P :=
    hdom.mono' (exp_square_aemeasurable P (fun ω => X ω + Y ω) (hX.add hY) (4 * A))
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          exp_square_midpoint A (X ω) (Y ω) hA))
  refine ⟨hzi, ?_⟩
  have h := integral_mono hzi hdom (fun ω => exp_square_midpoint A (X ω) (Y ω) hA)
  rw [integral_div, integral_add hXi hYi] at h
  linarith

lemma exp_square_center (Y : Ω → ℝ) (hY : Integrable Y P) (a A : ℝ) (hA : 0 < A)
    (hi : Integrable (fun ω => Real.exp ((Y ω - a) ^ 2 / A)) P)
    (hb : (∫ ω, Real.exp ((Y ω - a) ^ 2 / A) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((Y ω - ∫ z, Y z ∂P) ^ 2 / (4 * A))) P ∧
      (∫ ω, Real.exp ((Y ω - ∫ z, Y z ∂P) ^ 2 / (4 * A)) ∂P) ≤ 2 := by
  have hj := (convex_exp_square A hA).map_integral_le
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hY.sub (integrable_const a)) hi
  have hmean : Real.exp (((∫ z, Y z ∂P) - a) ^ 2 / A) ≤ 2 := by
    have h := hj.trans hb
    simp only [Pi.sub_apply] at h
    rw [integral_sub hY (integrable_const a)] at h
    simpa only [integral_const, probReal_univ, one_smul] using! h
  have hc : (∫ _ : Ω, Real.exp ((a - ∫ z, Y z ∂P) ^ 2 / A) ∂P) ≤ 2 := by
    simpa [sub_sq_comm] using hmean
  have h := exp_square_add P (fun ω => Y ω - a) (fun _ => a - ∫ z, Y z ∂P)
    (hY.aemeasurable.sub measurable_const.aemeasurable) measurable_const.aemeasurable
    A hA hi (integrable_const _) hb hc
  have he : ∀ ω, (Y ω - a) + (a - ∫ z, Y z ∂P) = Y ω - ∫ z, Y z ∂P := by
    intro ω
    ring
  simpa only [he] using h

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory
namespace HighDimProb.Isoperimetry.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma centered_second_moment_bound (X : Ω → ℝ) (hX : AEMeasurable X P)
    (hi : Integrable (fun ω => Real.exp ((X ω) ^ 2 / 32)) P)
    (hb : (∫ ω, Real.exp ((X ω) ^ 2 / 32) ∂P) ≤ 2) :
    Integrable (fun ω => (X ω) ^ 2) P ∧ (∫ ω, (X ω) ^ 2 ∂P) ≤ 32 := by
  have hsi : Integrable (fun ω => (X ω) ^ 2) P :=
    (hi.const_mul 32).mono' ((hX.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Real.add_one_le_exp ((X ω) ^ 2 / 32)]))
  refine ⟨hsi, ?_⟩
  have h := integral_mono ((integrable_const (1 : ℝ)).add (hsi.div_const 32)) hi
    (fun ω => by simpa only [Pi.add_apply, add_comm] using! Real.add_one_le_exp ((X ω) ^ 2 / 32))
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const (1 : ℝ)) (hsi.div_const 32), integral_div] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

lemma radial_exp_square (R : Ω → ℝ) (hR : Integrable R P)
    (hR2 : Integrable (fun ω => (R ω) ^ 2) P) (hR0 : ∀ᵐ ω ∂P, 0 ≤ R ω)
    (r : ℝ) (hr : 0 ≤ r) (hsecond : (∫ ω, (R ω) ^ 2 ∂P) = r ^ 2)
    (hi : Integrable (fun ω => Real.exp ((R ω - ∫ z, R z ∂P) ^ 2 / 32)) P)
    (hb : (∫ ω, Real.exp ((R ω - ∫ z, R z ∂P) ^ 2 / 32) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((R ω - r) ^ 2 / 256)) P ∧
      (∫ ω, Real.exp ((R ω - r) ^ 2 / 256) ∂P) ≤ 2 := by
  let m := ∫ ω, R ω ∂P
  have hm : 0 ≤ m := integral_nonneg_of_ae hR0
  have hX : AEMeasurable (fun ω => R ω - m) P := hR.aemeasurable.sub measurable_const.aemeasurable
  obtain ⟨hvarI, hvarB⟩ := centered_second_moment_bound P (fun ω => R ω - m) hX hi hb
  have hvarEq : (∫ ω, (R ω - m) ^ 2 ∂P) = r ^ 2 - m ^ 2 := by
    have he : (fun ω => (R ω - m) ^ 2) = (fun ω => (R ω) ^ 2 - 2 * m * R ω + m ^ 2) := by
      funext ω
      ring
    have hsub : Integrable (fun ω => (R ω) ^ 2 - 2 * m * R ω) P := by
      simpa only [Pi.sub_apply] using! hR2.sub (hR.const_mul (2 * m))
    rw [he, integral_add hsub (integrable_const (m ^ 2)),
      integral_sub hR2 (hR.const_mul (2 * m)), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul, hsecond]
    change r ^ 2 - 2 * m * m + m ^ 2 = r ^ 2 - m ^ 2
    ring
  have hvar0 : 0 ≤ r ^ 2 - m ^ 2 := by
    rw [← hvarEq]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hmr : m ≤ r := by nlinarith
  have hdiff : (m - r) ^ 2 ≤ 32 := by
    rw [hvarEq] at hvarB
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hmr)]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hconst : Real.exp ((m - r) ^ 2 / 64) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 2 := Real.exp_log (by norm_num)
  obtain ⟨h64i, h64b⟩ := exp_square_weaken P (fun ω => R ω - m) hX 32 64
    (by norm_num) (by norm_num) hi hb
  have h := exp_square_add P (fun ω => R ω - m) (fun _ => m - r) hX
    measurable_const.aemeasurable 64 (by norm_num) h64i (integrable_const _)
    h64b (by simpa using hconst)
  have he : ∀ ω, (R ω - m) + (m - r) = R ω - r := by intro ω; ring
  norm_num only [he] at h
  exact h

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem gaussian_radial_exp_square :
    Integrable (fun x : E => Real.exp ((‖x‖ - Real.sqrt n) ^ 2 / 256)) (stdGaussian E) ∧
      (∫ x : E, Real.exp ((‖x‖ - Real.sqrt n) ^ 2 / 256) ∂stdGaussian E) ≤ 2 := by
  have h := gaussian_lipschitz_exp_square (fun x : E => ‖x‖) 1 (by norm_num) lipschitzWith_one_norm
  norm_num only [NNReal.coe_one, one_pow, mul_one] at h
  apply radial_exp_square (stdGaussian E) (fun x : E => ‖x‖)
    gaussian_norm_integrable gaussian_norm_sq_integrable
    (Filter.Eventually.of_forall norm_nonneg) (Real.sqrt n) (Real.sqrt_nonneg _) _ h.1 h.2
  rw [gaussian_norm_sq_integral, Real.sq_sqrt (Nat.cast_nonneg n)]

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def normalize (r : ℝ) (x : E) : E := (r / ‖x‖) • x

theorem measurable_normalize (r : ℝ) : Measurable (normalize (n := n) r) := by
  unfold normalize
  fun_prop

theorem norm_normalize {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : x ≠ 0) :
    ‖normalize r x‖ = r := by
  rw [normalize, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr (norm_nonneg _))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)

theorem normalize_isometry (r : ℝ) (U : E ≃ₗᵢ[ℝ] E) (x : E) :
    normalize r (U x) = U (normalize r x) := by
  simp [normalize]

theorem gaussian_ne_zero (hn : 0 < n) : ∀ᵐ x ∂stdGaussian E, x ≠ 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hz : (stdGaussian E) {0} = 0 := by
    rw [← map_pi_eq_stdGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _)
      (measurableSet_singleton _)]
    have he : (WithLp.toLp 2) ⁻¹' ({0} : Set E) = {0} := by ext x; simp
    rw [he, Measure.pi_singleton]
    simp [hn.ne']
  simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hz

theorem gaussian_normalize_norm (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂(stdGaussian E).map (normalize r), ‖x‖ = r := by
  apply (ae_map_iff (measurable_normalize r).aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).2
  filter_upwards [gaussian_ne_zero hn] with x hx
  exact norm_normalize hr hx

theorem gaussian_normalize_invariant (r : ℝ) (U : E ≃ₗᵢ[ℝ] E) :
    ((stdGaussian E).map (normalize r)).map U = (stdGaussian E).map (normalize r) := by
  rw [Measure.map_map U.continuous.measurable (measurable_normalize r)]
  have he : (U ∘ normalize r) = (normalize r ∘ U) := by
    funext x
    exact (normalize_isometry r U x).symm
  rw [he, ← Measure.map_map (measurable_normalize r) U.continuous.measurable,
    stdGaussian_map]

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem dist_normalize {r : ℝ} {x : E} (hx : x ≠ 0) :
    dist (normalize r x) x = |r - ‖x‖| := by
  have hs : normalize r x - x = (r / ‖x‖ - 1) • x := by
    simp [normalize, sub_smul]
  rw [dist_eq_norm, hs, norm_smul, Real.norm_eq_abs]
  calc
    |r / ‖x‖ - 1| * ‖x‖ = |(r / ‖x‖ - 1) * ‖x‖| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
    _ = |r - ‖x‖| := by
      rw [sub_mul, div_mul_cancel₀ r (norm_ne_zero_iff.mpr hx), one_mul]

theorem observable_radial_error {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F)
    (r : ℝ) (hn : 0 < n) :
    ∀ᵐ x ∂stdGaussian E, |F (normalize r x) - F x| ≤ (L : ℝ) * |r - ‖x‖| := by
  filter_upwards [gaussian_ne_zero hn] with x hx
  simpa only [Real.dist_eq, dist_normalize hx] using hF.dist_le_mul (normalize r x) x

theorem sphere_observable_integrable {F : E → ℝ} {L : NNReal}
    (hF : LipschitzWith L F) {r : ℝ} (hr : 0 ≤ r) (hn : 0 < n) :
    Integrable (fun x => F (normalize r x)) (stdGaussian E) := by
  refine (integrable_const (|F 0| + (L : ℝ) * r)).mono' ?_ ?_
  · exact (hF.continuous.measurable.comp (measurable_normalize r)).aestronglyMeasurable
  · filter_upwards [gaussian_ne_zero hn] with x hx
    have h := hF.dist_le_mul (normalize r x) 0
    rw [Real.dist_eq, dist_zero_right, norm_normalize hr hx] at h
    rw [Real.norm_eq_abs]
    calc
      |F (normalize r x)| = |(F (normalize r x) - F 0) + F 0| := by congr 1; ring
      _ ≤ |F (normalize r x) - F 0| + |F 0| := abs_add_le _ _
      _ ≤ |F 0| + (L : ℝ) * r := by linarith

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory

namespace HighDimProb.Isoperimetry.Fresh

lemma scaled_error_exp_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X D : Ω → ℝ)
    (hX : AEMeasurable X P) {L A : ℝ} (hL : 0 < L) (hA : 0 < A)
    (hbound : ∀ᵐ ω ∂P, |X ω| ≤ L * |D ω|)
    (hi : Integrable (fun ω => Real.exp ((D ω) ^ 2 / A)) P)
    (hb : (∫ ω, Real.exp ((D ω) ^ 2 / A) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / (A * L ^ 2))) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / (A * L ^ 2)) ∂P) ≤ 2 := by
  have hpoint : ∀ᵐ ω ∂P, Real.exp ((X ω) ^ 2 / (A * L ^ 2)) ≤
      Real.exp ((D ω) ^ 2 / A) := by
    filter_upwards [hbound] with ω hω
    apply Real.exp_le_exp.mpr
    have hs : (X ω) ^ 2 ≤ L ^ 2 * (D ω) ^ 2 := by
      have hh := mul_self_le_mul_self (abs_nonneg (X ω)) hω
      simpa only [← pow_two, mul_pow, sq_abs] using hh
    rw [div_le_div_iff₀ (mul_pos hA (sq_pos_of_pos hL)) hA]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hA.le]
  have hxi : Integrable (fun ω => Real.exp ((X ω) ^ 2 / (A * L ^ 2))) P :=
    hi.mono' (exp_square_aemeasurable P X hX _) (hpoint.mono fun ω hω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω)
  exact ⟨hxi, (integral_mono_ae hxi hi hpoint).trans hb⟩

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem sphere_lipschitz_exp_square (F : E → ℝ) (L : NNReal)
    (hL : 0 < L) (hF : LipschitzWith L F) (hn : 0 < n) :
    Integrable (fun x => Real.exp ((F (normalize (Real.sqrt n) x) -
      ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E) ^ 2 / (64 * (L : ℝ)) ^ 2)) (stdGaussian E) ∧
    (∫ x, Real.exp ((F (normalize (Real.sqrt n) x) -
      ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E) ^ 2 / (64 * (L : ℝ)) ^ 2) ∂stdGaussian E) ≤ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let P := stdGaussian E
  let Y : E → ℝ := fun x => F (normalize (Real.sqrt n) x)
  let a : ℝ := ∫ x, F x ∂P
  let A : E → ℝ := fun x => F x - a
  let D : E → ℝ := fun x => Y x - F x
  have hY : Integrable Y P := sphere_observable_integrable hF (Real.sqrt_nonneg _) hn
  have hA : AEMeasurable A P := hF.continuous.measurable.aemeasurable.sub measurable_const.aemeasurable
  have hD : AEMeasurable D P := hY.aemeasurable.sub hF.continuous.measurable.aemeasurable
  have hg := gaussian_lipschitz_exp_square F L hL hF
  have hgi := exp_square_weaken P A hA (32 * (L : ℝ) ^ 2) (256 * (L : ℝ) ^ 2)
    (by positivity) (by nlinarith [sq_nonneg (L : ℝ)]) hg.1 hg.2
  have herr : ∀ᵐ x ∂P, |D x| ≤ (L : ℝ) * |‖x‖ - Real.sqrt n| := by
    simpa only [D, Y, abs_sub_comm] using observable_radial_error hF (Real.sqrt n) hn
  have hd := scaled_error_exp_square P D (fun x => ‖x‖ - Real.sqrt n) hD hLr
    (by norm_num : (0 : ℝ) < 256) herr gaussian_radial_exp_square.1 gaussian_radial_exp_square.2
  have hadd := exp_square_add P A D hA hD (256 * (L : ℝ) ^ 2) (by positivity)
    hgi.1 hd.1 hgi.2 hd.2
  have he : ∀ x, A x + D x = Y x - a := by
    intro x
    dsimp [A, D]
    ring
  have hden : 4 * (256 * (L : ℝ) ^ 2) = 1024 * (L : ℝ) ^ 2 := by ring
  simp only [he, hden] at hadd
  have hc := exp_square_center P Y hY a (1024 * (L : ℝ) ^ 2) (by positivity) hadd.1 hadd.2
  have hden' : 4 * (1024 * (L : ℝ) ^ 2) = (64 * (L : ℝ)) ^ 2 := by ring
  simpa only [hden'] using hc

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem charFun_radial (μ : Measure E)
    (hi : ∀ U : E ≃ₗᵢ[ℝ] E, μ.map U = μ)
    {t u : E} (htu : ‖t‖ = ‖u‖) : charFun μ t = charFun μ u := by
  let U : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (t - u))ᗮ
  have hU : U t = u := Submodule.reflection_sub htu
  calc
    charFun μ t = ∫ x, Complex.exp ((inner ℝ (U x) (U t) : ℝ) * Complex.I) ∂μ := by
      simp only [charFun_apply, U.inner_map_map]
    _ = charFun (μ.map U) u := by
      rw [charFun_apply, integral_map U.continuous.aemeasurable (by fun_prop)]
      simp only [hU]
    _ = charFun μ u := by rw [hi U]

theorem invariant_sphere_unique (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ = r) (hν : ∀ᵐ x ∂ν, ‖x‖ = r)
    (hiμ : ∀ U : E ≃ₗᵢ[ℝ] E, μ.map U = μ)
    (hiν : ∀ U : E ≃ₗᵢ[ℝ] E, ν.map U = ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  let a : ℝ := ‖t‖ / r
  have ha : 0 ≤ a := div_nonneg (norm_nonneg _) hr.le
  have hn (x : E) (hx : ‖x‖ = r) : ‖a • x‖ = ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hx]
    exact div_mul_cancel₀ _ hr.ne'
  have hconstμ : (fun z => charFun μ (a • z)) =ᵐ[ν] fun _ => charFun μ t := by
    filter_upwards [hν] with z hz
    exact charFun_radial μ hiμ (hn z hz)
  have hconstν : (fun x => charFun ν (a • x)) =ᵐ[μ] fun _ => charFun ν t := by
    filter_upwards [hμ] with x hx
    exact charFun_radial ν hiν (hn x hx)
  have hint : Integrable (fun p : E × E =>
      Complex.exp ((inner ℝ p.1 (a • p.2) : ℝ) * Complex.I)) (μ.prod ν) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun p => (Complex.norm_exp_ofReal_mul_I _).le
  calc
    charFun μ t = ∫ z, charFun μ (a • z) ∂ν := by
      rw [integral_congr_ae hconstμ, integral_const]
      simp
    _ = ∫ x, ∫ z, Complex.exp ((inner ℝ x (a • z) : ℝ) * Complex.I) ∂ν ∂μ := by
      simp only [charFun_apply]
      exact (integral_integral_swap hint).symm
    _ = ∫ x, charFun ν (a • x) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [charFun_apply]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp only
          rw [inner_smul_right, inner_smul_right, real_inner_comm x z]
    _ = charFun ν t := by
      rw [integral_congr_ae hconstν, integral_const]
      simp

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem native_uniform_map_eq {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (hu : IsUniformOnSphere P (Real.sqrt n) X) (hn : 0 < n) :
    P.map X = (stdGaussian E).map (normalize (Real.sqrt n)) := by
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let : IsProbabilityMeasure ((stdGaussian E).map (normalize (Real.sqrt n))) :=
    Measure.isProbabilityMeasure_map (measurable_normalize _).aemeasurable
  apply invariant_sphere_unique _ _ (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
  · apply (ae_map_iff hX.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet).2
    filter_upwards [hu.1] with ω hω
    simpa only [Metric.mem_sphere, dist_zero_right] using hω
  · exact gaussian_normalize_norm hn (Real.sqrt_nonneg _)
  · intro U
    rw [Measure.map_map U.continuous.measurable hX]
    exact hu.2 U
  · exact gaussian_normalize_invariant _

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem integral_comp_eq_of_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = Q.map Y)
    (g : E → ℝ) (hg : Measurable g) :
    (∫ ω, g (X ω) ∂P) = ∫ ω, g (Y ω) ∂Q := by
  rw [← integral_map hX.aemeasurable hg.aestronglyMeasurable, hlaw,
    integral_map hY.aemeasurable hg.aestronglyMeasurable]

theorem integrable_comp_iff_of_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = Q.map Y)
    (g : E → ℝ) (hg : Measurable g) :
    Integrable (fun ω => g (X ω)) P ↔ Integrable (fun ω => g (Y ω)) Q := by
  change Integrable (g ∘ X) P ↔ Integrable (g ∘ Y) Q
  rw [← integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable,
    hlaw, integrable_map_measure hg.aestronglyMeasurable hY.aemeasurable]

theorem native_witness_transfer {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (hu : IsUniformOnSphere P (Real.sqrt n) X) (hn : 0 < n)
    (f F : E → ℝ) (hF : Continuous F)
    (he : Set.EqOn f F (Metric.sphere (0 : E) (Real.sqrt n))) (t : ℝ)
    (hi : Integrable (fun x => Real.exp ((F (normalize (Real.sqrt n) x) -
      ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E) ^ 2 / t ^ 2)) (stdGaussian E))
    (hb : (∫ x, Real.exp ((F (normalize (Real.sqrt n) x) -
      ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E) ^ 2 / t ^ 2) ∂stdGaussian E) ≤ 2) :
    Integrable (fun ω => Real.exp ((f (X ω) - ∫ ω, f (X ω) ∂P) ^ 2 / t ^ 2)) P ∧
      (∫ ω, Real.exp ((f (X ω) - ∫ ω, f (X ω) ∂P) ^ 2 / t ^ 2) ∂P) ≤ 2 := by
  have hlaw := native_uniform_map_eq P hX hu hn
  have hae : (fun ω => f (X ω)) =ᵐ[P] fun ω => F (X ω) := by
    filter_upwards [hu.1] with ω hω
    exact he hω
  have hm : (∫ ω, f (X ω) ∂P) = ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E :=
    (integral_congr_ae hae).trans
      (integral_comp_eq_of_law hX (measurable_normalize _) hlaw F hF.measurable)
  let g : E → ℝ := fun x => Real.exp ((F x -
    ∫ y, F (normalize (Real.sqrt n) y) ∂stdGaussian E) ^ 2 / t ^ 2)
  have hg : Measurable g := by unfold g; fun_prop
  have haeg : (fun ω => Real.exp ((f (X ω) - ∫ ω, f (X ω) ∂P) ^ 2 / t ^ 2)) =ᵐ[P]
      fun ω => g (X ω) := by
    filter_upwards [hae] with ω hω
    dsimp only [g]
    rw [hω, hm]
  constructor
  · have hh := (integrable_comp_iff_of_law hX (measurable_normalize _) hlaw g hg).2 hi
    exact hh.congr haeg.symm
  · rw [integral_congr_ae haeg, integral_comp_eq_of_law hX (measurable_normalize _) hlaw g hg]
    exact hb

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory
namespace HighDimProb.Isoperimetry.Fresh
variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)

lemma subgaussianNorm_le_of_witness (X : Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (hi : Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P)
    (hb : (∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P) ≤ 2) :
    subgaussianNorm P X ≤ t := by
  unfold subgaussianNorm
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro r hr
    exact hr.1.le
  · exact ⟨ht, hi, hb⟩

lemma subgaussianNorm_congr_ae (X Y : Ω → ℝ) (h : X =ᵐ[P] Y) :
    subgaussianNorm P X = subgaussianNorm P Y := by
  unfold subgaussianNorm
  congr 1
  ext t
  have he : (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) =ᵐ[P]
      (fun ω => Real.exp ((Y ω) ^ 2 / t ^ 2)) := h.mono (fun _ hω => by simp only [hω])
  have hi := integrable_congr he
  have hv := integral_congr_ae he
  change (0 < t ∧ Integrable (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) P ∧
    (∫ ω, Real.exp ((X ω) ^ 2 / t ^ 2) ∂P) ≤ 2) ↔
    (0 < t ∧ Integrable (fun ω => Real.exp ((Y ω) ^ 2 / t ^ 2)) P ∧
    (∫ ω, Real.exp ((Y ω) ^ 2 / t ^ 2) ∂P) ≤ 2)
  rw [hi, hv]

lemma subgaussianNorm_zero_ae [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : X =ᵐ[P] 0) : subgaussianNorm P X ≤ 0 := by
  have hall : ∀ t : ℝ, 0 < t → subgaussianNorm P X ≤ t := by
    intro t ht
    have he : (fun ω => Real.exp ((X ω) ^ 2 / t ^ 2)) =ᵐ[P] (fun _ => (1 : ℝ)) := by
      filter_upwards [hX] with ω hω
      simp [hω]
    apply subgaussianNorm_le_of_witness P X t ht
    · exact (integrable_const (1 : ℝ)).congr he.symm
    · rw [integral_congr_ae he]
      simp
  by_contra hn
  have hp : 0 < subgaussianNorm P X := lt_of_not_ge hn
  have h := hall (subgaussianNorm P X / 2) (by positivity)
  linarith

end HighDimProb.Isoperimetry.Fresh
end

section

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.Fresh

theorem native_sphere_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (hX : Measurable X)
    (hu : IsUniformOnSphere P (Real.sqrt n) X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal)
    (hf : LipschitzOnWith L f (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n))) :
    subgaussianNorm P (fun ω => f (X ω) - ∫ ω, f (X ω) ∂P) ≤ 64 * (L : ℝ) := by
  have hzero (c : ℝ) (hc : (fun ω => f (X ω)) =ᵐ[P] fun _ => c) :
      subgaussianNorm P (fun ω => f (X ω) - ∫ ω, f (X ω) ∂P) ≤ 0 := by
    have hm : (∫ ω, f (X ω) ∂P) = c := by rw [integral_congr_ae hc]; simp
    apply subgaussianNorm_zero_ae P
    filter_upwards [hc] with ω hω
    simp only [hω, hm, sub_self, Pi.zero_apply]
  by_cases hn : n = 0
  · subst n
    have hc : (fun ω => f (X ω)) =ᵐ[P] fun _ => f 0 :=
      Filter.Eventually.of_forall fun ω => congrArg f (Subsingleton.elim (X ω) 0)
    exact (hzero (f 0) hc).trans (by positivity)
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨F, hF, he⟩ := hf.extend_real
  by_cases hL : L = 0
  · subst L
    have hc : (fun ω => f (X ω)) =ᵐ[P] fun _ => F 0 := by
      filter_upwards [hu.1] with ω hω
      rw [he hω]
      apply dist_le_zero.mp
      simpa using hF.dist_le_mul (X ω) 0
    simpa using hzero (F 0) hc
  have hLp : 0 < L := lt_of_le_of_ne (zero_le) (Ne.symm hL)
  have hw := sphere_lipschitz_exp_square F L hLp hF hnp
  have ht := native_witness_transfer P hX hu hnp f F hF.continuous he (64 * (L : ℝ)) hw.1 hw.2
  exact subgaussianNorm_le_of_witness P _ _ (by positivity) ht.1 ht.2

theorem native_lipschitz_concentration_sphere :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (_hX_meas : Measurable X)
        (_hX_unif : IsUniformOnSphere Prob (Real.sqrt n) X)
        (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal)
        (_hf_lip : LipschitzOnWith L f (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n))),
        subgaussianNorm Prob (fun ω => f (X ω) - ∫ ω, f (X ω) ∂Prob) ≤ C * (L : ℝ) := by
  refine ⟨64, by norm_num, ?_⟩
  intro Ω _ P _ n X hX hu f L hf
  exact native_sphere_bound P X hX hu f L hf

end HighDimProb.Isoperimetry.Fresh
end

open HighDimProb.Isoperimetry

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (_hX_meas : Measurable X)
        (_hX_unif : IsUniformOnSphere Prob (Real.sqrt n) X)
        (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal)
        (_hf_lip : LipschitzOnWith L f (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n))),
        subgaussianNorm Prob (fun ω => f (X ω) - ∫ ω, f (X ω) ∂Prob) ≤ C * (L : ℝ)  := by
  exact Fresh.native_lipschitz_concentration_sphere
