-- Prove2me | solution 1 for OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:08:06.742504+00:00
-- url     : https://prove2.me/submissions/d74e225f-5852-4b15-b939-66d624553343

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryActualTower_finite_tensor_amplitude
import Theorems.Thm_OAI_ElasticityBoundaryCutoffLayer_correction_order_bound
import Theorems.Thm_OAI_ElasticityBoundaryCutoffLayer_strong_cutoff_scale
import Theorems.Thm_OAI_ElasticityBoundarySmoothOperator_scaledOperator_order_bound

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling

lemma scale_comp (δ ε : ℝ) (y : Y) : scale δ (scale ε y) = scale (δ*ε) y := by
  ext i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> ring

lemma scale_inv (δ : ℝ) (hδ : δ≠0) (y : Y) : scale δ (scale δ⁻¹ y) = y := by
  rw [scale_comp, mul_inv_cancel₀ hδ, scale_one]

lemma scale_injective (δ : ℝ) (hδ : δ≠0) : Function.Injective (scale δ) := by
  intro y z h
  have := congrArg (scale δ⁻¹) h
  simpa only [scale_comp, inv_mul_cancel₀ hδ, scale_one] using this

lemma scale_surjective (δ : ℝ) (hδ : δ≠0) : Function.Surjective (scale δ) :=
  fun y => ⟨scale δ⁻¹ y, scale_inv δ hδ y⟩

lemma scale_det (δ : ℝ) : (scale δ).det = δ^4 := by
  change LinearMap.det (LinearMap.pi (fun i : Fin 3 =>
    (scaleFactor δ i • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj i))) = _
  rw [LinearMap.det_pi]
  simp [scaleFactor, Fin.prod_univ_three]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact full-space change of variables; valid even when the integral is the
Bochner fallback zero, and for vector-valued functions. -/
theorem integral_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y, f y) = δ^4 • ∫ y, f (scale δ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Y)
    (f := scale δ) (f' := fun _ => scale δ) MeasurableSet.univ
    (fun y _ => (scale δ).hasFDerivAt.hasFDerivWithinAt)
    (scale_injective δ hδ).injOn f
  simpa only [image_univ, (scale_surjective δ hδ).range_eq, Measure.restrict_univ,
    scale_det, abs_of_nonneg (show 0 ≤ δ^4 by positivity), integral_smul] using h

lemma scaled_integrable_iff {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    Integrable (fun y => f (scale δ y)) ↔ Integrable f := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure Y)
    (f := scale δ) (f' := fun _ => scale δ) MeasurableSet.univ
    (fun y _ => (scale δ).hasFDerivAt.hasFDerivWithinAt)
    (scale_injective δ hδ).injOn f
  have hp : δ^4 ≠ 0 := pow_ne_zero _ hδ
  simpa only [image_univ, (scale_surjective δ hδ).range_eq, integrableOn_univ,
    scale_det, abs_of_nonneg (show 0 ≤ δ^4 by positivity), integrable_fun_smul_iff hp] using h.symm

end ElasticityBoundaryScaling

end
end
section
/-! Integrable polynomial majorants for the physical anisotropic boundary-layer
profiles. The decay and all moments are proved, not assumed symbol bounds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights

lemma factor_nonneg (b : ℝ) (i : Fin 3) (t : ℝ) : 0 ≤ factor b i t := by
  unfold factor
  split_ifs
  · exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  · exact (Real.exp_pos _).le

lemma weight_nonneg (b : ℝ) (y : Y) : 0 ≤ weight b y :=
  Finset.prod_nonneg (fun i _ => factor_nonneg b i (y i))

lemma measurable_factor (b : ℝ) (i : Fin 3) : Measurable (factor b i) := by
  unfold factor
  by_cases hi : i = 2
  · simp only [hi, ite_true]
    exact (by fun_prop : Measurable (fun s : ℝ => Real.exp (-b*s))).indicator measurableSet_Ioi
  · simp only [hi, ite_false]
    fun_prop

lemma measurable_weight (b : ℝ) : Measurable (weight b) := by
  unfold weight
  exact Finset.measurable_prod _ (fun i _ => (measurable_factor b i).comp (measurable_pi_apply i))

lemma integrable_factor_pow {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun t : ℝ => |t|^n * factor b i t) := by
  by_cases hi : i = 2
  · have h : IntegrableOn (fun t : ℝ => t^n * Real.exp (-b*t)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
          (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)
    have h' : (fun t : ℝ => |t|^n * factor b i t) =
        (Ioi (0 : ℝ)).indicator (fun t => t^n * Real.exp (-b*t)) := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp [factor, hi, ht, abs_of_pos (mem_Ioi.mp ht)]
      · simp [factor, hi, ht]
    rw [h']
    exact h.integrable_indicator measurableSet_Ioi
  · have h : Integrable (fun t : ℝ => t^n * Real.exp (-b*t^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) hb (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    simpa only [factor, hi, ite_false, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h.norm

lemma integrable_factor {b : ℝ} (hb : 0 < b) (i : Fin 3) : Integrable (factor b i) := by
  simpa using integrable_factor_pow hb i 0

lemma integrable_weight {b : ℝ} (hb : 0 < b) : Integrable (weight b) :=
  Integrable.fintype_prod (fun i => integrable_factor hb i)

lemma integrable_coordinate_moment {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun y : Y => |y i|^n * weight b y) := by
  let g : Fin 3 → ℝ → ℝ := fun j t => (if i=j then |t|^n else 1) * factor b j t
  have hg (j : Fin 3) : Integrable (g j) := by
    by_cases hij : i=j
    · simpa [g, hij] using integrable_factor_pow hb j n
    · simpa [g, hij] using integrable_factor hb j
  have h := Integrable.fintype_prod hg
  simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, ite_true] at h
  exact h

lemma norm_pow_le_sum (y : Y) (n : ℕ) : ‖y‖^n ≤ ∑ i, |y i|^n := by
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm y
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (y j)) n) (Finset.mem_univ i)

/-- Every finite radial moment of the Gaussian-tangential, exponential-normal
profile is integrable over the full coordinate space (zero for t≤0). -/
theorem integrable_norm_moment {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun y : Y => ‖y‖^n * weight b y) := by
  have h := integrable_finsetSum Finset.univ (fun i _ => integrable_coordinate_moment hb i n)
  apply h.mono' ((continuous_norm.measurable.pow_const n).mul (measurable_weight b)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖‖y‖^n * weight b y‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg y) n) (weight_nonneg b y)),
      ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_pow_le_sum y n) (weight_nonneg b y))

end ElasticityBoundaryWeights

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal anisotropic oscillatory Gaussian boundary profiles, with actual
Frechet derivatives.  The small parameter is never assigned a symbolic DN map. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryProfile
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights

lemma phase_real (δ : ℝ) (y : Y) : (value (phase δ) y).re = -y 2-(y 0)^2-(y 1)^2 := by
  simp [phase, value, Complex.div_re, ← Complex.ofReal_pow]
  ring

lemma envelope_norm (δ : ℝ) (y : Y) :
    ‖envelope δ y‖=Real.exp (-y 2-(y 0)^2-(y 1)^2) := by
  rw [envelope, Complex.norm_exp, phase_real]

/-- Modulus squared is the proved integrable Gaussian/normal weight; the fast
oscillation does not alter it at any nonzero scale. -/
theorem profile_square_weight (δ : ℝ) (p : MP) (y : Y) :
    ({y : Y | 0<y 2} : Set Y).indicator (fun y => ‖profile δ p y‖^2) y =
      ‖value p y‖^2 * weight 2 y := by
  by_cases hy : 0<y 2
  · simp [Set.indicator, hy, profile, mul_pow, envelope_norm,
      weight, Fin.prod_univ_three, factor]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    rw [mul_comm (Real.exp _)]
    congr 2
    ring
  · simp [Set.indicator, hy, weight, Fin.prod_univ_three, factor]

end ElasticityBoundaryProfile

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Uniform multivariable Taylor estimates for anisotropically rescaled boundary
layers. The constants are proved for actual smooth compactly supported physical
coefficient extensions; no symbol/asymptotic identification is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityBoundaryTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedDeriv_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : ℕ) (z : E) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => f (t • z)) t =
      iteratedFDeriv ℝ k f (t • z) (fun _ => z) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (f ∘ line z) t (fun _ => 1) = _
  rw [(line z).iteratedFDeriv_comp_right hf t (mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [line_apply, one_smul]

lemma radialTaylor_eq_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (z : E) :
    radialTaylor f n z = taylorWithinEval (fun t : ℝ => f (t • z)) n (Icc 0 1) 0 1 := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hg.of_le (mod_cast le_top)).contDiffAt (by simp), iteratedDeriv_line hf]
  simp

lemma radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ (n+1) f x‖ ≤ C) (z : E) :
    ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) / (n.factorial : ℝ) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n+1) (fun t : ℝ => f (t • z)) (Icc 0 1) t‖ ≤
        C * ‖z‖^(n+1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hg.of_le (mod_cast le_top)).contDiffAt ht, iteratedDeriv_line hf]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hC (t • z)) (pow_nonneg (norm_nonneg z) (n+1)))
  have h := taylor_mean_remainder_bound (f := fun t : ℝ => f (t • z))
    (a := 0) (b := 1) (n := n) (x := 1) (by norm_num)
    (hg.of_le (mod_cast le_top)).contDiffOn (by simp) hbound
  simpa only [radialTaylor_eq_line hf, one_smul, sub_zero, one_pow, mul_one] using h

lemma compact_iteratedFDeriv_bound {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((hf.of_le (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by
    exact_mod_cast le_top)).continuous_iteratedFDeriv').bounded_above_of_compact_support
      (hc.iteratedFDeriv n)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every smooth compactly supported coefficient has a global polynomially
weighted Taylor remainder estimate, at every finite order. -/
theorem compact_radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) := by
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_bound hf hc (n+1)
  refine ⟨C/(n.factorial : ℝ), div_nonneg hC (Nat.cast_nonneg _), fun z => ?_⟩
  simpa only [div_mul_eq_mul_div] using radialTaylor_remainder hf n hbound z

end ElasticityBoundaryTaylor

end
end
section
/-! Literal polynomial representations of the actual Frechet Taylor jets and
of their anisotropic parameter dependence. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTaylorPolynomial
open MvPolynomial ElasticityBoundaryTaylor ElasticityBoundaryMVCalculus ElasticityBoundaryScaling

lemma value_diagonal {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ)
    (y : Y) : value (diagonal T) y = T (fun _ => y) := by
  classical
  have hy : (fun _ : Fin n => y) = (fun _ : Fin n => ∑ i : Fin 3, y i • Pi.single i (1:ℝ)) := by
    funext k i
    simp [Pi.single_apply]
  rw [hy]
  change _ = T.toMultilinearMap (fun _ => ∑ i : Fin 3, y i • Pi.single i (1:ℝ))
  rw [T.toMultilinearMap.map_sum]
  simp only [diagonal, value, eval_sum, eval_mul, eval_C, eval_prod, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  rw [T.toMultilinearMap.map_smul_univ]
  simp only [Complex.real_smul, Complex.ofReal_prod]
  change T (fun k => Pi.single (j k) 1) * _ = _ * T (fun k => Pi.single (j k) 1)
  exact mul_comm _ _

lemma value_taylor (f : Y → ℂ) (n : ℕ) (y : Y) :
    value (taylor f n) y = radialTaylor f n y := by
  simp only [taylor, value, eval_sum, radialTaylor]
  apply Finset.sum_congr rfl
  intro k _
  change value (((k.factorial : ℂ)⁻¹) • diagonal (iteratedFDeriv ℝ k f 0)) y = _
  rw [value_smul, value_diagonal]
  simp [Complex.real_smul]

end ElasticityBoundaryTaylorPolynomial

end
end
section
/-! Corrected amplitudes for the literal Taylor tensor differential operator.
The operator coefficients are computed, rather than a formal sequence assumed. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryActualTower
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryTensorSeries ElasticityBoundaryTaylorPolynomial

lemma parameterize_coeff_zero (p : MP) :
    (parameterize p).coeff 0=C (value p 0) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction p using MvPolynomial.induction_on with
  | C c => simp [parameterize]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq, value_add]
  | mul_X p i hp =>
      have hw : weightOrder i≠0 := by unfold weightOrder; split_ifs <;> decide
      simp only [map_mul, Polynomial.eval_mul, parameterize, aeval_X,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zero_pow hw,
        mul_zero, value_mul, value_X, Pi.zero_apply, Complex.ofReal_zero, map_zero]

lemma taylor_coeff_zero {f : (Fin 3 → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (N : ℕ) :
    (parameterize (taylor f N)).coeff 0=C (f 0) := by
  rw [parameterize_coeff_zero, value_taylor]
  obtain ⟨A,_,hA⟩ := ElasticityBoundaryTaylor.compact_radialTaylor_remainder hf hc N
  have hz : f 0-ElasticityBoundaryTaylor.radialTaylor f N 0=0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hA 0) (norm_nonneg _)
  rw [(sub_eq_zero.mp hz).symm]

end ElasticityBoundaryActualTower

end
end
section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile
lemma measurable_halfspace : MeasurableSet halfspace :=
  (isOpen_lt continuous_const (continuous_apply 2)).measurableSet

lemma one_add_pow_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : (1+r)^n ≤ 2^n*(1+r^n) := by
  by_cases h : r≤1
  · calc
      _ ≤ (2:ℝ)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ _ := by nlinarith [pow_nonneg hr n, pow_nonneg (show (0:ℝ)≤2 by norm_num) n]
  · have h1 : 1 ≤ r := le_of_not_ge h
    calc
      _ ≤ (2*r)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (2:ℝ)^n*r^n := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (show (0:ℝ)≤2 by norm_num) n]

lemma scale_mem_halfspace {δ : ℝ} (hδ : δ≠0) (y : Y) : scale δ y ∈ halfspace ↔ y∈halfspace := by
  change 0 < scale δ y 2 ↔ 0<y 2
  simp only [scale_apply, scaleFactor]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hδ)

lemma scale_indicator {F : Type*} [Zero F] {δ : ℝ} (hδ : δ≠0) (f : Y → F) (y : Y) :
    halfspace.indicator f (scale δ y)=halfspace.indicator (fun y => f (scale δ y)) y := by
  classical
  change (if scale δ y ∈ halfspace then _ else 0) = (if y∈halfspace then _ else 0)
  rw [scale_mem_halfspace hδ]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integralOn_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y in halfspace, f y) = δ^4 • ∫ y in halfspace, f (scale δ y) := by
  rw [← integral_indicator measurable_halfspace, integral_scale hδ]
  simp_rw [scale_indicator hδ]
  rw [integral_indicator measurable_halfspace]

lemma integrableOn_scaled_iff {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    IntegrableOn (fun y => f (scale δ y)) halfspace ↔ IntegrableOn f halfspace := by
  rw [← integrable_indicator_iff measurable_halfspace, ← integrable_indicator_iff measurable_halfspace]
  simpa only [scale_indicator hδ] using (scaled_integrable_iff hδ (halfspace.indicator f))

end ElasticityBoundaryProfileBounds

end
end
section
/-! Uniform polynomial-growth estimates for the actual smooth coefficient
Taylor errors, multiplied by a finite amplitude family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryOrderBound
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryParameterBounds
  ElasticityBoundaryTaylorPolynomial ElasticityBoundaryTaylor ElasticityBoundaryScaling
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights

lemma OrderBound.add {f g : ℝ → Y → ℂ} {k : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g k) : OrderBound (fun δ y => f δ y+g δ y) k := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
  have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
  calc
    _ ≤ ‖f δ y‖+‖g δ y‖ := norm_add_le _ _
    _ ≤ A*δ^k*(1+‖y‖)^a+B*δ^k*(1+‖y‖)^b :=
      add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
    _ ≤ A*δ^k*(1+‖y‖)^(max a b)+B*δ^k*(1+‖y‖)^(max a b) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _))
        (mul_nonneg hA (pow_nonneg hδ.le _)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _))
        (mul_nonneg hB (pow_nonneg hδ.le _)))
    _ = _ := by ring

lemma OrderBound.mul {f g : ℝ → Y → ℂ} {k l : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g l) : OrderBound (fun δ y => f δ y*g δ y) (k+l) := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A*B,mul_nonneg hA hB,a+b,fun δ hδ hδ1 y => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ (A*δ^k*(1+‖y‖)^a)*(B*δ^l*(1+‖y‖)^b) :=
      mul_le_mul (ha δ hδ hδ1 y) (hb δ hδ hδ1 y) (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

/-- Every such explicit bound gives a genuine weighted L2 estimate. -/
theorem OrderBound.square_mass {f : ℝ → Y → ℂ} {k : ℕ} (hf : OrderBound f k)
    (hm : ∀ δ, Continuous (f δ)) {b : ℝ} (hb : 0<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      Integrable (fun y => ‖f δ y‖^2*weight b y) ∧
      (∫ y, ‖f δ y‖^2*weight b y) ≤ C*δ^(2*k) := by
  obtain ⟨A,hA,n,h⟩ := hf
  let g : Y → ℝ := fun y => A^2*2^(2*n)*(weight b y+‖y‖^(2*n)*weight b y)
  have hi : Integrable g := ((integrable_weight hb).add
    (integrable_norm_moment hb (2*n))).const_mul (A^2*2^(2*n))
  have hg (y : Y) : 0≤g y := by
    dsimp [g]
    exact mul_nonneg (by positivity) (add_nonneg (weight_nonneg _ _)
      (mul_nonneg (by positivity) (weight_nonneg _ _)))
  refine ⟨∫ y, g y, integral_nonneg hg,fun δ hδ hδ1 => ?_⟩
  have hp (y : Y) : ‖f δ y‖^2*weight b y ≤ δ^(2*k)*g y := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (h δ hδ hδ1 y) 2
    have hpoly := one_add_pow_le (norm_nonneg y) (2*n)
    have hbase : ‖f δ y‖^2 ≤ (A^2*δ^(2*k))*(2^(2*n)*(1+‖y‖^(2*n))) := by
      calc
        _ ≤ (A*δ^k*(1+‖y‖)^n)^2 := hsq
        _ = (A^2*δ^(2*k))*(1+‖y‖)^(2*n) := by simp only [mul_pow, ← pow_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)
    calc
      _ ≤ ((A^2*δ^(2*k))*(2^(2*n)*(1+‖y‖^(2*n))))*weight b y :=
        mul_le_mul_of_nonneg_right hbase (weight_nonneg b y)
      _ = _ := by dsimp [g]; ring
  have hI : Integrable (fun y => ‖f δ y‖^2*weight b y) := by
    apply (hi.const_mul (δ^(2*k))).mono'
      (((hm δ).norm.pow 2).measurable.mul (measurable_weight b)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      change |‖f δ y‖^2*weight b y| ≤ δ^(2*k)*g y
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_nonneg b y))]
      exact hp y)
  refine ⟨hI, ?_⟩
  have hbound := integral_mono hI (hi.const_mul (δ^(2*k))) hp
  rw [integral_const_mul, mul_comm] at hbound
  exact hbound

end ElasticityBoundaryOrderBound

end
end
section
/-! The genuine smooth variable-coefficient operator applied to constructed
finite boundary amplitudes. The remaining error is estimated, not discarded. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundarySmoothOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryTaylorPolynomial ElasticityBoundaryOrderBound
  ElasticityBoundaryScaling ElasticityBoundaryLayerOperator ElasticityBoundaryWeights

lemma continuous_scaledOperator (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) : Continuous (scaledOperator a b q δ i) := by
  apply Continuous.add
  · apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((ha i α j β).comp (scale δ).continuous).mul (smooth_value _).continuous
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((hb i j β).comp (scale δ).continuous).mul (smooth_value _).continuous

end ElasticityBoundarySmoothOperator

end
end
section
/-! Literal unscaled differential residuals of the constructed boundary fields.
The estimates are in the actual half-space L2 norm, not a formal series norm. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryStrongLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights

lemma envelope_product_indicator (δ : ℝ) (f : Y → ℂ) (y : Y) :
    halfspace.indicator (fun y => ‖envelope δ y*f y‖^2) y=‖f y‖^2*weight 2 y := by
  have h := profile_square_weight δ (C (f y)) y
  change halfspace.indicator (fun z => ‖profile δ (C (f y)) z‖^2) y= _ at h
  by_cases hy : y∈halfspace
  · simpa only [Set.indicator_of_mem hy, profile, value_C] using h
  · simpa only [Set.indicator_of_notMem hy, value_C] using h

lemma integral_envelope_product (δ : ℝ) (f : Y → ℂ) :
    (∫ y in halfspace, ‖envelope δ y*f y‖^2)=∫ y : Y, ‖f y‖^2*weight 2 y := by
  rw [← integral_indicator measurable_halfspace]
  exact integral_congr_ae (Filter.Eventually.of_forall (envelope_product_indicator δ f))

lemma integrable_envelope_product_iff (δ : ℝ) (f : Y → ℂ) :
    IntegrableOn (fun y => ‖envelope δ y*f y‖^2) halfspace ↔
      Integrable (fun y => ‖f y‖^2*weight 2 y) := by
  rw [← integrable_indicator_iff measurable_halfspace]
  have h : halfspace.indicator (fun y => ‖envelope δ y*f y‖^2) =
      (fun y => ‖f y‖^2*weight 2 y) := funext (envelope_product_indicator δ f)
  rw [h]

end ElasticityBoundaryStrongLayer

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Pointwise all-order cutoff bounds. These bounds feed exactly the same
weighted-mass estimate used for the smooth coefficient Taylor error. -/
noncomputable section
open Set
namespace ElasticityBoundaryCutoffBound
open ElasticityBoundaryOrderBound ElasticityBoundaryScaling

lemma bounded_scaled {f : Y → ℂ} {M : ℝ} (hM : 0≤M) (hf : ∀ y, ‖f y‖≤M) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  exact ⟨M,hM,0,fun δ _ _ y => by simpa using hf (scale δ y)⟩

lemma compact_scaled {f : Y → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  obtain ⟨M,hM⟩ := hf.bounded_above_of_compact_support hc
  exact bounded_scaled (le_trans (norm_nonneg (f 0)) (hM 0))
    hM

end ElasticityBoundaryCutoffBound

end
end
section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma smooth_dpart {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (dpart f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma continuous_cutoffScaled (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) : Continuous (cutoffScaled a b χ q δ i) := by
  have hc := hχ.continuous.comp (scale δ).continuous
  apply Continuous.add (hc.mul (continuous_scaledOperator a b ha hb q δ i))
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((ha i α j β).comp (scale δ).continuous).mul
      ((((smooth_dpart hχ β).continuous.comp (scale δ).continuous).mul (smooth_value _).continuous).add
       (((smooth_dpart hχ α).continuous.comp (scale δ).continuous).mul (smooth_value _).continuous))
  · apply continuous_const.mul
    apply Continuous.add
    · apply continuous_finsetSum
      intro α _
      apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro β _
      exact (((ha i α j β).comp (scale δ).continuous).mul
        ((smooth_dpart (smooth_dpart hχ β) α).continuous.comp (scale δ).continuous)).mul
          (smooth_value _).continuous
    · apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro β _
      exact (((hb i j β).comp (scale δ).continuous).mul
        ((smooth_dpart hχ β).continuous.comp (scale δ).continuous)).mul (smooth_value _).continuous

end ElasticityBoundaryCutoffLayer

end
end
section
/-! Compactly supported actual half-space quasimodes with arbitrary strong
residual order and uniform H1 bounds. All scalings are those of the physical
boundary layer, not a formal symbol expansion. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffParametrix
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound ElasticityBoundaryCutoffLayer

lemma scaled_envelope_mass {δ : ℝ} (hδ : δ≠0) (r : ℝ) (F g : Y → ℂ)
    (hF : ∀ y, F (scale δ y)=r • (envelope δ y*g y)) :
    (∫ z in halfspace, ‖F z‖^2)=δ^4*r^2*∫ y : Y, ‖g y‖^2*weight 2 y := by
  rw [integralOn_scale hδ]
  simp_rw [hF, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, integral_envelope_product]
  ring

lemma scaled_envelope_integrable {δ : ℝ} (hδ : δ≠0) (r : ℝ) (F g : Y → ℂ)
    (hF : ∀ y, F (scale δ y)=r • (envelope δ y*g y))
    (hg : Integrable (fun y => ‖g y‖^2*weight 2 y)) :
    IntegrableOn (fun z => ‖F z‖^2) halfspace := by
  rw [← integrableOn_scaled_iff hδ]
  simp_rw [hF, norm_smul, mul_pow]
  exact ((integrable_envelope_product_iff δ g).mpr hg).const_mul _

lemma continuous_strong (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    (u : Fin 3 → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : Fin 3) :
    Continuous (strong a b u i) := by
  apply Continuous.add
  · apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (ha i α j β).mul (smooth_dpart (smooth_dpart (hu j) β) α).continuous
  · apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (hb i j β).mul (smooth_dpart (hu j) β).continuous

/-- A localized smooth physical trial field with arbitrary small strong force. -/
theorem finite_cutoff_layer_oai (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  have hta0 : ∀ i α j β, (tensorTaylor a (N+1) i α j β).coeff 0=C (elasticityTensor l m i α j β) := by
    intro i α j β
    rw [tensorTaylor, taylor_coeff_zero (ha i α j β).1 (ha i α j β).2, ha0]
  obtain ⟨p,R,hp0,hpb,hR⟩ := finite_tensor_amplitude (tensorTaylor a (N+1)) (lowerTaylor b (N+1))
    l m hm he hp hta0 p₀ h₀ (N+1)
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  let q := amplitude p (N+1)
  have hq := scaledOperator_order_bound a b ha hb q R (N+1) hR i
  have ho : OrderBound (fun δ y => cutoffScaled a b χ q δ i y) (N+1+1) := by
    have hmain : OrderBound (fun δ y => χ (scale δ y)*scaledOperator a b q δ i y) (N+1+1) := by
      simpa only [Nat.zero_add] using (compact_scaled hχ.continuous hc).mul hq
    exact hmain.add
      (correction_order_bound a b (fun i α j β => ⟨(ha i α j β).1.continuous,(ha i α j β).2⟩)
        (fun i j β => ⟨(hb i j β).1.continuous,(hb i j β).2⟩) hχ hc hχ0 q (N+1+1) i)
  obtain ⟨C,hC,hI⟩ := ho.square_mass
    (fun δ => continuous_cutoffScaled a b (fun i α j β => (ha i α j β).1.continuous)
      (fun i j β => (hb i j β).1.continuous) hχ q δ i) (by norm_num : (0:ℝ)<2)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hBound⟩ := hI δ hδ hδ1
  have hid := strong_cutoff_scale a b hχ hδ.ne' q i
  have hcont := continuous_strong a b (fun i α j β => (ha i α j β).1.continuous)
    (fun i j β => (hb i j β).1.continuous) (cutoffLayer χ q δ) (smooth_cutoffLayer hχ q δ) i
  refine ⟨(memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    (scaled_envelope_integrable hδ.ne' _ _ _ hid hInt), ?_⟩
  rw [scaled_envelope_mass hδ.ne' _ _ _ hid]
  calc
    _ ≤ δ^4*((δ^4)⁻¹)^2*(C*δ^(2*(N+1+1))) := mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = C*δ^(2*N) := by
      rw [show 2*(N+1+1)=4+2*N by omega, pow_add]
      field_simp

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer_oai := @OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer_oai
