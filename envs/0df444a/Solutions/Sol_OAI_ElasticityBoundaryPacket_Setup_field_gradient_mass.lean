-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:51:13.580915+00:00
-- url     : https://prove2.me/submissions/acea6c27-8540-473f-90ab-8d5f5cb4dc46

import Mathlib
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Theorems.Thm_OAI_ElasticityBoundaryCutoffParametrix_first_scaled_identity
import Theorems.Thm_OAI_ElasticityBoundaryGradientMass_transferred_gradient_mass

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal smooth polynomial amplitudes in boundary coordinates, including
actual Frechet derivatives and polynomial growth. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace ElasticityBoundaryMVCalculus

/-- Every fixed amplitude is bounded by a uniform polynomial moment, so the
Gaussian/exponential majorants used for its remainder are honest integrable functions. -/
theorem polynomialGrowth (p : MP) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ y : Y, ‖value p y‖ ≤ C*(1+‖y‖)^d := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, 0, fun y => by simp⟩
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun y => ?_⟩
      have hbase : 1 ≤ 1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value p y‖+‖value q y‖ := by rw [value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha y) (hb y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right _ _)) hB)
        _ = _ := by ring
  | mul_X p i hp =>
      obtain ⟨A,hA,a,ha⟩ := hp
      refine ⟨A,hA,a+1,fun y => ?_⟩
      have hcoord : ‖(y i : ℂ)‖ ≤ 1+‖y‖ := by
        rw [Complex.norm_real]
        exact (norm_le_pi_norm y i).trans (by linarith)
      calc
        _ = ‖value p y‖*‖(y i : ℂ)‖ := by rw [value_mul, value_X, norm_mul]
        _ ≤ (A*(1+‖y‖)^a)*(1+‖y‖) :=
          mul_le_mul (ha y) hcoord (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end ElasticityBoundaryMVCalculus

end
end
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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
/-! Uniform true L2/H1 estimates for finite corrected boundary amplitudes. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryParameterBounds
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights ElasticityBoundaryParameter

lemma atParameter_add (q r : Polynomial MP) (δ : ℝ) :
    atParameter (q+r) δ=atParameter q δ+atParameter r δ := Polynomial.eval_add

lemma value_parameter_monomial (n : ℕ) (p : MP) (δ : ℝ) (y : Y) :
    value (atParameter (Polynomial.monomial n p) δ) y=value p y*(δ:ℂ)^n := by
  simp [atParameter,value]

lemma parameterGrowth (q : Polynomial MP) :
    ∃ A : ℝ, 0≤A ∧ ∃ n : ℕ, ∀ δ : ℝ, 0≤δ → δ≤1 → ∀ y : Y,
      ‖value (atParameter q δ) y‖ ≤ A*(1+‖y‖)^n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
      have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value (atParameter p δ) y‖+‖value (atParameter q δ) y‖ := by
          rw [atParameter_add,value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _)) hB)
        _ = _ := by ring
  | monomial k p =>
      obtain ⟨A,hA,a,ha⟩ := polynomialGrowth p
      refine ⟨A,hA,a,fun δ hδ hδ1 y => ?_⟩
      rw [value_parameter_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hδ]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hδ hδ1)).trans (ha y)

end ElasticityBoundaryParameterBounds

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

lemma OrderBound.weaken {f : ℝ → Y → ℂ} {k l : ℕ} (hf : OrderBound f k) (hl : l≤k) :
    OrderBound f l := by
  obtain ⟨A,hA,n,h⟩ := hf
  refine ⟨A,hA,n,fun δ hδ hδ1 y => ?_⟩
  exact (h δ hδ hδ1 y).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδ1 hl) hA) (by positivity))

lemma parameter_bound (p : Polynomial MP) :
    OrderBound (fun δ y => value (atParameter p δ) y) 0 := by
  obtain ⟨A,hA,n,h⟩ := parameterGrowth p
  exact ⟨A,hA,n,fun δ hδ hδ1 y => by simpa using h δ hδ.le hδ1 y⟩

lemma power_bound (k : ℕ) : OrderBound (fun δ _ => (δ:ℂ)^k) k := by
  refine ⟨1,by norm_num,0,fun δ hδ _ _ => ?_⟩
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]

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

lemma compact_dpart {f : Y → ℂ} (hf : HasCompactSupport f) (j : Fin 3) :
    HasCompactSupport (dpart f j) := HasCompactSupport.fderiv_apply ℝ hf _

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

lemma first_scaled_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j β : Fin 3) :
    OrderBound (fun δ y => firstScaled χ q δ j β y) 0 := by
  have hmain : OrderBound (fun δ y => χ (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y) 0 := by
    simpa only [Nat.zero_add] using (compact_scaled hχ.continuous hc).mul
      (parameter_bound (PD β (unpack j q)))
  have herr : OrderBound (fun δ y => (δ:ℂ)^2*dpart χ β (scale δ y)*value (atParameter (unpack j q) δ) y) 0 := by
    have h := (((power_bound 2).mul (compact_scaled (smooth_dpart hχ β).continuous (compact_dpart hc β))).mul
      (parameter_bound (unpack j q))).weaken (show 0≤2+0+0 by omega)
    exact h
  exact hmain.add herr

lemma first_scaled_continuous {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j β : Fin 3) : Continuous (firstScaled χ q δ j β) := by
  exact ((hχ.continuous.comp (scale δ).continuous).mul (smooth_value _).continuous).add
    ((continuous_const.mul ((smooth_dpart hχ β).continuous.comp (scale δ).continuous)).mul
      (smooth_value _).continuous)

/-- The actual physical gradient is uniformly L2 bounded; its delta^-2
factor is canceled by the genuine anisotropic delta^4 volume factor. -/
theorem cutoff_gradient_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j β : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      MemLp (dpart (cutoffLayer χ q δ j) β) 2 (volume.restrict halfspace) ∧
      (∫ z in halfspace, ‖dpart (cutoffLayer χ q δ j) β z‖^2) ≤ C := by
  obtain ⟨C,hC,hI⟩ := (first_scaled_bound hχ hc q j β).square_mass
    (fun δ => first_scaled_continuous hχ q δ j β) (by norm_num : (0:ℝ)<2)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hB⟩ := hI δ hδ hδ1
  have hid := first_scaled_identity hχ hδ.ne' q j β
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (smooth_dpart (smooth_cutoffLayer hχ q δ j) β).continuous.aestronglyMeasurable).mpr
      (scaled_envelope_integrable hδ.ne' _ _ _ hid hInt), ?_⟩
  rw [scaled_envelope_mass hδ.ne' _ _ _ hid]
  have hpow : δ^4*((δ^2)⁻¹)^2=1 := by field_simp
  rw [hpow,one_mul]
  simpa only [Nat.mul_zero,pow_zero,mul_one] using hB

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Value mass and the exact identification of Euclidean and product Lebesgue
measure used by the physical boundary packets. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryPacketMass
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryParameterBounds
  ElasticityBoundaryOrderBound ElasticityBoundaryCutoffBound ElasticityBoundaryScaling
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryMVCalculus
  ElasticityBoundaryTensorSeries ElasticityBoundaryProfileBounds ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
lemma measurable_H : MeasurableSet H :=
  (isOpen_lt (continuous_const : Continuous (fun _ : X => (0:ℝ)))
    (EuclideanSpace.proj 2).continuous).measurableSet

lemma integral_ofLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Y → F) : (∫ x in H, f x.ofLp)=∫ y in halfspace, f y := by
  rw [← integral_indicator measurable_H,← integral_indicator measurable_halfspace]
  have hh (x : X) : H.indicator (fun x => f x.ofLp) x=halfspace.indicator f x.ofLp := rfl
  simp_rw [hh]
  exact (PiLp.volume_preserving_ofLp I).integral_comp
    (PiLp.homeomorph 2 (fun _ : I => ℝ)).measurableEmbedding _

end ElasticityBoundaryPacketMass

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
namespace ElasticityBoundaryPacket
/-! Actual smooth compact physical fields selected from the curved boundary
parametrix, on an arbitrary honest smooth domain. -/
open Set MeasureTheory Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryCutoffLayer ElasticityBoundaryCutoffParametrix ElasticityBoundaryPacketMass
  ElasticityBoundaryGradientMass ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryStrongLayer
  ElasticityBoundaryLocalParametrix ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
  ElasticityBoundaryProfileBounds ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.field_gradient_mass_oai (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i d,
      (∫ z in Ω, ‖dd (s.field q δ i) (basis d) z‖^2)≤C := by
  obtain ⟨A,hA,hbound⟩ := transferred_gradient_mass s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Ψ s.Φ_smooth s.Ψ_smooth s.Φ_germ s.Ψ_germ
  choose B hB hBbound using cutoff_gradient_bound s.cutoff_smooth s.cutoff_compact q
  refine ⟨A*∑ j, ∑ α, B j α,mul_nonneg hA
    (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun α _ => hB j α))),fun δ hδ hδ1 i d => ?_⟩
  apply (hbound _ (smooth_cutoffLayer s.cutoff_smooth q δ) (s.cutoff_layer_support q δ) i d).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro α _
  rw [integral_ofLp (fun y => ‖dpart (cutoffLayer s.cutoff q δ j) α y‖^2)]
  exact (hBbound j α δ hδ hδ1).2

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass_oai := @OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass_oai
