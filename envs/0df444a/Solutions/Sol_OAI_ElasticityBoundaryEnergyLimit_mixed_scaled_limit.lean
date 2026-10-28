-- Prove2me | solution 1 for OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:48:33.385602+00:00
-- url     : https://prove2.me/submissions/cddf7d92-0962-41fd-ab7e-3c37d4874766

import Mathlib
import Definitions.Def_OAIQ6El001

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

lemma scale_zero (y : Y) : scale 0 y = 0 := by
  ext i
  simp [scaleFactor]

lemma continuous_scale_at (y : Y) : Continuous (fun δ : ℝ => scale δ y) := by
  apply continuous_pi
  intro i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> fun_prop

lemma scale_tendsto_zero (y : Y) : Filter.Tendsto (fun δ : ℝ => scale δ y) (nhds 0) (nhds 0) := by
  simpa only [scale_zero] using (continuous_scale_at y).tendsto 0

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
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

lemma PD_apply (j : Fin 3) (q : Polynomial MP) :
    PD j q=coeffMap (E₀ j) q+Polynomial.X*coeffMap (E₁ j) q := rfl

end ElasticityBoundaryParameter

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

end ElasticityBoundaryOrderBound

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

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer

lemma eventually_small_positive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0<δ ∧ δ≤1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with δ hδ h1
  exact ⟨hδ,h1.le⟩

lemma OrderBound.conj {F : ℝ → Y → ℂ} {k : ℕ} (hF : OrderBound F k) :
    OrderBound (fun δ y => star (F δ y)) k := by
  obtain ⟨A,hA,n,h⟩ := hF
  exact ⟨A,hA,n,fun δ hδ h1 y => by simpa only [norm_star] using h δ hδ h1 y⟩

/-- Domination uses the full Gaussian-normal weight, and is uniform for every
small positive scale. No convergence of the physical DN symbol is assumed. -/
theorem weighted_tendsto {F : ℝ → Y → ℂ} {f : Y → ℂ}
    (hF : OrderBound F 0) (hc : ∀ δ, Continuous (F δ))
    (ht : ∀ y, Tendsto (fun δ => F δ y) (𝓝[>] 0) (𝓝 (f y)))
    {b : ℝ} (hb : 0<b) :
    Tendsto (fun δ => ∫ y, weight b y • F δ y) (𝓝[>] 0) (𝓝 (∫ y, weight b y • f y)) := by
  obtain ⟨A,hA,n,hB⟩ := hF
  let g : Y → ℝ := fun y => (A*2^n)*(weight b y+‖y‖^n*weight b y)
  have hg : Integrable g := ((integrable_weight hb).add (integrable_norm_moment hb n)).const_mul _
  apply tendsto_integral_filter_of_dominated_convergence g
  · exact Eventually.of_forall (fun δ => (measurable_weight b).aestronglyMeasurable.smul
      (hc δ).aestronglyMeasurable)
  · filter_upwards [eventually_small_positive] with δ hδ
    exact Eventually.of_forall (fun y => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg b y)]
      have h := hB δ hδ.1 hδ.2 y
      simp only [pow_zero,mul_one] at h
      calc
        _ ≤ weight b y*(A*(1+‖y‖)^n) := mul_le_mul_of_nonneg_left h (weight_nonneg b y)
        _ ≤ weight b y*(A*(2^n*(1+‖y‖^n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) n) hA)
            (weight_nonneg b y)
        _ = g y := by dsimp [g]; ring)
  · exact hg
  · exact Eventually.of_forall (fun y => tendsto_const_nhds.smul (ht y))

lemma continuous_value_parameter (q : Polynomial MP) (y : Y) :
    Continuous (fun δ : ℝ => value (atParameter q δ) y) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      have he : (fun δ : ℝ => value (atParameter (p+q) δ) y)=
          (fun δ => value (atParameter p δ) y+value (atParameter q δ) y) := by
        funext δ
        rw [atParameter_add,value_add]
      rw [he]
      exact hp.add hq
  | monomial n p =>
      simp_rw [value_parameter_monomial]
      exact continuous_const.mul (Complex.continuous_ofReal.pow n)

lemma value_parameter_zero (q : Polynomial MP) (y : Y) :
    value (atParameter q 0) y=value (q.coeff 0) y := by
  simp only [atParameter,Complex.ofReal_zero,map_zero,← Polynomial.coeff_zero_eq_eval_zero]

lemma PD_coeff_zero (q : Polynomial MP) (β : Fin 3) :
    (PD β q).coeff 0=E₀ β (q.coeff 0) := by
  simp [PD_apply,coeffMap_coeff]

lemma firstScaled_tendsto {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (h0 : χ 0=1)
    (q : Polynomial W) (j β : Fin 3) (y : Y) :
    Tendsto (fun δ => firstScaled χ q δ j β y) (𝓝[>] 0)
      (𝓝 (value (E₀ β (q.coeff 0 j)) y)) := by
  have hχt : Tendsto (fun δ => χ (scale δ y)) (𝓝 (0:ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,h0] using hχ.continuous.continuousAt.tendsto.comp (scale_tendsto_zero y)
  have hpt : Tendsto (fun δ => value (atParameter (PD β (unpack j q)) δ) y)
      (𝓝 (0:ℝ)) (𝓝 (value (E₀ β (q.coeff 0 j)) y)) := by
    simpa only [value_parameter_zero,PD_coeff_zero,unpack,coeffMap_coeff,LinearMap.proj_apply]
      using (continuous_value_parameter (PD β (unpack j q)) y).tendsto 0
  have hdt := (smooth_dpart hχ β).continuous.continuousAt.tendsto.comp (scale_tendsto_zero y)
  have hqt := (continuous_value_parameter (unpack j q) y).tendsto 0
  have ht := (hχt.mul hpt).add (((Complex.continuous_ofReal.tendsto 0).pow 2).mul hdt |>.mul hqt)
  simpa only [Complex.ofReal_zero,zero_pow (by norm_num : 2≠0),zero_mul,one_mul,add_zero,Function.comp_def,firstScaled]
    using ht.mono_left nhdsWithin_le_nhds

end ElasticityBoundaryLimit
namespace ElasticityBoundaryEnergyLimit
/-! Actual normalized mixed energy limits of the corrected, cut-off boundary
layers. The coefficient has its genuine normal factor and arbitrary compact
smooth remainder; all Jacobian and physical-derivative powers are exact. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound

lemma normal_power_bound (n : ℕ) : OrderBound (fun (_ : ℝ) (y : Y) => (y 2:ℂ)^n) 0 := by
  refine ⟨1,by norm_num,n,fun δ _ _ y => ?_⟩
  simp only [pow_zero,mul_one,one_mul,norm_pow,Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm y 2).trans (by linarith [norm_nonneg y])) n

lemma mixed_scaled_bound (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (p q : Polynomial W) (i α j β : Fin 3) :
    OrderBound (mixedScaled n H χ p q i α j β) 0 := by
  exact (((normal_power_bound n).mul (compact_scaled hH hcH)).mul
    (first_scaled_bound hχ hcχ p i α)).mul (OrderBound.conj (first_scaled_bound hχ hcχ q j β))

lemma mixed_scaled_continuous (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : Fin 3) (δ : ℝ) :
    Continuous (mixedScaled n H χ p q i α j β δ) :=
  (((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n |>.mul
    (hH.comp (scale δ).continuous)).mul (first_scaled_continuous hχ p δ i α)).mul
    (first_scaled_continuous hχ q δ j β).star

/-- The coefficient at the base point is extracted from the exact mixed
boundary energy. Corrections of every positive parameter order disappear. -/
theorem mixed_scaled_limit_oai (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  apply weighted_tendsto (mixed_scaled_bound n hH hcH hχ hcχ p q i α j β)
    (mixed_scaled_continuous n hH hχ p q i α j β) _ (by norm_num)
  intro y
  have hHt : Tendsto (fun δ => H (scale δ y)) (𝓝[>] 0) (𝓝 (H 0)) :=
    (hH.tendsto 0 |>.comp (scale_tendsto_zero y)).mono_left nhdsWithin_le_nhds
  exact ((tendsto_const_nhds.mul hHt).mul (firstScaled_tendsto hχ h0 p i α y)).mul
    (firstScaled_tendsto hχ h0 q j β y).star

end ElasticityBoundaryEnergyLimit

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit_oai := @OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit_oai
