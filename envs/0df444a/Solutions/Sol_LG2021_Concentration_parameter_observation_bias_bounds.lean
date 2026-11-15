-- Prove2me | solution 1 for LG2021.Concentration.parameter_observation_bias_bounds
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T15:58:40.908889+00:00
-- url     : https://prove2.me/submissions/778c9adc-7ad3-4cc7-8f05-1adc8a28a0f2

import Mathlib
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_GaussianEstimators
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Theorems.Thm_LG2021_nearby_simplex_volume
import Theorems.Thm_LG2021_paper_strong_separation
import Theorems.Thm_LG2021_shallow_ellipsoid_cover
import Theorems.Thm_ModernConvex_Ellipsoids_lowner_fritz_john
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_hasGradient

set_option autoImplicit false

/- LG2021AlgorithmOracle -/
section

/-!
The concrete estimators and stopping rule of Algorithm 1 in Tor Lattimore and
Andras Gyorgy, "Improved regret for zeroth-order stochastic convex bandits",
Proceedings of the 34th Conference on Learning Theory, PMLR 134, 2021.

The positivity test in `eligible` makes the stopping rule total: a zero
lower confidence bound cannot trigger stopping. The moment constants remain
explicit parameters for the formal concentration estimates.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Concentration
open scoped Classical

private instance (u : ℕ) : MeasurableSpace (Option (Fin u)) := ⊤

private instance (u : ℕ) : MeasurableSingletonClass (Option (Fin u)) := ⟨fun _ => trivial⟩

private structure OracleConfig where
  horizon : ℕ
  radius : ℝ
  lambda : ℝ
  momentConstant : ℝ
  concentrationConstant : ℝ

















private theorem measurable_likelihoodRatio {d : ℕ} (lambda : ℝ) :
    Measurable (fun w : Space d × Space d => likelihoodRatio lambda w.1 w.2) := by
  unfold likelihoodRatio
  fun_prop

private theorem measurable_truncation {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => truncation lambda r w.1 w.2) := by
  unfold truncation
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le (measurable_likelihoodRatio lambda) measurable_const).inter
    (measurableSet_le measurable_snd.norm measurable_const)

private theorem measurable_scalarCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => scalarCoefficient lambda r w.1 w.2) := by
  exact ((measurable_const.sub measurable_const).add
    ((measurable_likelihoodRatio lambda).div_const lambda)).mul (measurable_truncation lambda r)

private theorem measurable_gradientCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => gradientCoefficient lambda r w.1 w.2) := by
  exact (((measurable_likelihoodRatio lambda).mul (measurable_truncation lambda r)).div_const
    ((1 - lambda) ^ 2)).smul (by fun_prop)

























end LG2021.Algorithm

end
end

/- LG2021AlgorithmGeometry -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Matrix
open scoped Classical

private instance (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

private instance (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))














































end LG2021.Algorithm

end
end

/- LG2021AlgorithmQuantization -/
section

/-!
An explicit countable approximation of halfspace coefficients. This is an
additional algorithm completion, not a statement asserted in Lattimore–Gyorgy.
It permits measurable canonical ellipsoid choices on countable cut histories.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory
open scoped Classical













































end LG2021.Algorithm

end
end

/- LG2021JohnHelpers -/
section

/-! Small internal adapters reused verbatim from the accepted John-ellipsoid
solution. Their explicit inclusion avoids relying on unexposed helper names in
an external canonical theorem module. The John theorem itself is imported and
reused by its canonical statement. -/

noncomputable section
namespace LG2021.JohnHelpers
open Matrix Finset MeasureTheory ModernConvex.Ellipsoids
open scoped ENNReal



































end LG2021.JohnHelpers

end
end

/- LG2021Geometry -/
section

namespace LG2021

open Set ModernConvex.Ellipsoids



open Matrix











end LG2021

end

/- LG2021AlgorithmSelector -/
section

/-!
A canonical minimum enclosing ellipsoid is chosen for each finite rational cut
history. The history space is countable, so this choice is measurable without
an additional measurable-selection principle.

The geometric existence and rounding facts reuse the proved Loewner–Fritz John
theorem. The countable-history adapter is an additional algorithm completion.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical









































end LG2021.Algorithm

end
end

/- LG2021AlgorithmState -/
section

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace LG2021.Algorithm

open MeasureTheory Concentration
open scoped Classical



































end LG2021.Algorithm

end
end

/- CorollaryTransport -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal







end BilateralProfitMHR.CorollaryTransport

end
end

/- LG2021GaussianGeometrySphere -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory

private theorem measurable_gaussian_normalize (d : ℕ) (R : ℝ) :
    Measurable (fun x : Space d => (R / ‖x‖) • x) := by fun_prop

private instance sphereMeasure_probability (d : ℕ) (R : ℝ) :
    IsProbabilityMeasure (sphereMeasure d R) := by
  unfold sphereMeasure
  exact Measure.isProbabilityMeasure_map (measurable_gaussian_normalize d R).aemeasurable









end LG2021

end
end

/- Normalized Gaussian norm support -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory





end LG2021

end
end

/- LG2021AlgorithmPolicy -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory BilateralProfitMHR
open scoped Classical

/-- Independent candidate blocks and Gaussian query vectors for all possible
stages before the fixed horizon. Beyond the horizon the seed is extended by zero. -/
private abbrev Seed (d u n : ℕ) := (Fin (n + 1) → Fin u → Space d) × (Fin (n + 1) → Space d)





























private def seedMeasure (d u : ℕ) (cfg : OracleConfig) : Measure (Seed d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))).prod
      (Measure.pi (fun _ : Fin (cfg.horizon + 1) => gaussian d))

private instance seedMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (seedMeasure d u cfg) := by
  unfold seedMeasure
  infer_instance







end LG2021.Algorithm

end
end

/- CorollaryNormalization -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal




end BilateralProfitMHR.CorollaryTransport

end
end

/- LG2021Process -/
section

namespace LG2021

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal





















end LG2021

end

/- LG2021Concentration -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A global second-order upper bound for the real exponential. -/
private theorem exp_le_one_add_add_sq_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num [Finset.sum_range_succ, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_pow,
    Complex.norm_real, Real.norm_eq_abs] at h
  have h' : Real.exp x - (1 + x) ≤ x ^ 2 * Real.exp |x| :=
    (le_abs_self _).trans h
  linarith

/-- A quadratic-times-exponential envelope, used for centered moment bounds. -/
private theorem sq_mul_exp_abs_le_exp_sq (v s : ℝ) (hs : |s| ≤ 1 / 2) :
    v ^ 2 * Real.exp |s * v| ≤ 4 * Real.exp (v ^ 2) := by
  have hpow : v ^ 2 ≤ 2 * Real.exp (v ^ 2 / 2) := by
    have := Real.add_one_le_exp (v ^ 2 / 2)
    linarith
  have harg : |s * v| ≤ v ^ 2 / 2 + 1 / 8 := by
    rw [abs_mul]
    have hv := sq_nonneg (|v| - 1 / 2)
    nlinarith [sq_abs v, mul_le_mul_of_nonneg_right hs (abs_nonneg v)]
  have he : Real.exp (1 / 8 : ℝ) ≤ 2 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  calc
    v ^ 2 * Real.exp |s * v| ≤
        (2 * Real.exp (v ^ 2 / 2)) * Real.exp (v ^ 2 / 2 + 1 / 8) := by
      exact mul_le_mul hpow (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
    _ = 2 * Real.exp (v ^ 2) * Real.exp (1 / 8) := by
      have heq : Real.exp (v ^ 2 / 2) * Real.exp (v ^ 2 / 2) = Real.exp (v ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.exp_add]
      calc
        _ = 2 * (Real.exp (v ^ 2 / 2) * Real.exp (v ^ 2 / 2)) * Real.exp (1 / 8) := by ring
        _ = _ := by rw [heq]
    _ ≤ 4 * Real.exp (v ^ 2) := by nlinarith [Real.exp_pos (v ^ 2)]

/-- The small-parameter exponential envelope retains its linear term, which vanishes on centering. -/
private theorem exp_mul_le_small_parameter (v s : ℝ) (hs : |s| ≤ 1 / 2) :
    Real.exp (s * v) ≤ 1 + s * v + 4 * s ^ 2 * Real.exp (v ^ 2) := by
  have h := exp_le_one_add_add_sq_mul_exp_abs (s * v)
  have h' := mul_le_mul_of_nonneg_left (sq_mul_exp_abs_le_exp_sq v s hs) (sq_nonneg s)
  nlinarith

/-- Every exponential linear moment is dominated by a Gaussian-square moment. -/
private theorem exp_mul_le_exp_sq (v s : ℝ) :
    Real.exp (s * v) ≤ Real.exp (s ^ 2 / 4) * Real.exp (v ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (v - s / 2)]

/-- A finite exponential-square moment gives integrability of every linear exponential. -/
private theorem integrable_exp_mul_of_exp_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * X ω)) P := by
  apply (hI.const_mul (Real.exp (s ^ 2 / 4))).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      exp_mul_le_exp_sq (X ω) s

/-- Centered exponential-square moments imply a sub-Gaussian MGF, with a universal constant. -/
private theorem hasSubgaussianMGF_of_unit_exp_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2) ∂P) ≤ 2)
    (hzero : (∫ ω, X ω ∂P) = 0) :
    HasSubgaussianMGF X 16 P := by
  have hXI : Integrable X P := by
    apply hI.mono' hX.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      have h := Real.add_one_le_exp ((X ω) ^ 2)
      nlinarith [sq_nonneg (|X ω| - 1 / 2), sq_abs (X ω)]
  refine ⟨integrable_exp_mul_of_exp_square P X hX hI, ?_⟩
  intro s
  change (∫ ω, Real.exp (s * X ω) ∂P) ≤ Real.exp (16 * s ^ 2 / 2)
  by_cases hs : |s| ≤ 1 / 2
  · have hJ : Integrable (fun ω => 1 + s * X ω +
        4 * s ^ 2 * Real.exp ((X ω) ^ 2)) P :=
      ((integrable_const 1).add (hXI.const_mul s)).add (hI.const_mul (4 * s ^ 2))
    calc
      _ ≤ ∫ ω, 1 + s * X ω + 4 * s ^ 2 * Real.exp ((X ω) ^ 2) ∂P :=
        integral_mono (integrable_exp_mul_of_exp_square P X hX hI s) hJ
          (fun ω => exp_mul_le_small_parameter (X ω) s hs)
      _ = 1 + 4 * s ^ 2 * (∫ ω, Real.exp ((X ω) ^ 2) ∂P) := by
        have hA : Integrable (fun ω => 1 + s * X ω) P :=
          (integrable_const 1).add (hXI.const_mul s)
        rw [integral_add hA (hI.const_mul (4 * s ^ 2)),
          integral_add (integrable_const 1) (hXI.const_mul s)]
        simp [integral_const_mul, hzero]
      _ ≤ 1 + 8 * s ^ 2 := by nlinarith [sq_nonneg s]
      _ ≤ Real.exp (16 * s ^ 2 / 2) := by
        have h := Real.add_one_le_exp (8 * s ^ 2)
        convert h using 1 <;> ring_nf
  · have hs2 : 1 / 4 ≤ s ^ 2 := by
      have := lt_of_not_ge hs
      nlinarith [sq_abs s, sq_nonneg (|s| - 1 / 2)]
    calc
      _ ≤ ∫ ω, Real.exp (s ^ 2 / 4) * Real.exp ((X ω) ^ 2) ∂P :=
        integral_mono (integrable_exp_mul_of_exp_square P X hX hI s)
          (hI.const_mul _) (fun ω => exp_mul_le_exp_sq (X ω) s)
      _ = Real.exp (s ^ 2 / 4) * (∫ ω, Real.exp ((X ω) ^ 2) ∂P) := integral_const_mul _ _
      _ ≤ Real.exp (s ^ 2 / 4) * 2 := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
      _ ≤ Real.exp (s ^ 2 / 4) * Real.exp 1 := by
        gcongr
        have := Real.add_one_le_exp (1 : ℝ)
        norm_num at this ⊢
        exact this
      _ = Real.exp (s ^ 2 / 4 + 1) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (16 * s ^ 2 / 2) := Real.exp_le_exp.mpr (by nlinarith)

/-- Exponential-square control at a positive radius implies the standard MGF predicate. -/
private theorem hasSubgaussianMGF_of_exp_square {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2)
    (hzero : (∫ ω, X ω ∂P) = 0) :
    HasSubgaussianMGF X (⟨16 * r ^ 2, by positivity⟩ : ℝ≥0) P := by
  have hY := hasSubgaussianMGF_of_unit_exp_square P (fun ω => X ω / r)
    (hX.div_const r) (by simpa only [div_pow] using hI)
    (by simpa only [div_pow] using hM) (by simp [integral_div, hzero])
  have hscale := (hY.const_mul r)
  have hfun : (fun ω => r * (X ω / r)) = X := by
    funext ω
    field_simp [ne_of_gt hr]
  rw [hfun] at hscale
  refine ⟨hscale.integrable_exp_mul, ?_⟩
  intro t
  have h := hscale.mgf_le t
  change mgf X P t ≤ Real.exp ((r ^ 2 * 16) * t ^ 2 / 2) at h
  change mgf X P t ≤ Real.exp ((16 * r ^ 2) * t ^ 2 / 2)
  convert h using 1 <;> ring_nf








end LG2021.Concentration

end

/- LG2021ConcentrationProducts -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Exponential-square envelopes control a product without an independence hypothesis. -/
private theorem exp_abs_mul_le_average_exp_sq (u v : ℝ) :
    Real.exp |u * v| ≤ (Real.exp (u ^ 2) + Real.exp (v ^ 2)) / 2 := by
  have harg : |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v]
  have hconv := convexOn_exp.2 (Set.mem_univ (u ^ 2)) (Set.mem_univ (v ^ 2))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconv
  calc
    _ ≤ Real.exp ((u ^ 2 + v ^ 2) / 2) := Real.exp_le_exp.mpr harg
    _ = Real.exp ((1 / 2) * u ^ 2 + (1 / 2) * v ^ 2) := by congr 1; ring
    _ ≤ (1 / 2) * Real.exp (u ^ 2) + (1 / 2) * Real.exp (v ^ 2) := hconv
    _ = _ := by ring

/-- Two exponential-square bounds give an exponential-absolute moment for their product. -/
private theorem exp_abs_product_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXI : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P)
    (hYI : Integrable (fun ω => Real.exp ((Y ω) ^ 2)) P)
    (hXM : (∫ ω, Real.exp ((X ω) ^ 2) ∂P) ≤ 2)
    (hYM : (∫ ω, Real.exp ((Y ω) ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp |X ω * Y ω|) P ∧
      (∫ ω, Real.exp |X ω * Y ω| ∂P) ≤ 2 := by
  have hJ := (hXI.add hYI).div_const 2
  have hI : Integrable (fun ω => Real.exp |X ω * Y ω|) P := by
    apply hJ.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using
        exp_abs_mul_le_average_exp_sq (X ω) (Y ω)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ ω, (Real.exp ((X ω) ^ 2) + Real.exp ((Y ω) ^ 2)) / 2 ∂P :=
      integral_mono hI hJ (fun ω => exp_abs_mul_le_average_exp_sq (X ω) (Y ω))
    _ = ((∫ ω, Real.exp ((X ω) ^ 2) ∂P) +
        (∫ ω, Real.exp ((Y ω) ^ 2) ∂P)) / 2 := by
      rw [integral_div, integral_add hXI hYI]
    _ ≤ 2 := by linarith

/-- The product estimate at arbitrary positive radii. -/
private theorem exp_abs_product_moment_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / a ^ 2)) P)
    (hYI : Integrable (fun ω => Real.exp ((Y ω) ^ 2 / b ^ 2)) P)
    (hXM : (∫ ω, Real.exp ((X ω) ^ 2 / a ^ 2) ∂P) ≤ 2)
    (hYM : (∫ ω, Real.exp ((Y ω) ^ 2 / b ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω * Y ω| / (a * b))) P ∧
      (∫ ω, Real.exp (|X ω * Y ω| / (a * b)) ∂P) ≤ 2 := by
  have h := exp_abs_product_moment P (fun ω => X ω / a) (fun ω => Y ω / b)
    (hX.div_const a) (hY.div_const b)
    (by simpa only [div_pow] using hXI) (by simpa only [div_pow] using hYI)
    (by simpa only [div_pow] using hXM) (by simpa only [div_pow] using hYM)
  simpa only [div_mul_div_comm, abs_div, abs_of_pos (mul_pos ha hb)] using h









end LG2021.Concentration

end

/- LG2021ConcentrationCentering -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Exponential-absolute moments control the first absolute moment. -/
private theorem integral_abs_le_one_of_exp_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp |X ω|) P)
    (hM : (∫ ω, Real.exp |X ω| ∂P) ≤ 2) :
    Integrable X P ∧ (∫ ω, |X ω| ∂P) ≤ 1 ∧ |∫ ω, X ω ∂P| ≤ 1 := by
  have hXI : Integrable X P := by
    apply hI.mono' hX.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have := Real.add_one_le_exp |X ω|
    linarith
  have hXA : Integrable (fun ω => |X ω|) P := hXI.abs
  have hA : (∫ ω, |X ω| ∂P) ≤ 1 := by
    have hJA : Integrable (fun ω => 1 + |X ω|) P := (integrable_const 1).add hXA
    have h := integral_mono hJA hI
      (fun ω => by simpa only [add_comm] using Real.add_one_le_exp |X ω|)
    rw [integral_add (integrable_const 1) hXA] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith
  refine ⟨hXI, hA, ?_⟩
  have h := norm_integral_le_integral_norm (μ := P) X
  simp only [Real.norm_eq_abs] at h
  exact h.trans hA

/-- A pointwise envelope for the centered exponential-absolute moment. -/
private theorem exp_abs_sub_quarter_le (x a : ℝ) (ha : |a| ≤ 1) :
    Real.exp (|x - a| / 4) ≤ (4 / 3) * (3 / 4 + Real.exp |x| / 4) := by
  have harg : |x - a| / 4 ≤ |x| / 4 + 1 / 4 := by
    have := abs_sub x a
    linarith
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ |x|)
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hconv' : Real.exp (|x| / 4) ≤ 3 / 4 + Real.exp |x| / 4 := by
    have heq1 : (1 / 4 : ℝ) * |x| = |x| / 4 := by ring
    have heq2 : (1 / 4 : ℝ) * Real.exp |x| = Real.exp |x| / 4 := by ring
    simpa only [heq1, heq2] using hconv
  calc
    _ ≤ Real.exp (|x| / 4 + 1 / 4) := Real.exp_le_exp.mpr harg
    _ = Real.exp (|x| / 4) * Real.exp (1 / 4) := Real.exp_add _ _
    _ ≤ (3 / 4 + Real.exp |x| / 4) * (4 / 3) :=
      mul_le_mul hconv' hquarter (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Centering costs at most a factor four in the exponential-absolute scale. -/
private theorem exp_abs_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp |X ω|) P)
    (hM : (∫ ω, Real.exp |X ω| ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / 4)) P ∧
      (∫ ω, Real.exp (|X ω - ∫ a, X a ∂P| / 4) ∂P) ≤ 2 ∧
      (∫ ω, (X ω - ∫ a, X a ∂P) ∂P) = 0 := by
  obtain ⟨hXI, _, hmean⟩ := integral_abs_le_one_of_exp_abs P X hX hI hM
  have hJ : Integrable (fun ω => (4 / 3) * (3 / 4 + Real.exp |X ω| / 4)) P :=
    ((integrable_const (3 / 4 : ℝ)).add (hI.div_const 4)).const_mul (4 / 3)
  have hEI : Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / 4)) P := by
    apply hJ.mono' (by fun_prop)
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      exp_abs_sub_quarter_le (X ω) (∫ a, X a ∂P) hmean
  refine ⟨hEI, ?_, ?_⟩
  · calc
      _ ≤ ∫ ω, (4 / 3) * (3 / 4 + Real.exp |X ω| / 4) ∂P :=
        integral_mono hEI hJ (fun ω => exp_abs_sub_quarter_le (X ω) _ hmean)
      _ = (4 / 3) * (3 / 4 + (∫ ω, Real.exp |X ω| ∂P) / 4) := by
        rw [integral_const_mul, integral_add (integrable_const (3 / 4 : ℝ)) (hI.div_const 4)]
        simp [integral_div]
      _ ≤ 2 := by linarith
  · rw [integral_sub hXI (integrable_const _)]
    simp


/-- Centering at an arbitrary exponential-absolute radius. -/
private theorem exp_abs_centered_moment_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp (|X ω| / r)) P)
    (hM : (∫ ω, Real.exp (|X ω| / r) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r))) P ∧
      (∫ ω, Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r)) ∂P) ≤ 2 ∧
      (∫ ω, (X ω - ∫ a, X a ∂P) ∂P) = 0 := by
  have hI' : Integrable (fun ω => Real.exp |X ω / r|) P := by
    simpa only [abs_div, abs_of_pos hr] using hI
  have hM' : (∫ ω, Real.exp |X ω / r| ∂P) ≤ 2 := by
    simpa only [abs_div, abs_of_pos hr] using hM
  have h := exp_abs_centered_moment P (fun ω => X ω / r) (hX.div_const r) hI' hM'
  have heq : (fun ω => Real.exp (|X ω / r - ∫ a, X a / r ∂P| / 4)) =
      (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r))) := by
    funext ω
    rw [integral_div, ← sub_div, abs_div, abs_of_pos hr]
    congr 1
    ring
  refine ⟨heq ▸ h.1, heq ▸ h.2.1, ?_⟩
  have hXI' := (integral_abs_le_one_of_exp_abs P (fun ω => X ω / r)
    (hX.div_const r) hI' hM').1.const_mul r
  have hfun : (fun ω => r * (X ω / r)) = X := by
    funext ω
    field_simp [ne_of_gt hr]
  rw [hfun] at hXI'
  rw [integral_sub hXI' (integrable_const _)]
  simp


end LG2021.Concentration

end

/- LG2021ConcentrationEstimators -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem likelihoodRatio_nonneg {d : ℕ} {lambda : ℝ} (hlambda : lambda < 1)
    (z x : Space d) : 0 ≤ likelihoodRatio lambda z x := by
  unfold likelihoodRatio
  positivity

private theorem truncation_zero_or_one {d : ℕ} (lambda r : ℝ) (z x : Space d) :
    truncation lambda r z x = 0 ∨ truncation lambda r z x = 1 := by
  unfold truncation
  split_ifs <;> simp

private theorem truncation_eq_one_iff {d : ℕ} (lambda r : ℝ) (z x : Space d) :
    truncation lambda r z x = 1 ↔
      likelihoodRatio lambda z x ≤ Real.exp 1 / (1 - lambda) ^ d ∧
      ‖x‖ ≤ r / (d : ℝ) := by
  unfold truncation
  split_ifs <;> simp_all

/-- Bernoulli's inequality bounds the likelihood-ratio cutoff uniformly in dimension. -/
private theorem likelihood_cutoff_le_six {d : ℕ} {lambda : ℝ}
    (hlambda : 0 ≤ lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2) :
    Real.exp 1 / (1 - lambda) ^ d ≤ 6 := by
  have hpow : (1 / 2 : ℝ) ≤ (1 - lambda) ^ d := by
    have h := one_add_mul_le_pow (a := -lambda) (by linarith : (-2 : ℝ) ≤ -lambda) d
    simp only [mul_neg, ← sub_eq_add_neg] at h
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (1 - lambda) ^ d)).2
  have hexp := Real.exp_one_lt_three
  nlinarith

/-- The scalar multiplier is uniformly bounded after truncation. -/
private theorem abs_scalarCoefficient_le {d : ℕ} {lambda : ℝ} (r : ℝ) (z x : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2) :
    |scalarCoefficient lambda r z x| ≤ 7 / lambda := by
  have hR := likelihoodRatio_nonneg (show lambda < 1 by linarith) z x
  rcases truncation_zero_or_one lambda r z x with hI | hI
  · simp only [scalarCoefficient, hI, mul_zero, abs_zero]
    positivity
  · have hRmax := ((truncation_eq_one_iff lambda r z x).1 hI).1
    have hR6 := hRmax.trans (likelihood_cutoff_le_six hpos.le hsmall hd)
    rw [scalarCoefficient, hI, mul_one]
    have heq : 1 - 1 / lambda + likelihoodRatio lambda z x / lambda =
        (lambda - 1 + likelihoodRatio lambda z x) / lambda := by
      field_simp [ne_of_gt hpos]
    rw [heq, abs_div, abs_of_pos hpos]
    apply div_le_div_of_nonneg_right _ hpos.le
    apply abs_le.mpr
    constructor <;> linarith

/-- The directional multiplier retains the one-dimensional Gaussian projection. -/
private theorem abs_gradientWeight_le {d : ℕ} {lambda : ℝ}
    (r : ℝ) (z x : Space d) (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2)
    (hd : (d : ℝ) * lambda ≤ 1 / 2) :
    |likelihoodRatio lambda z x * truncation lambda r z x / (1 - lambda) ^ 2| ≤ 24 := by
  have hR := likelihoodRatio_nonneg (show lambda < 1 by linarith) z x
  rcases truncation_zero_or_one lambda r z x with hI | hI
  · simp [hI]
  · have hRmax := ((truncation_eq_one_iff lambda r z x).1 hI).1
    have hR6 := hRmax.trans (likelihood_cutoff_le_six hpos.le hsmall hd)
    have hden : (1 / 4 : ℝ) ≤ (1 - lambda) ^ 2 := by nlinarith
    simp only [hI, mul_one, abs_of_nonneg (div_nonneg hR (sq_nonneg _))]
    apply (div_le_iff₀ (by positivity : 0 < (1 - lambda) ^ 2)).2
    nlinarith




end LG2021.Concentration

end

/- LG2021ConcentrationObservation -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A bounded deterministic mean can be added to normalized square-exponential noise. -/
private theorem exp_square_shift_envelope (x a : ℝ) (ha : |a| ≤ 1) :
    Real.exp ((x + a) ^ 2 / 16) ≤ (4 / 3) * (3 / 4 + Real.exp (x ^ 2) / 4) := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
  have harg : (x + a) ^ 2 / 16 ≤ x ^ 2 / 4 + 1 / 4 := by
    nlinarith [sq_nonneg (x - a), sq_nonneg x]
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (x ^ 2))
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hconv' : Real.exp (x ^ 2 / 4) ≤ 3 / 4 + Real.exp (x ^ 2) / 4 := by
    have heq1 : (1 / 4 : ℝ) * x ^ 2 = x ^ 2 / 4 := by ring
    have heq2 : (1 / 4 : ℝ) * Real.exp (x ^ 2) = Real.exp (x ^ 2) / 4 := by ring
    simpa only [heq1, heq2] using hconv
  calc
    _ ≤ Real.exp (x ^ 2 / 4 + 1 / 4) := Real.exp_le_exp.mpr harg
    _ = Real.exp (x ^ 2 / 4) * Real.exp (1 / 4) := Real.exp_add _ _
    _ ≤ (3 / 4 + Real.exp (x ^ 2) / 4) * (4 / 3) :=
      mul_le_mul hconv' hquarter (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The shifted observation has an explicit exponential-square radius four. -/
private theorem exp_square_observation_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {a : ℝ} (ha : |a| ≤ 1)
    (hI : Integrable (fun ω => Real.exp ((X ω - a) ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω - a) ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / 16)) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / 16) ∂P) ≤ 2 := by
  have hJ : Integrable (fun ω => (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4)) P :=
    ((integrable_const (3 / 4 : ℝ)).add (hI.div_const 4)).const_mul (4 / 3)
  have hbound (ω : Ω) : Real.exp ((X ω) ^ 2 / 16) ≤
      (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4) := by
    simpa only [sub_add_cancel] using exp_square_shift_envelope (X ω - a) a ha
  have hEI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / 16)) P := by
    apply hJ.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hbound ω
  refine ⟨hEI, ?_⟩
  calc
    _ ≤ ∫ ω, (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4) ∂P :=
      integral_mono hEI hJ hbound
    _ = (4 / 3) * (3 / 4 + (∫ ω, Real.exp ((X ω - a) ^ 2) ∂P) / 4) := by
      rw [integral_const_mul, integral_add (integrable_const (3 / 4 : ℝ)) (hI.div_const 4)]
      simp [integral_div]
    _ ≤ 2 := by linarith




/-- Centering an uncentered square-exponential variable costs a universal factor four. -/
private theorem exp_square_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2) ∂P) ≤ 2) :
    Integrable X P ∧
    Integrable (fun ω => Real.exp ((X ω - ∫ a, X a ∂P) ^ 2 / 16)) P ∧
      (∫ ω, Real.exp ((X ω - ∫ a, X a ∂P) ^ 2 / 16) ∂P) ≤ 2 := by
  have hXI : Integrable X P := by
    apply hI.mono' hX.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have h := Real.add_one_le_exp ((X ω) ^ 2)
    nlinarith [sq_nonneg (|X ω| - 1 / 2), sq_abs (X ω)]
  have hX2I : Integrable (fun ω => (X ω) ^ 2) P := by
    apply hI.mono' (by fun_prop)
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := Real.add_one_le_exp ((X ω) ^ 2)
    linarith
  have hJ : Integrable (fun ω => 1 + (X ω) ^ 2) P := (integrable_const 1).add hX2I
  have hX2 : (∫ ω, (X ω) ^ 2 ∂P) ≤ 1 := by
    have h := integral_mono hJ hI (fun ω => by simpa [add_comm] using Real.add_one_le_exp ((X ω) ^ 2))
    rw [integral_add (integrable_const 1) hX2I] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith
  have hXA : (∫ ω, |X ω| ∂P) ≤ 1 := by
    have h := integral_mono hXI.abs (hJ.div_const 2) (fun ω =>
      show |X ω| ≤ (1 + (X ω) ^ 2) / 2 by nlinarith [sq_nonneg (|X ω| - 1), sq_abs (X ω)])
    rw [integral_div, integral_add (integrable_const 1) hX2I] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith
  have hmean : |∫ a, X a ∂P| ≤ 1 := by
    have h := norm_integral_le_integral_norm (μ := P) X
    simp only [Real.norm_eq_abs] at h
    exact h.trans hXA
  have h := exp_square_observation_moment P (fun ω => X ω - ∫ a, X a ∂P)
    (hX.sub_const _) (a := -(∫ a, X a ∂P)) (by simpa only [abs_neg] using hmean)
    (by simpa only [sub_neg_eq_add, sub_add_cancel] using hI)
    (by simpa only [sub_neg_eq_add, sub_add_cancel] using hM)
  exact ⟨hXI, h⟩


/-- The centered square-exponential estimate at an arbitrary positive scale. -/
private theorem exp_square_centered_moment_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2) :
    Integrable X P ∧
    Integrable (fun ω => Real.exp ((X ω - ∫ a, X a ∂P) ^ 2 / (4 * r) ^ 2)) P ∧
      (∫ ω, Real.exp ((X ω - ∫ a, X a ∂P) ^ 2 / (4 * r) ^ 2) ∂P) ≤ 2 := by
  have h := exp_square_centered_moment P (fun ω => X ω / r) (hX.div_const r)
    (by simpa only [div_pow] using hI) (by simpa only [div_pow] using hM)
  have hXI := h.1.const_mul r
  have hfun : (fun ω => r * (X ω / r)) = X := by
    funext ω
    field_simp [ne_of_gt hr]
  rw [hfun] at hXI
  have heq : (fun ω => Real.exp ((X ω / r - ∫ a, X a / r ∂P) ^ 2 / 16)) =
      (fun ω => Real.exp ((X ω - ∫ a, X a ∂P) ^ 2 / (4 * r) ^ 2)) := by
    funext ω
    rw [integral_div, ← sub_div, div_pow]
    congr 1
    ring
  exact ⟨hXI, heq ▸ h.2⟩

/-- Explicit centered sub-Gaussian MGF control for a raw square-exponential observation. -/
private theorem centered_hasSubgaussianMGF_of_exp_square {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2) :
    Integrable X P ∧
      HasSubgaussianMGF (fun ω => X ω - ∫ a, X a ∂P)
        (⟨256 * r ^ 2, by positivity⟩ : NNReal) P := by
  obtain ⟨hXI, hCI, hCM⟩ := exp_square_centered_moment_scaled P X hX hr hI hM
  have h := hasSubgaussianMGF_of_exp_square P (fun ω => X ω - ∫ a, X a ∂P)
    (hX.sub_const _) (r := 4 * r) (by positivity) hCI hCM (by
      rw [integral_sub hXI (integrable_const _)]
      simp)
  refine ⟨hXI, h.integrable_exp_mul, ?_⟩
  intro t
  have hb := h.mgf_le t
  change mgf (fun ω => X ω - ∫ a, X a ∂P) P t ≤
    Real.exp ((16 * (4 * r) ^ 2) * t ^ 2 / 2) at hb
  change mgf (fun ω => X ω - ∫ a, X a ∂P) P t ≤
    Real.exp ((256 * r ^ 2) * t ^ 2 / 2)
  convert hb using 1 <;> ring_nf


end LG2021.Concentration

end

/- LG2021ConcentrationKernelMoments -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A uniform conditional nonnegative moment transfers to the joint law of a query and observation. -/
private theorem compProd_snd_moment_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (κ : Kernel A B) [IsMarkovKernel κ]
    (f : B → ℝ) (hf : Measurable f) (hfnonneg : ∀ y, 0 ≤ f y) (C : ℝ)
    (hcond : ∀ᵐ a ∂P, Integrable f (κ a) ∧ (∫ y, f y ∂κ a) ≤ C) :
    Integrable (fun p : A × B => f p.2) (P ⊗ₘ κ) ∧
      (∫ p, f p.2 ∂(P ⊗ₘ κ)) ≤ C := by
  have hsm : StronglyMeasurable (fun p : A × B => f p.2) := (hf.comp measurable_snd).stronglyMeasurable
  have hJ : Integrable (fun a => ∫ y, ‖f y‖ ∂κ a) P := by
    apply (integrable_const C).mono' hf.stronglyMeasurable.norm.integral_kernel.aestronglyMeasurable
    filter_upwards [hcond] with a ha
    have hpos : 0 ≤ ∫ y, f y ∂κ a := integral_nonneg hfnonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfnonneg _), abs_of_nonneg hpos] using ha.2
  have hI : Integrable (fun p : A × B => f p.2) (P ⊗ₘ κ) :=
    (Measure.integrable_compProd_iff hsm.aestronglyMeasurable).2 ⟨hcond.mono (fun _ h => h.1), hJ⟩
  refine ⟨hI, ?_⟩
  rw [Measure.integral_compProd hI]
  have hJ' : Integrable (fun a => ∫ y, f y ∂κ a) P := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfnonneg _)] using hJ
  calc
    _ ≤ ∫ _a, C ∂P := integral_mono_ae hJ' (integrable_const C) (hcond.mono (fun _ h => h.2))
    _ = C := by simp

/-- A moment of the query is unchanged when a Markov observation is appended. -/
private theorem compProd_fst_moment {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (κ : Kernel A B) [IsMarkovKernel κ]
    (f : A → ℝ) (hf : Measurable f) (hI : Integrable f P) :
    Integrable (fun p : A × B => f p.1) (P ⊗ₘ κ) ∧
      (∫ p, f p.1 ∂(P ⊗ₘ κ)) = ∫ a, f a ∂P := by
  have hsm : StronglyMeasurable (fun p : A × B => f p.1) := (hf.comp measurable_fst).stronglyMeasurable
  have hJ : Integrable (fun p : A × B => f p.1) (P ⊗ₘ κ) := by
    apply (Measure.integrable_compProd_iff hsm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun a =>
        (show Integrable (fun _y : B => f a) (κ a) from integrable_const (f a))
    · simpa using hI.norm
  refine ⟨hJ, ?_⟩
  rw [Measure.integral_compProd hJ]
  simp

/-- A bounded random multiplier preserves the square-exponential radius with the expected scale. -/
private theorem exp_square_bounded_mul_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X A : Ω → ℝ) (hX : Measurable X) (hA : Measurable A)
    {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (hbound : ∀ ω, |A ω| ≤ B)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2)) P ∧
      (∫ ω, Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2) ∂P) ≤ 2 := by
  have hb (ω : Ω) : Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2) ≤
      Real.exp ((X ω) ^ 2 / r ^ 2) := by
    apply Real.exp_le_exp.mpr
    have ha2 : (A ω) ^ 2 ≤ B ^ 2 := by
      nlinarith [hbound ω, abs_nonneg (A ω), sq_abs (A ω)]
    calc
      _ ≤ (B ^ 2 * (X ω) ^ 2) / (B * r) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg (X ω))]
      _ = _ := by field_simp [ne_of_gt hB, ne_of_gt hr]
  have hJ : Integrable (fun ω => Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2)) P := by
    apply hI.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb ω
  exact ⟨hJ, (integral_mono hJ hI hb).trans hM⟩





end LG2021.Concentration

end

/- LG2021GaussianMoments -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal

private theorem gaussian_inner_law {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
  change (stdGaussian (Space d)).map (innerSL ℝ q) = _
  rw [IsGaussian.map_eq_gaussianReal]
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm]

private theorem gaussian_inner_hasSubgaussianMGF {d : ℕ} (q : Space d) :
    HasSubgaussianMGF (fun x => inner ℝ q x) (‖q‖ ^ 2).toNNReal (gaussian d) := by
  apply (HasSubgaussianMGF.id_map_iff (by fun_prop)).1
  rw [gaussian_inner_law]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  simp [mgf_id_gaussianReal]

private theorem gaussian_inner_map {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖q‖ * x) := by
  calc
    _ = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
      change (stdGaussian (Space d)).map (innerSL ℝ q) = _
      rw [IsGaussian.map_eq_gaussianReal]
      simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
        innerSL_apply_norm]
    _ = _ := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        simp

private theorem gaussian_inner_second_moment {d : ℕ} (q : Space d) :
    (∫ x, (inner ℝ q x) ^ 2 ∂gaussian d) = ‖q‖ ^ 2 := by
  have hmean : (∫ x : Space d, inner ℝ q x ∂stdGaussian (Space d)) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ q)
  have hvar := variance_eq_integral (μ := stdGaussian (Space d))
    (X := fun x => inner ℝ q x) (by fun_prop)
  rw [hmean] at hvar
  simp only [sub_zero] at hvar
  change (∫ x : Space d, (inner ℝ q x) ^ 2 ∂stdGaussian (Space d)) = _
  rw [← hvar]
  have heq : (fun x : Space d => inner ℝ q x) = (innerSL ℝ q : Space d → ℝ) := rfl
  rw [heq, variance_dual_stdGaussian, innerSL_apply_norm]

private theorem gaussian_inner_fourth_moment {d : ℕ} (q : Space d) :
    (∫ x, (inner ℝ q x) ^ 4 ∂gaussian d) = 3 * ‖q‖ ^ 4 := by
  calc
    _ = ∫ y : ℝ, y ^ 4 ∂((gaussian d).map (fun x => inner ℝ q x)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ y : ℝ, (‖q‖ * y) ^ 4 ∂gaussianReal 0 1 := by
      rw [gaussian_inner_map, integral_map (by fun_prop) (by fun_prop)]
    _ = _ := by
      simp only [mul_pow, integral_const_mul, OAI.IndependentProducts.gaussian_integral_fourth]
      ring

private theorem gaussian_shift_exp_pdf_bound (s a x : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a| ≤ 1) :
    gaussianPDFReal 0 1 x * Real.exp ((s * x - a) ^ 2 / 64) ≤
      2 * gaussianPDFReal 0 2 x := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hp2 : 0 < 2 * Real.pi := by positivity
  have hp4 : 0 < 4 * Real.pi := by positivity
  have hsqrt2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hp2
  have hsqrt4 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.2 hp4
  have hr2 := Real.sq_sqrt hp2.le
  have hr4 := Real.sq_sqrt hp4.le
  have hratio : (Real.sqrt (2 * Real.pi))⁻¹ ≤
      (3 / 2 : ℝ) * (Real.sqrt (4 * Real.pi))⁻¹ := by
    have hroot : Real.sqrt (4 * Real.pi) ≤ (3 / 2 : ℝ) * Real.sqrt (2 * Real.pi) := by
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), Real.sqrt_nonneg (4 * Real.pi)]
    have hratio' : (1 : ℝ) / Real.sqrt (2 * Real.pi) ≤
        (3 / 2 : ℝ) / Real.sqrt (4 * Real.pi) :=
      (div_le_div_iff₀ hsqrt2 hsqrt4).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hratio'
  have hexp : Real.exp (1 / 32 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 32 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hasq : a ^ 2 ≤ 1 := by
    rcases abs_le.mp ha with ⟨ha0, ha1⟩
    nlinarith
  have hssq : s ^ 2 ≤ 1 := by nlinarith
  have hsxsq : (s * x) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hssq (sq_nonneg x)]
  have harg : -(x ^ 2) / 2 + (s * x - a) ^ 2 / 64 ≤
      1 / 32 - x ^ 2 / 4 := by
    nlinarith [sq_nonneg (s * x + a), sq_nonneg x]
  have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 : ℝ) ≤
      2 * (Real.sqrt (4 * Real.pi))⁻¹ := by
    calc
      _ ≤ ((3 / 2 : ℝ) * (Real.sqrt (4 * Real.pi))⁻¹) * (4 / 3 : ℝ) :=
        mul_le_mul hratio hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  calc
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 - x ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 : ℝ)) *
        Real.exp (-x ^ 2 / 4) := by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ (2 * (Real.sqrt (4 * Real.pi))⁻¹) * Real.exp (-x ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      rw [show 2 * Real.pi * 2 = 4 * Real.pi by ring]
      norm_num
      ring

private theorem gaussianReal_shift_exp_square (s a : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.exp ((s * x - a) ^ 2 / 64)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, Real.exp ((s * x - a) ^ 2 / 64) ∂gaussianReal 0 1) ≤ 2 := by
  have hdom := gaussian_shift_exp_pdf_bound s a
  have hprod : Integrable
      (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp ((s * x - a) ^ 2 / 64)) :=
    ((integrable_gaussianPDFReal 0 2).const_mul 2).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (Real.exp_pos _).le)]
        exact hdom x hs hs1 ha)
  have hint : Integrable (fun x : ℝ => Real.exp ((s * x - a) ^ 2 / 64))
      (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))).2
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hprod
  refine ⟨hint, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x : ℝ, 2 * gaussianPDFReal 0 2 x :=
      integral_mono hprod ((integrable_gaussianPDFReal 0 2).const_mul 2)
        (fun x => hdom x hs hs1 ha)
    _ = 2 := by
      rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 (by norm_num : (2 : ℝ≥0) ≠ 0)]
      norm_num

private theorem gaussian_projection_shift_exp_square {d : ℕ} (q : Space d) (a : ℝ)
    (hq : ‖q‖ ≤ 1) (ha : |a| ≤ 1) :
    Integrable (fun x => Real.exp ((inner ℝ q x - a) ^ 2 / 64)) (gaussian d) ∧
      (∫ x, Real.exp ((inner ℝ q x - a) ^ 2 / 64) ∂gaussian d) ≤ 2 := by
  have h := gaussianReal_shift_exp_square ‖q‖ a (norm_nonneg _) hq ha
  have hmapint : Integrable (fun y : ℝ => Real.exp ((y - a) ^ 2 / 64))
      ((gaussian d).map (fun x => inner ℝ q x)) := by
    rw [gaussian_inner_map]
    exact (integrable_map_measure (f := fun x : ℝ => ‖q‖ * x)
      (g := fun y : ℝ => Real.exp ((y - a) ^ 2 / 64)) (by fun_prop) (by fun_prop)).2 h.1
  have hint : Integrable (fun x => Real.exp ((inner ℝ q x - a) ^ 2 / 64))
      (gaussian d) :=
    (integrable_map_measure (f := fun x : Space d => inner ℝ q x)
      (g := fun y : ℝ => Real.exp ((y - a) ^ 2 / 64)) (by fun_prop) (by fun_prop)).1 hmapint
  refine ⟨hint, ?_⟩
  calc
    _ = ∫ y : ℝ, Real.exp ((y - a) ^ 2 / 64)
        ∂((gaussian d).map (fun x => inner ℝ q x)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x : ℝ, Real.exp ((‖q‖ * x - a) ^ 2 / 64) ∂gaussianReal 0 1 := by
      rw [gaussian_inner_map, integral_map (by fun_prop) (by fun_prop)]
    _ ≤ 2 := h.2

private theorem gaussian_coord_second_moment {d : ℕ} (i : Fin d) :
    (∫ x : Space d, (x i) ^ 2 ∂gaussian d) = 1 := by
  simpa [EuclideanSpace.inner_single_left] using
    gaussian_inner_second_moment (EuclideanSpace.single i (1 : ℝ))

private theorem gaussian_coord_fourth_moment {d : ℕ} (i : Fin d) :
    (∫ x : Space d, (x i) ^ 4 ∂gaussian d) = 3 := by
  simpa [EuclideanSpace.inner_single_left] using
    gaussian_inner_fourth_moment (EuclideanSpace.single i (1 : ℝ))

private theorem gaussian_coord_sq_integrable {d : ℕ} (i : Fin d) :
    Integrable (fun x : Space d => (x i) ^ 2) (gaussian d) := by
  have h := (IsGaussian.memLp_dual (gaussian d)
    (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) 2 (by norm_num)).integrable_sq
  have heq : (fun x : Space d =>
      ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x) ^ 2) = fun x => (x i) ^ 2 := by
    funext x
    simp [EuclideanSpace.inner_single_left]
  simpa only [heq] using h

private theorem gaussian_coord_fourth_integrable {d : ℕ} (i : Fin d) :
    Integrable (fun x : Space d => (x i) ^ 4) (gaussian d) := by
  have h := (IsGaussian.memLp_dual (gaussian d)
    (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) 4 (by norm_num)).integrable_norm_pow
      (by norm_num : (4 : ℕ) ≠ 0)
  have heq : (fun x : Space d =>
      ‖(innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x‖ ^ 4) = fun x => (x i) ^ 4 := by
    funext x
    simp only [innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
      Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
  simpa only [heq] using h

private theorem gaussian_norm_sq_integrable (d : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ 2) (gaussian d) := by
  simpa using (IsGaussian.memLp_id (gaussian d) 2 (by norm_num)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)

private theorem gaussian_norm_fourth_integrable (d : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ 4) (gaussian d) := by
  simpa using (IsGaussian.memLp_id (gaussian d) 4 (by norm_num)).integrable_norm_pow
    (by norm_num : (4 : ℕ) ≠ 0)

private theorem gaussian_norm_second_moment (d : ℕ) :
    (∫ x : Space d, ‖x‖ ^ 2 ∂gaussian d) = d := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => gaussian_coord_sq_integrable i)]
  simp [gaussian_coord_second_moment]

private theorem gaussian_norm_fourth_moment_le (d : ℕ) :
    (∫ x : Space d, ‖x‖ ^ 4 ∂gaussian d) ≤ 3 * (d : ℝ) ^ 2 := by
  have hpoint (x : Space d) : ‖x‖ ^ 4 ≤ (d : ℝ) * ∑ i, (x i) ^ 4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin d => (x i) ^ 2) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, EuclideanSpace.real_norm_sq_eq]
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, mul_comm] using h
  calc
    _ ≤ ∫ x : Space d, (d : ℝ) * ∑ i, (x i) ^ 4 ∂gaussian d :=
      integral_mono (gaussian_norm_fourth_integrable d)
        ((integrable_finsetSum Finset.univ
          (fun i _ => gaussian_coord_fourth_integrable i)).const_mul (d : ℝ)) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => gaussian_coord_fourth_integrable i)]
      simp [gaussian_coord_fourth_moment]
      ring

end LG2021

end
end

/- LG2021ConcentrationEstimatorMoments -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- The actual truncated scalar estimator has a square-exponential radius `28/lambda`.
This is a conditional-kernel form of the moment step in Lemma 4(c) of Tor Lattimore and
András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits,
Proceedings of the 34th Conference on Learning Theory, PMLR 134, 2021. -/
private theorem scalarEstimator_moment {d : ℕ} (P : Measure (Space d)) [IsProbabilityMeasure P]
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hobs : ∀ᵐ x ∂P, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ =>
      Real.exp ((p.2 * scalarCoefficient lambda r z p.1) ^ 2 / (28 / lambda) ^ 2)) (P ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ,
      Real.exp ((p.2 * scalarCoefficient lambda r z p.1) ^ 2 / (28 / lambda) ^ 2)
        ∂(P ⊗ₘ κ)) ≤ 2 := by
  obtain ⟨hI, hM⟩ := compProd_snd_moment_le P κ (fun y : ℝ => Real.exp (y ^ 2 / 16))
    (by fun_prop) (fun _ => (Real.exp_pos _).le) 2 hobs
  have hR : Measurable (fun p : Space d × ℝ => likelihoodRatio lambda z p.1) :=
    (Algorithm.measurable_likelihoodRatio (d := d) lambda).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  have hT : Measurable (fun p : Space d × ℝ => truncation lambda r z p.1) :=
    (Algorithm.measurable_truncation (d := d) lambda r).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  have hC : Measurable (fun _p : Space d × ℝ => (1 - 1 / lambda : ℝ)) := measurable_const
  have hA : Measurable (fun p : Space d × ℝ => scalarCoefficient lambda r z p.1) := by
    exact (hC.add (hR.div_const lambda)).mul hT
  have h := exp_square_bounded_mul_moment (P ⊗ₘ κ) Prod.snd
    (fun p : Space d × ℝ => scalarCoefficient lambda r z p.1) measurable_snd hA
    (r := 4) (B := 7 / lambda) (by norm_num) (by positivity)
    (fun p => abs_scalarCoefficient_le r z p.1 hpos hsmall hd)
    (by simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using hI)
    (by simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using hM)
  have heq : (7 / lambda : ℝ) * 4 = 28 / lambda := by ring
  have hfun : (fun p : Space d × ℝ =>
      Real.exp ((scalarCoefficient lambda r z p.1 * p.2) ^ 2 / ((7 / lambda) * 4) ^ 2)) =
      (fun p : Space d × ℝ =>
        Real.exp ((p.2 * scalarCoefficient lambda r z p.1) ^ 2 / (28 / lambda) ^ 2)) := by
    funext p
    rw [heq, mul_comm (scalarCoefficient lambda r z p.1) p.2]
  exact hfun ▸ h

/-- The gradient estimator is a product of a boundedly weighted observation and a Gaussian projection.
The product-moment step is the admissible-radius form of Lemma 2.7.7 in Roman Vershynin,
High-Dimensional Probability: An Introduction with Applications in Data Science,
Cambridge University Press, 2018, used in Lattimore–György Lemma 4(d). -/
private theorem directionalGradientEstimator_moment {d : ℕ}
    (P : Measure (Space d)) [IsProbabilityMeasure P]
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q)
    (hprojI : Integrable (fun x => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2)) P)
    (hprojM : (∫ x, Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2) ∂P) ≤ 2)
    (hobs : ∀ᵐ x ∂P, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ =>
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))) (P ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ,
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))
        ∂(P ⊗ₘ κ)) ≤ 2 := by
  let A : Space d × ℝ → ℝ := fun p =>
    likelihoodRatio lambda z p.1 * truncation lambda r z p.1 / (1 - lambda) ^ 2
  have hA : Measurable A := by
    exact (((Algorithm.measurable_likelihoodRatio lambda).comp
      (measurable_const.prodMk measurable_fst)).mul
      ((Algorithm.measurable_truncation lambda r).comp
        (measurable_const.prodMk measurable_fst))).div_const _
  obtain ⟨hI, hM⟩ := compProd_snd_moment_le P κ (fun y : ℝ => Real.exp (y ^ 2 / 16))
    (by fun_prop) (fun _ => (Real.exp_pos _).le) 2 hobs
  have hweighted := exp_square_bounded_mul_moment (P ⊗ₘ κ) Prod.snd A measurable_snd hA
    (r := 4) (B := 24) (by norm_num) (by norm_num)
    (fun p => abs_gradientWeight_le r z p.1 hpos hsmall hd)
    (by norm_num at hI ⊢; exact hI) (by norm_num at hM ⊢; exact hM)
  have hprojection := compProd_fst_moment P κ
    (fun x => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2)) (by fun_prop) hprojI
  have h := exp_abs_product_moment_scaled (P ⊗ₘ κ)
    (fun p : Space d × ℝ => A p * p.2) (fun p => inner ℝ (p.1 - lambda • z) η)
    (hA.mul measurable_snd) (by fun_prop) (a := 96) (b := q) (by norm_num) hq
    (by norm_num at hweighted ⊢; exact hweighted.1) hprojection.1
    (by norm_num at hweighted ⊢; exact hweighted.2) (hprojection.2 ▸ hprojM)
  have heq : (fun p : Space d × ℝ =>
      Real.exp (|(A p * p.2) * inner ℝ (p.1 - lambda • z) η| / (96 * q))) =
      (fun p : Space d × ℝ =>
        Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))) := by
    funext p
    simp only [directionalGradientCoefficient, gradientCoefficient, real_inner_smul_left]
    dsimp [A]
    congr 3
    ring
  exact heq ▸ h


/-- The concrete Gaussian-gradient estimator has a universal exponential-absolute radius.
This completes the moment bound corresponding to Lattimore–György Lemma 4(d), with a
larger explicit universal constant and with an arbitrary conditional observation kernel. -/
private theorem gaussian_directionalGradientEstimator_moment {d : ℕ}
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hz : lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ =>
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / 768))
        ((gaussian d) ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ,
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / 768)
        ∂((gaussian d) ⊗ₘ κ)) ≤ 2 := by
  have ha : |lambda * inner ℝ η z| ≤ 1 := by
    rw [abs_mul, abs_of_pos hpos]
    have hi := abs_real_inner_le_norm η z
    calc
      _ ≤ lambda * (‖η‖ * ‖z‖) := mul_le_mul_of_nonneg_left hi hpos.le
      _ ≤ lambda * ‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right hη (norm_nonneg z)]
      _ ≤ 1 := hz
  have hproj := gaussian_projection_shift_exp_square η (lambda * inner ℝ η z) hη ha
  have heq : (fun x : Space d => Real.exp ((inner ℝ η x - lambda * inner ℝ η z) ^ 2 / 64)) =
      (fun x : Space d => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / (8 : ℝ) ^ 2)) := by
    funext x
    rw [← real_inner_comm (x - lambda • z) η, inner_sub_right, real_inner_smul_right]
    norm_num
  rw [heq] at hproj
  have h := directionalGradientEstimator_moment (gaussian d) κ r z η hpos hsmall hd
    (q := 8) (by norm_num) hproj.1 hproj.2 hobs
  norm_num at h ⊢
  exact h


end LG2021.Concentration

end

/- LG2021ConcentrationParameters -/
section

set_option autoImplicit false

namespace LG2021.Concentration

/-- Elementary bounds on the explicit confidence base. -/
private theorem parameterBase_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (10 ^ 6 : ℝ) ≤ parameterBase d D n ∧
      (d : ℝ) + 1 ≤ parameterBase d D n ∧
      D + 1 ≤ parameterBase d D n ∧
      (n : ℝ) + 1 ≤ parameterBase d D n ∧
      3 * (D + 1) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdn : (1 : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  have hDn : (1 : ℝ) ≤ (D + 1) * ((n : ℝ) + 1) := by nlinarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith
  unfold parameterBase
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hDn (show 0 ≤ (d : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdn (show 0 ≤ D + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (show 0 ≤ ((d : ℝ) + 1) * (D + 1) by positivity)]

/-- The explicit confidence logarithm is bounded below and above. -/
private theorem parameterLog_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ parameterLog d D n ∧ parameterLog d D n ≤ 32 * parameterBase d D n := by
  have hb := (parameterBase_bounds d n hD).1
  have hA : 0 < parameterBase d D n := by nlinarith
  have hlower : 1 ≤ Real.log (parameterBase d D n) := by
    apply (Real.le_log_iff_exp_le hA).2
    have h := Real.exp_one_lt_three
    nlinarith
  have hupper := Real.log_le_sub_one_of_pos hA
  unfold parameterLog
  constructor <;> linarith

/-- The confidence choice makes the half-exponential error an exact reciprocal polynomial. -/
private theorem exp_neg_half_parameterLog (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-parameterLog d D n / 2) = (parameterBase d D n)⁻¹ ^ 16 := by
  have hA : 0 < parameterBase d D n := by
    have h := (parameterBase_bounds d n hD).1
    nlinarith
  unfold parameterLog
  rw [show -(32 * Real.log (parameterBase d D n)) / 2 =
      (16 : ℝ) * (-Real.log (parameterBase d D n)) by ring]
  have he := Real.exp_nat_mul (-Real.log (parameterBase d D n)) 16
  norm_num at he
  simpa only [mul_neg, Real.exp_neg, Real.exp_log hA] using he


/-- Basic size bounds for the Gaussian scale in the logarithmic regime. -/
private theorem paperRadius_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 ≤ paperRadius d L ∧
      0 < paperRadius d L ∧ paperRadius d L ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
  have hhi : Real.sqrt (2 * L) ≤ 2 * L := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  unfold paperRadius
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hhi (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]

/-- The contraction parameter is positive and uniformly small. -/
private theorem paperLambda_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    0 < paperLambda d L ∧ paperLambda d L ≤ 1 / 2 ∧
      (d : ℝ) * paperLambda d L ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hLpos : 0 < L := by linarith
  have hden : 0 < (4 * 10 ^ 5 : ℝ) * (d : ℝ) * L := by positivity
  unfold paperLambda
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    have h := mul_le_mul hdR hL (by norm_num) (by positivity)
    nlinarith
  · rw [mul_one_div]
    apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_left hL hdpos.le
    nlinarith

/-- The radius and contraction give the exact projection cutoff needed for Gaussian tails. -/
private theorem paper_projection_scale {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    paperLambda d L * (paperRadius d L / (2 * (d : ℝ))) =
      1 / (4 * Real.sqrt (2 * L)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  have hs : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  have hsq : (Real.sqrt (2 * L)) ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  unfold paperLambda paperRadius
  field_simp [ne_of_gt hdR, ne_of_gt hLpos, ne_of_gt hs]
  nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]

/-- Coarse polynomial bounds suffice to absorb the explicit confidence error. -/
private theorem parameter_size_bounds {d n : ℕ} (hd : 0 < d) {D : ℝ} (hD : 0 ≤ D) :
    paperRadius d (parameterLog d D n) ≤ 6400000 * (parameterBase d D n) ^ 3 ∧
    1 / paperLambda d (parameterLog d D n) ≤ 12800000 * (parameterBase d D n) ^ 2 ∧
    paperLipschitz d D (parameterLog d D n) ≤ D ∧
    3 * (1 + paperLipschitz d D (parameterLog d D n)) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  let A := parameterBase d D n
  let L := parameterLog d D n
  have hb := parameterBase_bounds d n hD
  have hA : 0 < A := by dsimp [A]; nlinarith [hb.1]
  have hdA : (d : ℝ) ≤ A := by dsimp [A]; linarith [hb.2.1]
  have hLb := parameterLog_bounds d n hD
  have hL : 1 ≤ L := hLb.1
  have hLA : L ≤ 32 * A := hLb.2
  have hr := paperRadius_bounds hd hL
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdr : (d : ℝ) ≤ paperRadius d L := by nlinarith [hr.1]
  have hell : paperLipschitz d D L ≤ D := by
    unfold paperLipschitz
    apply (div_le_iff₀ hr.2.1).2
    nlinarith [mul_le_mul_of_nonneg_left hdr hD]
  refine ⟨?_, ?_, hell, ?_⟩
  · calc
      _ ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := hr.2.2
      _ ≤ 2 * 10 ^ 5 * A ^ 2 * (32 * A) := by gcongr
      _ = _ := by ring
  · unfold paperLambda
    rw [one_div_one_div]
    calc
      _ ≤ 4 * 10 ^ 5 * A * (32 * A) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 3 * (1 + D) * ((d : ℝ) + 1) := by gcongr
      _ ≤ A := by simpa only [add_comm] using hb.2.2.2.2


/-- The explicit confidence choice makes the scalar truncation bias smaller than the oracle tolerance. -/
private theorem parameter_scalar_bias_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) :
    3 * (3 * (1 + paperLipschitz d D (parameterLog d D n)) * ((d : ℝ) + 1)) *
        Real.exp (-parameterLog d D n / 2) / paperLambda d (parameterLog d D n) ≤
      1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) := by
  let A := parameterBase d D n
  let L := parameterLog d D n
  let r := paperRadius d L
  let lambda := paperLambda d L
  let Q := 3 * (1 + paperLipschitz d D L) * ((d : ℝ) + 1)
  change 3 * Q * Real.exp (-L / 2) / lambda ≤ 1 / (8 * r * (n : ℝ))
  have hb := parameterBase_bounds d n hD
  have hAmin : (10 ^ 6 : ℝ) ≤ A := hb.1
  have hA : 0 < A := by nlinarith
  have hnA : (n : ℝ) ≤ A := by dsimp [A]; linarith [hb.2.2.2.1]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hr : 0 < r := (paperRadius_bounds hd hL).2.1
  have hl : 0 < lambda := (paperLambda_bounds hd hL).1
  have hQ : 0 ≤ Q := by
    dsimp [Q, paperLipschitz]
    positivity
  have hs := parameter_size_bounds (n := n) hd hD
  have hrA : r ≤ 6400000 * A ^ 3 := hs.1
  have hlA : 1 / lambda ≤ 12800000 * A ^ 2 := hs.2.1
  have hQA : Q ≤ A := hs.2.2.2
  have hcoef : 24 * r * (n : ℝ) * Q * (1 / lambda) ≤ (10 ^ 16 : ℝ) * A ^ 7 := by
    calc
      _ ≤ 24 * (6400000 * A ^ 3) * A * A * (12800000 * A ^ 2) := by gcongr
      _ = 1966080000000000 * A ^ 7 := by ring
      _ ≤ _ := by nlinarith [pow_nonneg hA.le 7]
  have hp : (10 ^ 16 : ℝ) ≤ A ^ 9 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 10 ^ 6 by positivity) hAmin 9
    norm_num at h
    linarith
  apply (le_div_iff₀ (show 0 < 8 * r * (n : ℝ) by positivity)).2
  calc
    _ = (24 * r * (n : ℝ) * Q * (1 / lambda)) * A⁻¹ ^ 16 := by
      rw [show Real.exp (-L / 2) = A⁻¹ ^ 16 from exp_neg_half_parameterLog d n hD]
      ring
    _ ≤ ((10 ^ 16 : ℝ) * A ^ 7) * A⁻¹ ^ 16 :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (10 ^ 16 : ℝ) / A ^ 9 := by
      field_simp [ne_of_gt hA]
      <;> ring
    _ ≤ 1 := (div_le_one (pow_pos hA 9)).2 hp

/-- The same explicit choice also controls the directional-gradient truncation bias. -/
private theorem parameter_directional_bias_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) :
    3 * (3 * (1 + paperLipschitz d D (parameterLog d D n)) * ((d : ℝ) + 1)) *
        Real.exp (-parameterLog d D n / 2) ≤
      1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) := by
  have hL := (parameterLog_bounds d n hD).1
  have hr := (paperRadius_bounds hd hL).2.1
  have hl := paperLambda_bounds hd hL
  apply le_trans ?_ (parameter_scalar_bias_le hd hn hD)
  apply (le_div_iff₀ hl.1).2
  apply mul_le_of_le_one_right
  · unfold paperLipschitz
    positivity
  · linarith [hl.2.1]


end LG2021.Concentration

end

/- LG2021ConcentrationFinite -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The two-sided tail follows from the two one-sided bounds on the same probability space. -/
private theorem measure_abs_ge_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c P) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have heq : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [heq]
  exact (measureReal_union_le _ _).trans (by
    have hp := hX.measure_ge_le hε
    have hn := hX.neg.measure_ge_le hε
    change P.real {ω | ε ≤ -X ω} ≤ _ at hn
    linarith)

/-- A finite family of sub-Gaussian deviations can be controlled simultaneously. -/
private theorem measure_exists_abs_ge_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (c : ι → ℝ≥0)
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hX : ∀ i, HasSubgaussianMGF (X i) (c i) P) :
    P.real {ω | ∃ i, ε i ≤ |X i ω|} ≤
      ∑ i, 2 * Real.exp (-(ε i) ^ 2 / (2 * c i)) := by
  have heq : {ω | ∃ i, ε i ≤ |X i ω|} = ⋃ i, {ω | ε i ≤ |X i ω|} := by
    ext ω
    simp
  rw [heq]
  exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ =>
    measure_abs_ge_le_of_hasSubgaussianMGF P (hX i) (hε i))


end LG2021.Concentration

end

/- LG2021ConcentrationTruncation -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

/-- Exceeding the Gaussian likelihood cutoff forces a large one-dimensional projection. -/
private theorem likelihood_exceeds_cutoff_implies_projection {d : ℕ} {lambda : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (z x : Space d)
    (hbad : Real.exp 1 / (1 - lambda) ^ d < likelihoodRatio lambda z x) :
    (1 / 4 : ℝ) < lambda * inner ℝ x z := by
  have hl : 0 < 1 - lambda := by linarith
  have hden : 0 < (1 - lambda) ^ d := by positivity
  have hexp : 1 < ‖x‖ ^ 2 / 2 - ‖x - lambda • z‖ ^ 2 / (2 * (1 - lambda) ^ 2) := by
    apply Real.exp_lt_exp.mp
    exact (div_lt_div_iff_of_pos_right hden).1 hbad
  have hnorm : ‖x - lambda • z‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * lambda * inner ℝ x z + lambda ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hnorm] at hexp
  have hmult : 2 * (1 - lambda) ^ 2 <
      ‖x‖ ^ 2 * (1 - lambda) ^ 2 -
        (‖x‖ ^ 2 - 2 * lambda * inner ℝ x z + lambda ^ 2 * ‖z‖ ^ 2) := by
    have h := (lt_div_iff₀ (show 0 < 2 * (1 - lambda) ^ 2 by positivity)).1
      (show 1 < (‖x‖ ^ 2 * (1 - lambda) ^ 2 -
        (‖x‖ ^ 2 - 2 * lambda * inner ℝ x z + lambda ^ 2 * ‖z‖ ^ 2)) /
          (2 * (1 - lambda) ^ 2) by
        convert hexp using 1 <;> field_simp [ne_of_gt hl] <;> ring)
    nlinarith
  have htwo : 0 ≤ 2 - lambda := by linarith
  have hx : 0 ≤ lambda * (2 - lambda) * ‖x‖ ^ 2 := by positivity
  have hz : 0 ≤ lambda ^ 2 * ‖z‖ ^ 2 := by positivity
  have hl2 : (1 / 4 : ℝ) ≤ (1 - lambda) ^ 2 := by nlinarith
  nlinarith


/-- The same likelihood cutoff under the contracted Gaussian has a stronger projection threshold. -/
private theorem likelihood_shift_exceeds_cutoff_implies_projection {d : ℕ} {lambda : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (z x : Space d)
    (hz : lambda * ‖z‖ ≤ 1)
    (hbad : Real.exp 1 / (1 - lambda) ^ d <
      likelihoodRatio lambda z ((1 - lambda) • x + lambda • z)) :
    (1 / 2 : ℝ) < lambda * inner ℝ x z := by
  have hl : 0 < 1 - lambda := by linarith
  have hden : 0 < (1 - lambda) ^ d := by positivity
  have hexp : 1 < ‖(1 - lambda) • x + lambda • z‖ ^ 2 / 2 -
      ‖((1 - lambda) • x + lambda • z) - lambda • z‖ ^ 2 / (2 * (1 - lambda) ^ 2) := by
    apply Real.exp_lt_exp.mp
    exact (div_lt_div_iff_of_pos_right hden).1 hbad
  have hshift : ((1 - lambda) • x + lambda • z) - lambda • z = (1 - lambda) • x :=
    add_sub_cancel_right _ _
  have hnorm : ‖(1 - lambda) • x + lambda • z‖ ^ 2 =
      (1 - lambda) ^ 2 * ‖x‖ ^ 2 +
        2 * lambda * (1 - lambda) * inner ℝ x z + lambda ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos hl, abs_of_pos hpos, mul_pow]
    ring
  rw [hshift, hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hl, mul_pow] at hexp
  have heq : ((1 - lambda) ^ 2 * ‖x‖ ^ 2) / (2 * (1 - lambda) ^ 2) = ‖x‖ ^ 2 / 2 := by
    field_simp [ne_of_gt hl]
  rw [heq] at hexp
  have hz2 : lambda ^ 2 * ‖z‖ ^ 2 ≤ 1 := by
    have h := mul_le_mul hz hz (show 0 ≤ lambda * ‖z‖ by positivity) (by norm_num)
    nlinarith
  have htwo : 0 ≤ 2 - lambda := by linarith
  have hx : 0 ≤ lambda * (2 - lambda) * ‖x‖ ^ 2 := by positivity
  have hproj : 1 / 2 < (1 - lambda) * (lambda * inner ℝ x z) := by nlinarith
  by_contra h
  have hle : lambda * inner ℝ x z ≤ 1 / 2 := le_of_not_gt h
  have := mul_le_mul_of_nonneg_left hle hl.le
  nlinarith


/-- A Euclidean norm deviation forces a coordinate deviation. -/
private theorem exists_coordinate_abs_ge_of_norm_gt {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) (x : Space d) (hx : R < ‖x‖) :
    ∃ i : Fin d, R / Real.sqrt (d : ℝ) ≤ |x i| := by
  by_contra h
  push_neg at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hcoord (i : Fin d) : (x i) ^ 2 ≤ (R / Real.sqrt (d : ℝ)) ^ 2 := by
    nlinarith [h i, sq_abs (x i), abs_nonneg (x i)]
  have hsum : ‖x‖ ^ 2 ≤ (d : ℝ) * (R / Real.sqrt (d : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, (R / Real.sqrt (d : ℝ)) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp
  have heq : (d : ℝ) * (R / Real.sqrt (d : ℝ)) ^ 2 = R ^ 2 := by
    rw [div_pow, Real.sq_sqrt hdR.le]
    field_simp [ne_of_gt hdR]
  rw [heq] at hsum
  nlinarith [norm_nonneg x]

/-- Coordinate sub-Gaussian tails imply a Euclidean norm tail without independence. -/
private theorem measure_norm_gt_le_of_coordinate_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (X : Ω → Space d)
    (hX : ∀ i : Fin d, HasSubgaussianMGF (fun ω => X ω i) 1 P)
    {R : ℝ} (hR : 0 ≤ R) :
    P.real {ω | R < ‖X ω‖} ≤ 2 * (d : ℝ) * Real.exp (-R ^ 2 / (2 * (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsub : {ω | R < ‖X ω‖} ⊆
      {ω | ∃ i : Fin d, R / Real.sqrt (d : ℝ) ≤ |X ω i|} :=
    fun ω hω => exists_coordinate_abs_ge_of_norm_gt hd hR (X ω) hω
  have htail := measure_exists_abs_ge_le P (fun i ω => X ω i) (fun _ => 1)
    (fun _ => R / Real.sqrt (d : ℝ)) (fun _ => by positivity) hX
  simp only [NNReal.coe_one, mul_one] at htail
  have heq : -(R / Real.sqrt (d : ℝ)) ^ 2 / 2 =
      -R ^ 2 / (2 * (d : ℝ)) := by
    rw [div_pow, Real.sq_sqrt hdR.le]
    norm_num
    ring
  have hbound := (measureReal_mono hsub).trans htail
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbound
  calc
    _ ≤ (d : ℝ) * (2 * Real.exp (-R ^ 2 / (2 * (d : ℝ)))) := hbound
    _ = _ := by ring


end LG2021.Concentration

end

/- LG2021ConcentrationGaussianTails -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

/-- Every standard Gaussian coordinate has variance proxy one. -/
private theorem gaussian_coordinate_hasSubgaussianMGF {d : ℕ} (i : Fin d) :
    HasSubgaussianMGF (fun x : Space d => x i) 1 (gaussian d) := by
  have h := LG2021.gaussian_inner_hasSubgaussianMGF (EuclideanSpace.single i (1 : ℝ))
  have hf : (fun x : Space d => inner ℝ (EuclideanSpace.single i (1 : ℝ)) x) =
      (fun x : Space d => x i) := by funext x; simp [EuclideanSpace.inner_single_left]
  rw [hf] at h
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  have hb := h.mgf_le t
  change mgf (fun x : Space d => x i) (gaussian d) t ≤
    Real.exp (((‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2).toNNReal : ℝ) * t ^ 2 / 2) at hb
  simpa using hb

/-- The standard Gaussian norm has an explicit coordinate-union tail. -/
private theorem gaussian_norm_gt_le {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    (gaussian d).real {x | R < ‖x‖} ≤
      2 * (d : ℝ) * Real.exp (-R ^ 2 / (2 * (d : ℝ))) :=
  measure_norm_gt_le_of_coordinate_subgaussian (gaussian d) hd id
    gaussian_coordinate_hasSubgaussianMGF hR


/-- A deterministic upper bound on a Gaussian projection norm gives a uniform tail parameter. -/
private theorem gaussian_inner_ge_le {d : ℕ} (q : Space d) {B ε : ℝ}
    (hB : 0 < B) (hq : ‖q‖ ≤ B) (hε : 0 ≤ ε) :
    (gaussian d).real {x | ε ≤ inner ℝ q x} ≤ Real.exp (-ε ^ 2 / (2 * B ^ 2)) := by
  have h := LG2021.gaussian_inner_hasSubgaussianMGF q
  have h' : HasSubgaussianMGF (fun x => inner ℝ q x) (B ^ 2).toNNReal (gaussian d) := by
    refine ⟨h.integrable_exp_mul, ?_⟩
    intro t
    have hm := h.mgf_le t
    simp only [Real.coe_toNNReal _ (sq_nonneg _)] at hm ⊢
    apply hm.trans
    apply Real.exp_le_exp.mpr
    have hsq : ‖q‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg q]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg t)]
  have ht := h'.measure_ge_le hε
  simpa only [Real.coe_toNNReal _ (sq_nonneg _)] using ht

/-- The likelihood truncation has a one-dimensional Gaussian upper tail under the query law. -/
private theorem gaussian_likelihood_bad_le {d : ℕ} {lambda B : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hB : 0 < B)
    (z : Space d) (hz : lambda * ‖z‖ ≤ B) :
    (gaussian d).real {x | Real.exp 1 / (1 - lambda) ^ d < likelihoodRatio lambda z x} ≤
      Real.exp (-1 / (32 * B ^ 2)) := by
  have hnorm : ‖lambda • z‖ ≤ B := by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hpos] using hz
  have ht := gaussian_inner_ge_le (lambda • z) hB hnorm (ε := 1 / 4) (by norm_num)
  have hsub : {x | Real.exp 1 / (1 - lambda) ^ d < likelihoodRatio lambda z x} ⊆
      {x | (1 / 4 : ℝ) ≤ inner ℝ (lambda • z) x} := by
    intro x hx
    have h := (likelihood_exceeds_cutoff_implies_projection hpos hsmall z x hx).le
    simpa only [Set.mem_ofPred_eq, real_inner_smul_left, real_inner_comm z x] using h
  have h := (measureReal_mono hsub).trans ht
  convert h using 1
  congr 1
  ring

/-- The likelihood truncation under the contracted Gaussian also has a direct projection tail. -/
private theorem gaussian_shift_likelihood_bad_le {d : ℕ} {lambda B : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hB : 0 < B)
    (z : Space d) (hz : lambda * ‖z‖ ≤ B) (hz1 : lambda * ‖z‖ ≤ 1) :
    (gaussian d).real {x | Real.exp 1 / (1 - lambda) ^ d <
      likelihoodRatio lambda z ((1 - lambda) • x + lambda • z)} ≤
      Real.exp (-1 / (8 * B ^ 2)) := by
  have hnorm : ‖lambda • z‖ ≤ B := by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hpos] using hz
  have ht := gaussian_inner_ge_le (lambda • z) hB hnorm (ε := 1 / 2) (by norm_num)
  have hsub : {x | Real.exp 1 / (1 - lambda) ^ d <
      likelihoodRatio lambda z ((1 - lambda) • x + lambda • z)} ⊆
      {x | (1 / 2 : ℝ) ≤ inner ℝ (lambda • z) x} := by
    intro x hx
    have h := (likelihood_shift_exceeds_cutoff_implies_projection hpos hsmall z x hz1 hx).le
    simpa only [Set.mem_ofPred_eq, real_inner_smul_left, real_inner_comm z x] using h
  have h := (measureReal_mono hsub).trans ht
  convert h using 1
  congr 1
  ring


/-- The full query-law truncation probability combines the likelihood and norm tails. -/
private theorem gaussian_truncation_bad_le {d : ℕ} (hd : 0 < d) {lambda r B : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hr : 0 ≤ r) (hB : 0 < B)
    (z : Space d) (hz : lambda * ‖z‖ ≤ B) :
    (gaussian d).real {x | truncation lambda r z x ≠ 1} ≤
      Real.exp (-1 / (32 * B ^ 2)) +
        2 * (d : ℝ) * Real.exp (-(r / (d : ℝ)) ^ 2 / (2 * (d : ℝ))) := by
  have heq : {x | truncation lambda r z x ≠ 1} =
      {x | Real.exp 1 / (1 - lambda) ^ d < likelihoodRatio lambda z x} ∪
        {x | r / (d : ℝ) < ‖x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, ne_eq, truncation_eq_one_iff, not_and_or, not_le]
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add
    (gaussian_likelihood_bad_le hpos hsmall hB z hz)
    (gaussian_norm_gt_le hd (div_nonneg hr (Nat.cast_nonneg d))))

/-- The full truncation probability under the contracted Gaussian has the same explicit form. -/
private theorem gaussian_shift_truncation_bad_le {d : ℕ} (hd : 0 < d) {lambda r B : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hr : 0 ≤ r) (hB : 0 < B)
    (z : Space d) (hz : lambda * ‖z‖ ≤ B) (hz1 : lambda * ‖z‖ ≤ 1)
    (hguard : lambda * ‖z‖ ≤ r / (2 * (d : ℝ))) :
    (gaussian d).real {x | truncation lambda r z ((1 - lambda) • x + lambda • z) ≠ 1} ≤
      Real.exp (-1 / (8 * B ^ 2)) +
        2 * (d : ℝ) * Real.exp (-(r / (2 * (d : ℝ))) ^ 2 / (2 * (d : ℝ))) := by
  have hl : 0 < 1 - lambda := by linarith
  have heq : {x | truncation lambda r z ((1 - lambda) • x + lambda • z) ≠ 1} =
      {x | Real.exp 1 / (1 - lambda) ^ d < likelihoodRatio lambda z ((1 - lambda) • x + lambda • z)} ∪
        {x | r / (d : ℝ) < ‖(1 - lambda) • x + lambda • z‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, ne_eq, truncation_eq_one_iff, not_and_or, not_le]
  have hsub : {x : Space d | r / (d : ℝ) < ‖(1 - lambda) • x + lambda • z‖} ⊆
      {x | r / (2 * (d : ℝ)) < ‖x‖} := by
    intro x hx
    change r / (d : ℝ) < ‖(1 - lambda) • x + lambda • z‖ at hx
    change r / (2 * (d : ℝ)) < ‖x‖
    have hnorm : ‖(1 - lambda) • x + lambda • z‖ ≤ ‖x‖ + r / (2 * (d : ℝ)) := by
      have h := norm_add_le ((1 - lambda) • x) (lambda • z)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hl, abs_of_pos hpos] at h
      nlinarith [norm_nonneg x]
    have heqR : r / (d : ℝ) = 2 * (r / (2 * (d : ℝ))) := by ring
    rw [heqR] at hx
    linarith
  have hnormprob := (measureReal_mono hsub).trans
    (gaussian_norm_gt_le hd (div_nonneg hr (by positivity)))
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add
    (gaussian_shift_likelihood_bad_le hpos hsmall hB z hz hz1) hnormprob)


end LG2021.Concentration

end

/- LG2021ConcentrationParameterTails -/
section

set_option autoImplicit false

namespace LG2021.Concentration

/-- The norm-tail polynomial factor is absorbed by the Gaussian exponential. -/
private theorem gaussian_norm_factor_absorbed {d : ℕ} (hd : 0 < d) {C L : ℝ}
    (hC : 2 ≤ C) (hL : 1 ≤ L) :
    2 * (d : ℝ) * Real.exp (-(C * (d : ℝ) * L)) ≤ Real.exp (-L) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hCd : 2 * (d : ℝ) ≤ C * (d : ℝ) := by nlinarith
  have hnonneg : 0 ≤ C * (d : ℝ) - 1 := by linarith
  have hlin : 2 * (d : ℝ) ≤ 1 + (C * (d : ℝ) - 1) * L := by
    have h := mul_le_mul_of_nonneg_left hL hnonneg
    linarith
  have he : 2 * (d : ℝ) ≤ Real.exp ((C * (d : ℝ) - 1) * L) :=
    hlin.trans (by simpa only [add_comm] using Real.add_one_le_exp ((C * (d : ℝ) - 1) * L))
  calc
    _ ≤ Real.exp ((C * (d : ℝ) - 1) * L) * Real.exp (-(C * (d : ℝ) * L)) := by gcongr
    _ = Real.exp (-L) := by rw [← Real.exp_add]; congr 1; ring

/-- The explicit geometric scales make both truncation probabilities at most `2 exp(-L)`. -/
private theorem paper_truncation_probabilities {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L)
    (z : Space d) (hz : ‖z‖ ≤ paperRadius d L / (2 * (d : ℝ))) :
    (gaussian d).real {x | truncation (paperLambda d L) (paperRadius d L) z x ≠ 1} ≤
      2 * Real.exp (-L) ∧
    (gaussian d).real {x | truncation (paperLambda d L) (paperRadius d L) z
      ((1 - paperLambda d L) • x + paperLambda d L • z) ≠ 1} ≤ 2 * Real.exp (-L) := by
  let r := paperRadius d L
  let lambda := paperLambda d L
  let B := 1 / (4 * Real.sqrt (2 * L))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  have hs : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  have hsq : (Real.sqrt (2 * L)) ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  have hr : 0 < r := (paperRadius_bounds hd hL).2.1
  have hl := paperLambda_bounds hd hL
  have hB : 0 < B := by dsimp [B]; positivity
  have hzB : lambda * ‖z‖ ≤ B := by
    calc
      _ ≤ lambda * (r / (2 * (d : ℝ))) := mul_le_mul_of_nonneg_left hz hl.1.le
      _ = B := paper_projection_scale hd hL
  have hB1 : B ≤ 1 := by
    have hs1 : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
    dsimp [B]
    apply (div_le_one (by positivity : 0 < 4 * Real.sqrt (2 * L))).2
    linarith
  have hguard : lambda * ‖z‖ ≤ r / (2 * (d : ℝ)) := by
    calc
      _ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) (by linarith [hl.2.1])
      _ ≤ _ := hz
  have he1 : -1 / (32 * B ^ 2) = -L := by
    dsimp [B]
    field_simp [ne_of_gt hs]
    nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
  have he2 : -1 / (8 * B ^ 2) = -(4 * L) := by
    dsimp [B]
    field_simp [ne_of_gt hs]
    nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
  have hn1 : -(r / (d : ℝ)) ^ 2 / (2 * (d : ℝ)) = -(10000000000 * (d : ℝ) * L) := by
    dsimp [r, paperRadius]
    field_simp [ne_of_gt hdR]
    nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
  have hn2 : -(r / (2 * (d : ℝ))) ^ 2 / (2 * (d : ℝ)) = -(2500000000 * (d : ℝ) * L) := by
    dsimp [r, paperRadius]
    field_simp [ne_of_gt hdR]
    nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
  have h1 := gaussian_truncation_bad_le hd hl.1 hl.2.1 hr.le hB z hzB
  have h2 := gaussian_shift_truncation_bad_le hd hl.1 hl.2.1 hr.le hB z hzB (hzB.trans hB1) hguard
  rw [he1, hn1] at h1
  rw [he2, hn2] at h2
  have hn1b := gaussian_norm_factor_absorbed hd (C := 10000000000) (by norm_num) hL
  have hn2b := gaussian_norm_factor_absorbed hd (C := 2500000000) (by norm_num) hL
  have he : Real.exp (-(4 * L)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
  constructor <;> linarith


end LG2021.Concentration

end

/- LG2021GaussianGeometrySurrogate -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem integrable_lipschitz_gaussian_affine {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (a : ℝ) (z : Space d) :
    Integrable (fun x => f (a • x + z)) (gaussian d) := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have hmajor : Integrable (fun x : Space d => ‖f 0‖ +
      (K : ℝ) * (|a| * ‖x‖ + ‖z‖)) (gaussian d) :=
    (integrable_const _).add (((hx.norm.const_mul |a|).add (integrable_const _)).const_mul _)
  apply hmajor.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f (a • x + z)‖ ≤ ‖f 0‖ + ‖f 0 - f (a • x + z)‖ := norm_le_insert _ _
    _ ≤ ‖f 0‖ + (K : ℝ) * ‖a • x + z‖ := by
      gcongr
      simpa only [zero_sub, norm_neg] using hf.norm_sub_le 0 (a • x + z)
    _ ≤ ‖f 0‖ + (K : ℝ) * (|a| * ‖x‖ + ‖z‖) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • x) z

private theorem integrable_lipschitz_gaussian {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Integrable f (gaussian d) := by
  simpa using integrable_lipschitz_gaussian_affine hf 1 0









end LG2021

end
end

/- LG2021ConcentrationEnvelopes -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- A normalized Lipschitz loss has a linear envelope after a bounded affine shift. -/
private theorem lipschitz_affine_loss_abs_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b x : Space d) (hb : ‖b‖ ≤ 1) :
    |f (a • x + b)| ≤ (1 + (K : ℝ)) * (1 + ‖x‖) := by
  have hnorm : ‖a • x + b‖ ≤ ‖x‖ + 1 := by
    have h := norm_add_le (a • x) b
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at h
    nlinarith [norm_nonneg x]
  have hdiff : |f (a • x + b) - f 0| ≤ (K : ℝ) * ‖a • x + b‖ := by
    simpa only [Real.norm_eq_abs, sub_zero] using hf.norm_sub_le (a • x + b) 0
  calc
    _ = |(f (a • x + b) - f 0) + f 0| := by rw [sub_add_cancel]
    _ ≤ |f (a • x + b) - f 0| + |f 0| := abs_add_le _ _
    _ ≤ (K : ℝ) * ‖a • x + b‖ + 1 := add_le_add hdiff hf0
    _ ≤ (K : ℝ) * (‖x‖ + 1) + 1 := by gcongr
    _ ≤ _ := by nlinarith [norm_nonneg x, K.coe_nonneg]

/-- A square-integrable polynomial envelope for the shifted loss. -/
private theorem lipschitz_affine_loss_sq_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b x : Space d) (hb : ‖b‖ ≤ 1) :
    (f (a • x + b)) ^ 2 ≤ 2 * (1 + (K : ℝ)) ^ 2 * (1 + ‖x‖ ^ 2) := by
  have h := sq_le_sq₀ (abs_nonneg (f (a • x + b)))
    (show 0 ≤ (1 + (K : ℝ)) * (1 + ‖x‖) by positivity) |>.2
      (lipschitz_affine_loss_abs_le hf hf0 ha ha1 b x hb)
  rw [sq_abs, mul_pow] at h
  have hpoly : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (1 + (K : ℝ)))
  nlinarith

/-- Gaussian second moments bound the loss envelope used in the scalar truncation bias. -/
private theorem gaussian_affine_loss_second_moment {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : Space d) (hb : ‖b‖ ≤ 1) :
    Integrable (fun x => (f (a • x + b)) ^ 2) (gaussian d) ∧
      (∫ x, (f (a • x + b)) ^ 2 ∂gaussian d) ≤
        (3 * (1 + (K : ℝ)) * ((d : ℝ) + 1)) ^ 2 := by
  have hJ : Integrable (fun x : Space d => 2 * (1 + (K : ℝ)) ^ 2 * (1 + ‖x‖ ^ 2)) (gaussian d) :=
    ((integrable_const 1).add (gaussian_norm_sq_integrable d)).const_mul _
  have hI : Integrable (fun x => (f (a • x + b)) ^ 2) (gaussian d) := by
    have hFc : Continuous (fun x : Space d => f (a • x + b)) := hf.continuous.comp (by fun_prop)
    apply hJ.mono' (hFc.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f (a • x + b)))] using
        lipschitz_affine_loss_sq_le hf hf0 ha ha1 b x hb
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x : Space d, 2 * (1 + (K : ℝ)) ^ 2 * (1 + ‖x‖ ^ 2) ∂gaussian d :=
      integral_mono hI hJ (fun x => lipschitz_affine_loss_sq_le hf hf0 ha ha1 b x hb)
    _ = 2 * (1 + (K : ℝ)) ^ 2 * (1 + (d : ℝ)) := by
      rw [integral_const_mul, integral_add (integrable_const 1) (gaussian_norm_sq_integrable d),
        gaussian_norm_second_moment]
      simp
    _ ≤ _ := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hpoly : 2 * (1 + (d : ℝ)) ≤ 9 * ((d : ℝ) + 1) ^ 2 := by nlinarith
      have h := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (1 + (K : ℝ)))
      nlinarith


/-- The directional Gaussian score times a shifted loss has a quadratic moment envelope. -/
private theorem gaussian_affine_score_second_moment {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b η : Space d) (hb : ‖b‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    Integrable (fun x => inner ℝ x η * f (a • x + b)) (gaussian d) ∧
    Integrable (fun x => (inner ℝ x η * f (a • x + b)) ^ 2) (gaussian d) ∧
      (∫ x, (inner ℝ x η * f (a • x + b)) ^ 2 ∂gaussian d) ≤
        (3 * (1 + (K : ℝ)) * ((d : ℝ) + 1)) ^ 2 := by
  let S : Space d → ℝ := fun x => inner ℝ x η * f (a • x + b)
  have hSc : Continuous S := by
    exact (by fun_prop : Continuous (fun x : Space d => inner ℝ x η)).mul
      (hf.continuous.comp (by fun_prop))
  have hbound (x : Space d) : (S x) ^ 2 ≤
      2 * (1 + (K : ℝ)) ^ 2 * (‖x‖ ^ 2 + ‖x‖ ^ 4) := by
    have hi : |inner ℝ x η| ≤ ‖x‖ := by
      exact (abs_real_inner_le_norm x η).trans (by nlinarith [norm_nonneg x])
    have hi2 : (inner ℝ x η) ^ 2 ≤ ‖x‖ ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (inner ℝ x η)) (norm_nonneg x)).2 hi
      simpa only [sq_abs] using h
    have hf2 := lipschitz_affine_loss_sq_le hf hf0 ha ha1 b x hb
    calc
      _ = (inner ℝ x η) ^ 2 * (f (a • x + b)) ^ 2 := by dsimp [S]; ring
      _ ≤ ‖x‖ ^ 2 * (2 * (1 + (K : ℝ)) ^ 2 * (1 + ‖x‖ ^ 2)) :=
        mul_le_mul hi2 hf2 (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hJ : Integrable (fun x : Space d => 2 * (1 + (K : ℝ)) ^ 2 *
      (‖x‖ ^ 2 + ‖x‖ ^ 4)) (gaussian d) :=
    ((gaussian_norm_sq_integrable d).add (gaussian_norm_fourth_integrable d)).const_mul _
  have hS2I : Integrable (fun x => (S x) ^ 2) (gaussian d) := by
    apply hJ.mono' (hSc.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S x))] using hbound x
  have hSI : Integrable S (gaussian d) := by
    apply ((integrable_const 1).add hS2I).mono' hSc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      change ‖S x‖ ≤ 1 + (S x) ^ 2
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|S x| - 1 / 2), sq_abs (S x)]
  refine ⟨hSI, hS2I, ?_⟩
  calc
    _ ≤ ∫ x : Space d, 2 * (1 + (K : ℝ)) ^ 2 * (‖x‖ ^ 2 + ‖x‖ ^ 4) ∂gaussian d :=
      integral_mono hS2I hJ hbound
    _ = 2 * (1 + (K : ℝ)) ^ 2 * ((d : ℝ) + ∫ x : Space d, ‖x‖ ^ 4 ∂gaussian d) := by
      rw [integral_const_mul, integral_add (gaussian_norm_sq_integrable d)
        (gaussian_norm_fourth_integrable d), gaussian_norm_second_moment]
    _ ≤ 2 * (1 + (K : ℝ)) ^ 2 * ((d : ℝ) + 3 * (d : ℝ) ^ 2) := by
      gcongr
      exact gaussian_norm_fourth_moment_le d
    _ ≤ _ := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hpoly : 2 * ((d : ℝ) + 3 * (d : ℝ) ^ 2) ≤ 9 * ((d : ℝ) + 1) ^ 2 := by nlinarith
      have h := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (1 + (K : ℝ)))
      nlinarith


end LG2021.Concentration

end

/- LG2021ConcentrationBias -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A second-moment estimate controls truncation bias using any positive balancing parameter. -/
private theorem abs_setIntegral_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → ℝ)
    (hFI : Integrable F P) (hF2I : Integrable (fun ω => (F ω) ^ 2) P)
    (s : Set Ω) (hs : MeasurableSet s) {A : ℝ} (hA : 0 < A) :
    |∫ ω in s, F ω ∂P| ≤
      (∫ ω, (F ω) ^ 2 ∂P) / (2 * A) + (A / 2) * P.real s := by
  have hIabs : Integrable (s.indicator (fun ω => |F ω|)) P := hFI.abs.indicator hs
  have hIs : Integrable (s.indicator (fun _ : Ω => (1 : ℝ))) P := (integrable_const 1).indicator hs
  have hJ : Integrable (fun ω => (F ω) ^ 2 / (2 * A) +
      (A / 2) * s.indicator (fun _ : Ω => (1 : ℝ)) ω) P :=
    (hF2I.div_const (2 * A)).add (hIs.const_mul (A / 2))
  have hp (ω : Ω) : s.indicator (fun ω => |F ω|) ω ≤
      (F ω) ^ 2 / (2 * A) + (A / 2) * s.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω, mul_one]
      have h : |F ω| - A / 2 ≤ (F ω) ^ 2 / (2 * A) := by
        apply (le_div_iff₀ (show 0 < 2 * A by positivity)).2
        nlinarith [sq_nonneg (|F ω| - A), sq_abs (F ω)]
      linarith
    · simp only [Set.indicator_of_notMem hω, mul_zero, add_zero]
      positivity
  calc
    _ ≤ ∫ ω in s, |F ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P.restrict s) F
    _ = ∫ ω, s.indicator (fun ω => |F ω|) ω ∂P := (integral_indicator hs).symm
    _ ≤ ∫ ω, (F ω) ^ 2 / (2 * A) + (A / 2) * s.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P :=
      integral_mono hIabs hJ hp
    _ = _ := by
      rw [integral_add (hF2I.div_const (2 * A)) (hIs.const_mul (A / 2)),
        integral_div, integral_const_mul, integral_indicator hs]
      simp


/-- Removing a measurable zero-one gate changes an expectation by the integral on its failure set. -/
private theorem integral_gate_sub_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F I : Ω → ℝ)
    (hFI : Integrable F P) (hI : Measurable I) (h01 : ∀ ω, I ω = 0 ∨ I ω = 1) :
    (∫ ω, F ω * I ω ∂P) - (∫ ω, F ω ∂P) = -∫ ω in {ω | I ω ≠ 1}, F ω ∂P := by
  have hbound : ∀ᵐ ω ∂P, ‖I ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
    rcases h01 ω with h | h <;> simp [h]
  have hmul := hFI.mul_bdd hI.aestronglyMeasurable hbound
  have hs : MeasurableSet {ω | I ω ≠ 1} := (measurableSet_eq_fun hI measurable_const).compl
  have heq : (fun ω => F ω * I ω - F ω) =
      (fun ω => -({ω | I ω ≠ 1}.indicator F ω)) := by
    funext ω
    rcases h01 ω with h | h <;> simp [h]
  rw [← integral_sub hmul hFI, heq, integral_neg, integral_indicator hs]

/-- A polynomial square-moment envelope and an exponentially small failure probability give a tiny bias. -/
private theorem integral_gate_bias_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F I : Ω → ℝ)
    (hFI : Integrable F P) (hF2I : Integrable (fun ω => (F ω) ^ 2) P)
    (hI : Measurable I) (h01 : ∀ ω, I ω = 0 ∨ I ω = 1)
    {Q L : ℝ} (hQ : 0 < Q) (hM : (∫ ω, (F ω) ^ 2 ∂P) ≤ Q ^ 2)
    (hprob : P.real {ω | I ω ≠ 1} ≤ 2 * Real.exp (-L)) :
    |(∫ ω, F ω * I ω ∂P) - (∫ ω, F ω ∂P)| ≤
      (3 / 2) * Q * Real.exp (-L / 2) := by
  rw [integral_gate_sub_integral P F I hFI hI h01, abs_neg]
  have hs : MeasurableSet {ω | I ω ≠ 1} := (measurableSet_eq_fun hI measurable_const).compl
  have hA : 0 < Q * Real.exp (L / 2) := by positivity
  have h := abs_setIntegral_le_second_moment P F hFI hF2I _ hs hA
  calc
    _ ≤ (∫ ω, (F ω) ^ 2 ∂P) / (2 * (Q * Real.exp (L / 2))) +
        (Q * Real.exp (L / 2) / 2) * P.real {ω | I ω ≠ 1} := h
    _ ≤ Q ^ 2 / (2 * (Q * Real.exp (L / 2))) +
        (Q * Real.exp (L / 2) / 2) * (2 * Real.exp (-L)) := by
      gcongr
    _ = (3 / 2) * Q * Real.exp (-L / 2) := by
      have heq : Real.exp (-L / 2) = (Real.exp (L / 2))⁻¹ := by
        rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
      have heq2 : Real.exp (-L) = (Real.exp (L / 2))⁻¹ ^ 2 := by
        rw [show -L = -(L / 2) + -(L / 2) by ring, Real.exp_add, Real.exp_neg]
        ring
      rw [heq, heq2]
      field_simp [ne_of_gt hQ, Real.exp_ne_zero]
      <;> ring


end LG2021.Concentration

end

/- LG2021GaussianGeometryTranslation -/
section


noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

private def stdDensity {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

private lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

private lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

private lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

private lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

private lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm



private lemma stdDensity_eq {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    stdDensity x = (Real.sqrt (2*Real.pi))⁻¹ ^ (Fintype.card ι) *
      Real.exp (-‖x‖^2/2) := by
  simp only [stdDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp [EuclideanSpace.norm_sq_eq]

end LG2021.GaussianTranslation

namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussian_eq_withDensity (d : ℕ) :
    gaussian d = volume.withDensity (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 x)) := by
  rw [gaussian, GaussianTranslation.stdGaussian_density]
  congr 1
  funext x
  rw [GaussianTranslation.stdDensity_eq]
  simp [gaussianDensity]

end LG2021

end
end

/- LG2021GaussianGeometryDensity -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem gaussianDensity_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Space d) :
    0 ≤ gaussianDensity s x := by
  unfold gaussianDensity
  positivity







end LG2021

end
end

/- LG2021GaussianGeometryAffine -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private def affineGaussianRatio {d : ℕ} (a : ℝ) (b x : Space d) : ℝ :=
  Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2)) / a ^ d

private theorem affineGaussianRatio_pos {d : ℕ} {a : ℝ} (ha : 0 < a) (b x : Space d) :
    0 < affineGaussianRatio a b x := by
  unfold affineGaussianRatio
  positivity

private theorem volume_map_affine {d : ℕ} {a : ℝ} (ha : 0 < a) (b : Space d) :
    (volume : Measure (Space d)).map (fun x => a • x + b) =
      ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
  have heq : (fun x : Space d => a • x + b) = (fun y => y + b) ∘ (fun x => a • x) := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume ha.ne', Measure.map_smul,
    (measurePreserving_add_right volume b).map_eq]
  simp [Space, abs_of_pos (inv_pos.mpr (pow_pos ha _))]

private theorem gaussianDensity_mul_affineRatio {d : ℕ} {a : ℝ} (ha : 0 < a) (b x : Space d) :
    gaussianDensity 1 x * affineGaussianRatio a b x =
      (a ^ d)⁻¹ * gaussianDensity 1 (a⁻¹ • (x - b)) := by
  unfold gaussianDensity affineGaussianRatio
  simp only [mul_one, one_pow, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha)]
  have heq : -(a⁻¹ * ‖x - b‖) ^ 2 / 2 = -‖x - b‖ ^ 2 / (2 * a ^ 2) := by
    field_simp
  rw [heq]
  have he : Real.exp (-‖x‖ ^ 2 / 2) *
      Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2)) =
      Real.exp (-‖x - b‖ ^ 2 / (2 * a ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ d *
        (Real.exp (-‖x‖ ^ 2 / 2) *
          Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2))) / a ^ d := by ring
    _ = _ := by rw [he]; ring

/-- Exact affine Gaussian change of measure, including its Jacobian. -/
private theorem gaussian_map_affine {d : ℕ} {a : ℝ} (ha : 0 < a) (b : Space d) :
    (gaussian d).map (fun x => a • x + b) =
      (gaussian d).withDensity (fun x => ENNReal.ofReal (affineGaussianRatio a b x)) := by
  have hρ : Measurable (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 x)) := by
    unfold gaussianDensity
    fun_prop
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  have hm := GaussianTranslation.map_density_comp (volume : Measure (Space d))
    (fun x => a • x + b) (by fun_prop)
    (fun x => ENNReal.ofReal (gaussianDensity 1 (a⁻¹ • (x - b)))) (by
      unfold gaussianDensity
      fun_prop)
  have hc : (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 (a⁻¹ • (x - b)))) ∘
      (fun x => a • x + b) = fun x => ENNReal.ofReal (gaussianDensity 1 x) := by
    funext x
    simp only [Function.comp_def, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [hc] at hm
  simp only [gaussian_eq_withDensity]
  rw [hm, volume_map_affine ha, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal ((a ^ d)⁻¹)) (by unfold gaussianDensity; fun_prop),
    ← withDensity_mul volume hρ hrat]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ha.le d)),
    ← ENNReal.ofReal_mul (gaussianDensity_nonneg (by norm_num : (0 : ℝ) < 1) x)]
  congr 1
  exact (gaussianDensity_mul_affineRatio ha b x).symm

end LG2021

end
end

/- LG2021GaussianGeometryChangeOfMeasure -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_affineGaussianRatio_iff {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    Integrable (fun x => affineGaussianRatio a b x * F x) (gaussian d) ↔
      Integrable (fun u => F (a • u + b)) (gaussian d) := by
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  have hw := integrable_withDensity_iff_integrable_smul' (μ := gaussian d) hrat
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := F)
  simp only [ENNReal.toReal_ofReal (affineGaussianRatio_pos ha b _).le, smul_eq_mul] at hw
  have hm := integrable_map_measure (μ := gaussian d)
    (f := fun x : Space d => a • x + b) hF.aestronglyMeasurable (by fun_prop)
  rw [gaussian_map_affine ha b] at hm
  exact hw.symm.trans hm

private theorem integral_affineGaussianRatio {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    (∫ x, affineGaussianRatio a b x * F x ∂gaussian d) =
      ∫ u, F (a • u + b) ∂gaussian d := by
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  calc
    _ = ∫ x, F x ∂(gaussian d).withDensity (fun x => ENNReal.ofReal (affineGaussianRatio a b x)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hrat
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (affineGaussianRatio_pos ha b _).le, smul_eq_mul]
    _ = ∫ x, F x ∂(gaussian d).map (fun x => a • x + b) := by rw [gaussian_map_affine ha b]
    _ = _ := integral_map (by fun_prop) hF.aestronglyMeasurable

private theorem integrable_likelihoodRatio_iff {d : ℕ} {lambda : ℝ} (hl : lambda < 1)
    (z : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    Integrable (fun x => Concentration.likelihoodRatio lambda z x * F x) (gaussian d) ↔
      Integrable (fun u => F ((1 - lambda) • u + lambda • z)) (gaussian d) := by
  exact integrable_affineGaussianRatio_iff (sub_pos.mpr hl) (lambda • z) hF

private theorem integral_likelihoodRatio {d : ℕ} {lambda : ℝ} (hl : lambda < 1)
    (z : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    (∫ x, Concentration.likelihoodRatio lambda z x * F x ∂gaussian d) =
      ∫ u, F ((1 - lambda) • u + lambda • z) ∂gaussian d := by
  exact integral_affineGaussianRatio (sub_pos.mpr hl) (lambda • z) hF

end LG2021

end
end

/- LG2021GaussianGeometryMollification -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

/-- Gaussian regularization of an actual function on Euclidean space. -/
private def gaussianMollify {d : ℕ} (epsilon : ℝ) (f : Space d → ℝ) (z : Space d) : ℝ :=
  ∫ x, f (z + epsilon • x) ∂gaussian d









end LG2021

end
end

/- LG2021GaussianGeometrySmoothingReuse -/
section
noncomputable section
namespace LG2021.ReusedSmoothing.RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma lipschitz_cont (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) (fun x y => ?_)).continuous
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Real.coe_toNNReal _ hL] using hlip x y

private lemma nonsmooth_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have hc := lipschitz_cont f L hL hlip
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((h1.const_mul |f x|).add (h2.const_mul (L*μ)))
    ((hc.comp (by fun_prop)).smul continuous_id).aestronglyMeasurable ?_
  filter_upwards [] with u
  have hh := hlip (x+μ • u) x
  rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hμ] at hh
  have hfn : |f (x+μ • u)| ≤ |f x|+L*μ*‖u‖ := by
    have htri := abs_add_le (f (x+μ • u)-f x) (f x)
    rw [sub_add_cancel] at htri
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hfn (norm_nonneg u)
  rw [norm_smul,Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith


end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussianMollify_hasGradient {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (∫ u, ((f (z + epsilon • u) - f z) / epsilon) • u ∂gaussian d) z := by
  have hLip (x y : Space d) : |f x - f y| ≤ (K : ℝ) * ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y
  have heq : gaussianMollify epsilon f =
      RandomGradFree.Shared.smoothing f epsilon := rfl
  rw [heq]
  simpa only [gaussian, RandomGradFree.Nonsmooth.oracle] using
    RandomGradFree.Nonsmooth.smoothing_hasGradient f (K : ℝ) K.coe_nonneg hLip epsilon he z

end LG2021

end
end

/- LG2021GaussianGeometryIntegrability -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory









end LG2021

end
end

/- LG2021GaussianGeometryGradient -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_gaussian_affine_value_smul {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 ≤ epsilon) (z : Space d) :
    Integrable (fun u => f (z + epsilon • u) • u) (gaussian d) := by
  apply ReusedSmoothing.RGF6.nonsmooth_integrable f (K : ℝ) K.coe_nonneg
    (fun x y => ?_) epsilon he z
  simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y

private theorem gaussianMollify_hasGradient_uncentered {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (epsilon⁻¹ • ∫ u, f (z + epsilon • u) • u ∂gaussian d) z := by
  have hi := integrable_gaussian_affine_value_smul hf he.le z
  have hx : Integrable (fun u : Space d => u) (gaussian d) := IsGaussian.integrable_fun_id
  have heq : (fun u : Space d => ((f (z + epsilon • u) - f z) / epsilon) • u) =
      fun u => epsilon⁻¹ • (f (z + epsilon • u) • u - f z • u) := by
    funext u
    simp only [div_eq_mul_inv, smul_sub, smul_smul, ← sub_smul]
    congr 1
    ring
  have h := gaussianMollify_hasGradient hf he z
  have hic : Integrable (fun u : Space d => f z • u) (gaussian d) := hx.smul (f z)
  rw [heq, integral_smul, integral_sub hi hic, integral_smul] at h
  simpa only [gaussian, integral_id_stdGaussian, smul_zero, sub_zero] using h

private theorem surrogate_hasFDerivAt {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (hl1 : lambda < 1)
    (z : Space d) :
    HasFDerivAt (surrogate lambda f)
      (InnerProductSpace.toDual ℝ (Space d)
        ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)) z := by
  let A := InnerProductSpace.toDual ℝ (Space d)
    ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)
  have h := (gaussianMollify_hasGradient_uncentered hf (sub_pos.mpr hl1)
    (lambda • z)).hasFDerivAt
  have hc := h.comp z ((hasFDerivAt_id z).const_smul lambda)
  have hh := (((hc.sub_const (gaussianMean f)).const_mul lambda⁻¹).const_add (gaussianMean f))
  have heq : (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f)) =
      surrogate lambda f := by
    ext y
    simp only [surrogate, gaussianMollify, add_comm]
    ring
  change HasFDerivAt (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f))
      (lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d))) z at hh
  rw [heq] at hh
  have heqD : lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d)) = A := by
    ext v
    simp [ContinuousLinearMap.comp_apply, hl]
  rw [heqD] at hh
  exact hh

private theorem surrogate_directional_gradient {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (hl1 : lambda < 1)
    (z eta : Space d) :
    fderiv ℝ (surrogate lambda f) z eta = ((1-lambda)⁻¹)^2 *
      ∫ x, inner ℝ (x-lambda • z) eta * f x *
        Concentration.likelihoodRatio lambda z x ∂gaussian d := by
  have hchange := integral_likelihoodRatio hl1 z
    (F := fun x => inner ℝ (x-lambda • z) eta * f x)
    (by exact (Continuous.mul (by fun_prop) hf.continuous).measurable)
  have hi := integrable_gaussian_affine_value_smul hf (sub_pos.mpr hl1).le (lambda • z)
  rw [(surrogate_hasFDerivAt hf hl hl1 z).fderiv]
  simp only [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, real_inner_smul_left]
  have hinner : inner ℝ (∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d) eta =
      ∫ u, f (lambda • z + (1-lambda) • u) * inner ℝ u eta ∂gaussian d := by
    rw [real_inner_comm, ← integral_inner hi]
    simp only [inner_smul_right, real_inner_comm]
  rw [hinner]
  have heq : (∫ x, inner ℝ (x-lambda • z) eta * f x *
      Concentration.likelihoodRatio lambda z x ∂gaussian d) =
      (1-lambda) * ∫ u, f (lambda • z + (1-lambda) • u) * inner ℝ u eta ∂gaussian d := by
    calc
      _ = ∫ x, Concentration.likelihoodRatio lambda z x *
          (inner ℝ (x-lambda • z) eta * f x) ∂gaussian d := by
        congr 1; funext x; ring
      _ = _ := by
        rw [hchange, ← integral_const_mul]
        congr 1
        funext u
        simp only [add_sub_cancel_right, real_inner_smul_left]
        rw [add_comm ((1-lambda) • u)]
        ring
  rw [heq]
  field_simp
  <;> ring

end LG2021

end
end

/- LG2021ConcentrationSurrogateBias -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Truncation bias for the actual scalar likelihood-ratio estimator.
This is the change-of-measure calculation in Lemma 4(a) of Tor Lattimore and András György,
Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th
Conference on Learning Theory, PMLR 134, 2021, with an explicit second-moment envelope. -/
private theorem scalar_surrogate_bias_le {d : ℕ} {lambda r Q L : ℝ}
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hQ : 0 < Q)
    (f : Space d → ℝ) (hf : Measurable f) (z : Space d)
    (hFI : Integrable f (gaussian d))
    (hF2I : Integrable (fun x => (f x) ^ 2) (gaussian d))
    (hFUI : Integrable (fun x => f ((1 - lambda) • x + lambda • z)) (gaussian d))
    (hFU2I : Integrable (fun x => (f ((1 - lambda) • x + lambda • z)) ^ 2) (gaussian d))
    (hM : (∫ x, (f x) ^ 2 ∂gaussian d) ≤ Q ^ 2)
    (hMU : (∫ x, (f ((1 - lambda) • x + lambda • z)) ^ 2 ∂gaussian d) ≤ Q ^ 2)
    (hprob : (gaussian d).real {x | truncation lambda r z x ≠ 1} ≤ 2 * Real.exp (-L))
    (hprobU : (gaussian d).real {x |
      truncation lambda r z ((1 - lambda) • x + lambda • z) ≠ 1} ≤ 2 * Real.exp (-L)) :
    |(∫ x, f x * scalarCoefficient lambda r z x ∂gaussian d) - surrogate lambda f z| ≤
      3 * Q * Real.exp (-L / 2) / lambda := by
  let I := truncation lambda r z
  let U : Space d → Space d := fun x => (1 - lambda) • x + lambda • z
  have hI : Measurable I := (Algorithm.measurable_truncation (d := d) lambda r).comp
    (f := fun x : Space d => (z, x)) (measurable_const.prodMk measurable_id)
  have hU : Measurable U := by dsimp [U]; fun_prop
  have hIU : Measurable (fun x => I (U x)) := hI.comp hU
  have h01 : ∀ x, I x = 0 ∨ I x = 1 := truncation_zero_or_one lambda r z
  have h01U : ∀ x, I (U x) = 0 ∨ I (U x) = 1 := fun x => h01 (U x)
  have hbound : ∀ᵐ x ∂gaussian d, ‖I x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    rcases h01 x with h | h <;> simp [h]
  have hboundU : ∀ᵐ x ∂gaussian d, ‖I (U x)‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    rcases h01U x with h | h <;> simp [h]
  have hclipI : Integrable (fun x => f x * I x) (gaussian d) :=
    hFI.mul_bdd hI.aestronglyMeasurable hbound
  have hclipUI : Integrable (fun x => f (U x) * I (U x)) (gaussian d) :=
    hFUI.mul_bdd hIU.aestronglyMeasurable hboundU
  have hratioI : Integrable (fun x => likelihoodRatio lambda z x * (f x * I x)) (gaussian d) :=
    (integrable_likelihoodRatio_iff (by linarith : lambda < 1) z (hf.mul hI)).2 hclipUI
  have hmean : (∫ x, f x * scalarCoefficient lambda r z x ∂gaussian d) =
      (1 - 1 / lambda) * (∫ x, f x * I x ∂gaussian d) +
        (1 / lambda) * (∫ x, f (U x) * I (U x) ∂gaussian d) := by
    have heq : (fun x => f x * scalarCoefficient lambda r z x) =
        (fun x => (1 - 1 / lambda) * (f x * I x) +
          (1 / lambda) * (likelihoodRatio lambda z x * (f x * I x))) := by
      funext x
      dsimp [scalarCoefficient, I]
      ring
    rw [heq, integral_add (hclipI.const_mul _) (hratioI.const_mul _), integral_const_mul,
      integral_const_mul, integral_likelihoodRatio (by linarith : lambda < 1) z
        (F := fun x => f x * I x) (hf.mul hI)]
  have h0 := integral_gate_bias_le (gaussian d) f I hFI hF2I hI h01 hQ hM hprob
  have h1 := integral_gate_bias_le (gaussian d) (fun x => f (U x)) (fun x => I (U x))
    hFUI hFU2I hIU h01U hQ hMU hprobU
  rw [hmean]
  have heq : (1 - 1 / lambda) * (∫ x, f x * I x ∂gaussian d) +
      (1 / lambda) * (∫ x, f (U x) * I (U x) ∂gaussian d) - surrogate lambda f z =
      (1 - 1 / lambda) * ((∫ x, f x * I x ∂gaussian d) - ∫ x, f x ∂gaussian d) +
        (1 / lambda) * ((∫ x, f (U x) * I (U x) ∂gaussian d) - ∫ x, f (U x) ∂gaussian d) := by
    dsimp [surrogate, gaussianMean, U]
    ring
  rw [heq]
  have hcoeff : |1 - 1 / lambda| ≤ 1 / lambda := by
    have hinv : 1 ≤ 1 / lambda := (le_div_iff₀ hpos).2 (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith
  calc
    _ ≤ |(1 - 1 / lambda) * ((∫ x, f x * I x ∂gaussian d) - ∫ x, f x ∂gaussian d)| +
        |(1 / lambda) * ((∫ x, f (U x) * I (U x) ∂gaussian d) - ∫ x, f (U x) ∂gaussian d)| := abs_add_le _ _
    _ = |1 - 1 / lambda| * |(∫ x, f x * I x ∂gaussian d) - ∫ x, f x ∂gaussian d| +
        (1 / lambda) * |(∫ x, f (U x) * I (U x) ∂gaussian d) - ∫ x, f (U x) ∂gaussian d| := by
      rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hpos)]
    _ ≤ (1 / lambda) * ((3 / 2) * Q * Real.exp (-L / 2)) +
        (1 / lambda) * ((3 / 2) * Q * Real.exp (-L / 2)) := by
      gcongr
    _ = _ := by ring


/-- Truncation bias for the actual directional-gradient estimator.
The factor `1/(1-lambda)` produced by Gaussian change of measure is retained explicitly. -/
private theorem directional_surrogate_bias_le {d : ℕ} {lambda r Q L : ℝ} {K : NNReal}
    {f : Space d → ℝ} (hf : LipschitzWith K f)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hQ : 0 < Q) (z η : Space d)
    (hSI : Integrable (fun x => inner ℝ x η * f ((1 - lambda) • x + lambda • z)) (gaussian d))
    (hS2I : Integrable (fun x => (inner ℝ x η * f ((1 - lambda) • x + lambda • z)) ^ 2) (gaussian d))
    (hM : (∫ x, (inner ℝ x η * f ((1 - lambda) • x + lambda • z)) ^ 2 ∂gaussian d) ≤ Q ^ 2)
    (hprobU : (gaussian d).real {x |
      truncation lambda r z ((1 - lambda) • x + lambda • z) ≠ 1} ≤ 2 * Real.exp (-L)) :
    |(∫ x, f x * directionalGradientCoefficient lambda r z η x ∂gaussian d) -
      fderiv ℝ (surrogate lambda f) z η| ≤ 3 * Q * Real.exp (-L / 2) := by
  have hl : 0 < 1 - lambda := by linarith
  let I := truncation lambda r z
  let U : Space d → Space d := fun x => (1 - lambda) • x + lambda • z
  let S : Space d → ℝ := fun x => inner ℝ x η * f (U x)
  have hI : Measurable I := (Algorithm.measurable_truncation (d := d) lambda r).comp
    (f := fun x : Space d => (z, x)) (measurable_const.prodMk measurable_id)
  have hU : Measurable U := by dsimp [U]; fun_prop
  have hIU : Measurable (fun x => I (U x)) := hI.comp hU
  have hCM (F : Space d → ℝ) (hF : Measurable F) :
      (∫ x, inner ℝ (x - lambda • z) η * F x * likelihoodRatio lambda z x ∂gaussian d) =
        (1 - lambda) * ∫ x, inner ℝ x η * F (U x) ∂gaussian d := by
    calc
      _ = ∫ x, likelihoodRatio lambda z x * (inner ℝ (x - lambda • z) η * F x) ∂gaussian d := by
        congr 1
        funext x
        ring
      _ = ∫ x, inner ℝ (U x - lambda • z) η * F (U x) ∂gaussian d :=
        integral_likelihoodRatio (by linarith) z (by fun_prop)
      _ = _ := by
        dsimp [U]
        simp only [add_sub_cancel_right, real_inner_smul_left]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring
  have hclip : (∫ x, f x * directionalGradientCoefficient lambda r z η x ∂gaussian d) =
      ((1 - lambda)⁻¹) ^ 2 * (1 - lambda) * ∫ x, S x * I (U x) ∂gaussian d := by
    calc
      _ = ((1 - lambda)⁻¹) ^ 2 * ∫ x,
          inner ℝ (x - lambda • z) η * (f x * I x) * likelihoodRatio lambda z x ∂gaussian d := by
        rw [← integral_const_mul]
        congr 1
        funext x
        dsimp [directionalGradientCoefficient, gradientCoefficient, I]
        rw [real_inner_smul_left]
        simp only [div_eq_mul_inv, inv_pow]
        ring
      _ = _ := by
        rw [hCM (fun x => f x * I x) (hf.continuous.measurable.mul hI)]
        dsimp [S]
        rw [mul_assoc]
        congr 2
        apply integral_congr_ae
        filter_upwards with x
        ring
  have hderiv : fderiv ℝ (surrogate lambda f) z η =
      ((1 - lambda)⁻¹) ^ 2 * (1 - lambda) * ∫ x, S x ∂gaussian d := by
    rw [surrogate_directional_gradient hf (ne_of_gt hpos) (by linarith),
      hCM f hf.continuous.measurable]
    exact (mul_assoc _ _ _).symm
  have hcoef : ((1 - lambda)⁻¹) ^ 2 * (1 - lambda) = (1 - lambda)⁻¹ := by
    field_simp [ne_of_gt hl]
  have h01 : ∀ x, I (U x) = 0 ∨ I (U x) = 1 := fun x => truncation_zero_or_one lambda r z (U x)
  have hb := integral_gate_bias_le (gaussian d) S (fun x => I (U x))
    hSI hS2I hIU h01 hQ hM hprobU
  rw [hclip, hderiv, hcoef, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hl)]
  have hinv : (1 - lambda)⁻¹ ≤ 2 := (inv_le_comm₀ hl (by norm_num)).2 (by linarith)
  calc
    _ ≤ 2 * ((3 / 2) * Q * Real.exp (-L / 2)) := by gcongr
    _ = _ := by ring


end LG2021.Concentration

end

/- LG2021ConcentrationLemma4 -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Every admissible candidate gives a shift of norm at most one. -/
private theorem paper_candidate_shift_le_one {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L)
    (z : Space d) (hz : ‖z‖ ≤ paperRadius d L / (2 * (d : ℝ))) :
    ‖paperLambda d L • z‖ ≤ 1 := by
  have hl := paperLambda_bounds hd hL
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl.1]
  have hs : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
  calc
    _ ≤ paperLambda d L * (paperRadius d L / (2 * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hz hl.1.le
    _ = 1 / (4 * Real.sqrt (2 * L)) := paper_projection_scale hd hL
    _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)

/-- The Gaussian estimator biases, with every moment and truncation bound discharged.
This formalizes the bias estimate associated with Lemma 4 in Tor Lattimore and András György,
Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th
Conference on Learning Theory, PMLR 134, 2021. -/
private theorem paper_surrogate_bias_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L)
    {f : Space d → ℝ} {K : NNReal} (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1)
    (z η : Space d) (hz : ‖z‖ ≤ paperRadius d L / (2 * (d : ℝ))) (hη : ‖η‖ ≤ 1) :
    |(∫ x, f x * scalarCoefficient (paperLambda d L) (paperRadius d L) z x ∂gaussian d) -
      surrogate (paperLambda d L) f z| ≤
      3 * (3 * (1 + (K : ℝ)) * ((d : ℝ) + 1)) * Real.exp (-L / 2) / paperLambda d L ∧
    |(∫ x, f x * directionalGradientCoefficient (paperLambda d L) (paperRadius d L) z η x
      ∂gaussian d) - fderiv ℝ (surrogate (paperLambda d L) f) z η| ≤
      3 * (3 * (1 + (K : ℝ)) * ((d : ℝ) + 1)) * Real.exp (-L / 2) := by
  have hl := paperLambda_bounds hd hL
  have hb := paper_candidate_shift_le_one hd hL z hz
  have ha : 0 ≤ 1 - paperLambda d L := by linarith [hl.2.1]
  have ha1 : 1 - paperLambda d L ≤ 1 := by linarith [hl.1]
  have hF := gaussian_affine_loss_second_moment hf hf0
    (a := 1) (by norm_num) (by norm_num) 0 (by simp)
  simp only [one_smul, add_zero] at hF
  have hFU := gaussian_affine_loss_second_moment hf hf0 ha ha1 (paperLambda d L • z) hb
  have hS := gaussian_affine_score_second_moment hf hf0 ha ha1 (paperLambda d L • z) η hb hη
  have hp := paper_truncation_probabilities hd hL z hz
  have hQ : 0 < 3 * (1 + (K : ℝ)) * ((d : ℝ) + 1) := by positivity
  constructor
  · exact scalar_surrogate_bias_le hl.1 hl.2.1 hQ f hf.continuous.measurable z
      (integrable_lipschitz_gaussian hf) hF.1
      (integrable_lipschitz_gaussian_affine hf _ _) hFU.1 hF.2 hFU.2 hp.1 hp.2
  · exact directional_surrogate_bias_le hf hl.1 hl.2.1 hQ z η hS.1 hS.2.1 hS.2.2 hp.2

/-- The explicit confidence logarithm gives the numerical tolerance required by the oracle. -/
private theorem parameter_surrogate_bias_bounds {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1)
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (z η : Space d)
    (hz : ‖z‖ ≤ paperRadius d (parameterLog d D n) / (2 * (d : ℝ))) (hη : ‖η‖ ≤ 1) :
    |(∫ x, f x * scalarCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z x ∂gaussian d) -
      surrogate (paperLambda d (parameterLog d D n)) f z| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) ∧
    |(∫ x, f x * directionalGradientCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z η x ∂gaussian d) -
      fderiv ℝ (surrogate (paperLambda d (parameterLog d D n)) f) z η| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) := by
  have hL := (parameterLog_bounds d n hD).1
  have hl := (paperLambda_bounds hd hL).1
  have h := paper_surrogate_bias_bounds hd hL hf hf0 z η hz hη
  constructor
  · apply h.1.trans
    apply le_trans ?_ (parameter_scalar_bias_le hd hn hD)
    gcongr
  · apply h.2.trans
    apply le_trans ?_ (parameter_directional_bias_le hd hn hD)
    gcongr


end LG2021.Concentration

end

/- LG2021ConcentrationConditional -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory




end LG2021.Concentration

end

/- LG2021ConcentrationOracleMoments -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A conditional mean is only needed on the support of the multiplier. -/
private theorem compProd_weighted_mean_on_support {A : Type*} [MeasurableSpace A]
    (P : Measure A) [SFinite P] (κ : Kernel A ℝ) [IsSFiniteKernel κ]
    (C f : A → ℝ)
    (hI : Integrable (fun p : A × ℝ => p.2 * C p.1) (P ⊗ₘ κ))
    (hmean : ∀ᵐ a ∂P, C a ≠ 0 → (∫ y, y ∂κ a) = f a) :
    (∫ p : A × ℝ, p.2 * C p.1 ∂(P ⊗ₘ κ)) = ∫ a, f a * C a ∂P := by
  rw [Measure.integral_compProd hI]
  apply integral_congr_ae
  filter_upwards [hmean] with a ha
  rw [integral_mul_const]
  by_cases hC : C a = 0
  · simp [hC]
  · rw [ha hC]

/-- Centering the actual scalar estimator gives a universal sub-Gaussian proxy. -/
private theorem scalarEstimator_centered_mgf {d : ℕ}
    (P : Measure (Space d)) [IsProbabilityMeasure P]
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hobs : ∀ᵐ x ∂P, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ => p.2 * scalarCoefficient lambda r z p.1) (P ⊗ₘ κ) ∧
    HasSubgaussianMGF (fun p : Space d × ℝ => p.2 * scalarCoefficient lambda r z p.1 -
      ∫ q : Space d × ℝ, q.2 * scalarCoefficient lambda r z q.1 ∂(P ⊗ₘ κ))
      (NNReal.mk (256 * (28 / lambda) ^ 2) (by positivity) : NNReal) (P ⊗ₘ κ) := by
  have hm := scalarEstimator_moment P κ r z hpos hsmall hd hobs
  have hC : Measurable (fun p : Space d × ℝ => scalarCoefficient lambda r z p.1) :=
    (Algorithm.measurable_scalarCoefficient lambda r).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  exact centered_hasSubgaussianMGF_of_exp_square (P ⊗ₘ κ)
    (fun p => p.2 * scalarCoefficient lambda r z p.1) (measurable_snd.mul hC)
    (by positivity) hm.1 hm.2

/-- The scalar estimator retains its exact weighted mean under a feasible-query fallback. -/
private theorem scalarEstimator_mean {d : ℕ}
    (P : Measure (Space d)) [IsProbabilityMeasure P]
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (f : Space d → ℝ)
    (hobs : ∀ᵐ x ∂P, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2)
    (hmean : ∀ᵐ x ∂P, truncation lambda r z x = 1 → (∫ y, y ∂κ x) = f x) :
    (∫ p : Space d × ℝ, p.2 * scalarCoefficient lambda r z p.1 ∂(P ⊗ₘ κ)) =
      ∫ x, f x * scalarCoefficient lambda r z x ∂P := by
  apply compProd_weighted_mean_on_support P κ (scalarCoefficient lambda r z) f
    (scalarEstimator_centered_mgf P κ r z hpos hsmall hd hobs).1
  filter_upwards [hmean] with x hx hC
  apply hx
  rcases truncation_zero_or_one lambda r z x with h | h
  · exfalso
    apply hC
    simp [scalarCoefficient, h]
  · exact h






end LG2021.Concentration

end

/- LG2021ConcentrationOracleGradient -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A finite exponential-absolute moment implies ordinary integrability. -/
private theorem integrable_of_exp_abs_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp (|X ω| / r)) P) : Integrable X P := by
  apply (hI.const_mul r).mono' hX.aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  have he := Real.add_one_le_exp (|X ω| / r)
  have hmul := mul_le_mul_of_nonneg_left he hr.le
  have hcancel : r * (|X ω| / r) = |X ω| := by field_simp
  nlinarith

/-- The actual gradient estimate has centered exponential-absolute radius `3072`. -/
private theorem gaussian_gradientEstimator_centered_moment {d : ℕ}
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hz : lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1)
      ((gaussian d) ⊗ₘ κ) ∧
    Integrable (fun p : Space d × ℝ => Real.exp
      (|p.2 * directionalGradientCoefficient lambda r z η p.1 -
        ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient lambda r z η q.1
          ∂((gaussian d) ⊗ₘ κ)| / 3072)) ((gaussian d) ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ, Real.exp
      (|p.2 * directionalGradientCoefficient lambda r z η p.1 -
        ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient lambda r z η q.1
          ∂((gaussian d) ⊗ₘ κ)| / 3072) ∂((gaussian d) ⊗ₘ κ)) ≤ 2 := by
  have hG : Measurable (fun p : Space d × ℝ => gradientCoefficient lambda r z p.1) :=
    (Algorithm.measurable_gradientCoefficient lambda r).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  have hX : Measurable (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1) :=
    measurable_snd.mul (hG.inner measurable_const)
  have hm := gaussian_directionalGradientEstimator_moment κ r z η hpos hsmall hd hz hη hobs
  have hc := exp_abs_centered_moment_scaled ((gaussian d) ⊗ₘ κ)
    (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1)
    hX (r := 768) (by norm_num) hm.1 hm.2
  refine ⟨integrable_of_exp_abs_scaled _ _ hX (r := 768) (by norm_num) hm.1, ?_⟩
  norm_num at hc
  exact ⟨hc.1, hc.2.1⟩

/-- The directional gradient mean is unaffected by the legal-query fallback outside the truncation. -/
private theorem gaussian_gradientEstimator_mean {d : ℕ}
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hz : lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1) (f : Space d → ℝ)
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2)
    (hmean : ∀ᵐ x ∂gaussian d, truncation lambda r z x = 1 → (∫ y, y ∂κ x) = f x) :
    (∫ p : Space d × ℝ, p.2 * directionalGradientCoefficient lambda r z η p.1
      ∂((gaussian d) ⊗ₘ κ)) = ∫ x, f x * directionalGradientCoefficient lambda r z η x ∂gaussian d := by
  apply compProd_weighted_mean_on_support (gaussian d) κ (directionalGradientCoefficient lambda r z η) f
    (gaussian_gradientEstimator_centered_moment κ r z η hpos hsmall hd hz hη hobs).1
  filter_upwards [hmean] with x hx hC
  apply hx
  rcases truncation_zero_or_one lambda r z x with h | h
  · exfalso
    apply hC
    simp [directionalGradientCoefficient, gradientCoefficient, h]
  · exact h




end LG2021.Concentration

end

/- LG2021ConcentrationPathLaw -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



























end LG2021.Concentration

end
end

/- LG2021ConcentrationFreshSeed -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
























end LG2021.Concentration

end
end

/- LG2021ConcentrationNoAnticipation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped Classical










end LG2021.Concentration

end
end

/- LG2021ConcentrationSeedCoordinates -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal

/-- All private coordinates other than one Gaussian vector. -/
private abbrev GaussianRemainder (d u n : ℕ) :=
  (Fin (n + 1) → Fin u → Space d) × (Fin n → Space d)

private def gaussianRemainderMeasure (d u : ℕ) (cfg : OracleConfig) :
    Measure (GaussianRemainder d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))).prod
      (Measure.pi (fun _ : Fin cfg.horizon => gaussian d))

private instance gaussianRemainderMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (gaussianRemainderMeasure d u cfg) := by
  unfold gaussianRemainderMeasure
  infer_instance















end LG2021.Concentration

end
end

/- LG2021ConcentrationPairPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



































end LG2021.Concentration

end
end

/- LG2021ConcentrationPairKernel -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR


























end LG2021.Concentration

end
end

/- LG2021ConcentrationObservationPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal Classical















end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableMeans -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm














end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm



end LG2021.Concentration

end
end

/- LG2021ConcentrationPathAccumulation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal






end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictable -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm



































end LG2021.Concentration

end
end

/- LG2021ConcentrationKernelPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm































end LG2021.Concentration

end
end

/- LG2021ConcentrationPathFinite -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal




end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableEstimators -/
section

noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal







end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal



end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableGradient -/
section

noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal







end LG2021.Concentration

end
end

/- LG2021ConcentrationBernstein -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory






end LG2021.Concentration

end

/- LG2021OracleConfidenceArithmetic -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory



























end LG2021.Concentration

end
end

/- LG2021ConcentrationHistoryPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



















end LG2021.Concentration

end
end

/- LG2021ConcentrationEstimatorConfidence -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal









end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal





end LG2021.Concentration

end
end

/- LG2021ConcentrationTerminalConfidence -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal







end LG2021.Concentration

end
end

/- LG2021AlgorithmInvariant -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory BilateralProfitMHR
open scoped Classical





























end LG2021.Algorithm

end
end

/- LG2021OracleSampleComplexity -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory













end LG2021.Algorithm

end
end

/- LG2021AlgorithmTrace -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical



























end LG2021.Algorithm

end
end

/- LG2021TraceSums -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration































end LG2021.Algorithm

end
end

/- LG2021TerminalTrace -/
section

noncomputable section

namespace LG2021.Algorithm













end LG2021.Algorithm

end
end

/- LG2021RegretAggregation -/
section

namespace LG2021







end LG2021

end

/- LG2021StageAggregation -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical























end LG2021.Algorithm

end
end

/- LG2021StageSampleCost -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical















end LG2021.Algorithm

end
end

/- LG2021StageRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory











end LG2021.Algorithm

end
end

/- LG2021TraceMeasurable -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory
open scoped Classical























end LG2021.Algorithm

end
end

/- LG2021ConcentrationStageEstimators -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm





















end LG2021.Concentration

end
end

/- LG2021ConcentrationSumExpansion -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm







end LG2021.Concentration

end
end

/- LG2021ConcentrationStageExpansion -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm













end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR





end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR







end LG2021.Concentration

end
end

/- LG2021AlgorithmEllipsoidHelpers -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod


end LG2021.Algorithm

end
end

/- LG2021AlgorithmShallow -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod



end LG2021.Algorithm

end
end

/- LG2021AlgorithmVolume -/
section

/-!
Minimum-ellipsoid and protected-volume adapters. The source simplex supplies
the protected positive volume. The geometric contraction is the explicit
shallow-cut theorem.
-/

noncomputable section
namespace LG2021.Algorithm

open Matrix MeasureTheory Set ModernConvex.Ellipsoids
open LG2021.JohnHelpers
open scoped ENNReal






















end LG2021.Algorithm

end
end

/- LG2021AlgorithmSimplex -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set
open scoped BigOperators Classical








end LG2021.Algorithm

end
end

/- LG2021GaussianGeometryConvex -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace







end LG2021

end
end

/- LG2021AlgorithmPreservation -/
section

/-! The stopping test and its actual confidence estimates preserve every
near-minimizing point. The strict margin also justifies inward rational rounding. -/

noncomputable section
namespace LG2021.Algorithm















end LG2021.Algorithm

end
end

/- LG2021AlgorithmStageVolume -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical

























end LG2021.Algorithm

end
end

/- LG2021CandidateSampling -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory











end LG2021.Algorithm

end
end

/- LG2021RateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration













end LG2021.Algorithm

end
end

/- LG2021AlgorithmStageRate -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory Concentration





















end LG2021.Algorithm

end
end

/- LG2021AlgorithmGoodHistory -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory



























end LG2021.Algorithm

end
end

/- LG2021ConcentrationStageBuffers -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR









end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR







end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR





end LG2021.Concentration

end
end

/- LG2021GuardedRegret -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Set
open scoped Classical



















namespace Algorithm





end Algorithm
end LG2021

end
end

/- LG2021PairRegret -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical

























end LG2021.Concentration

end
end

/- LG2021AlgorithmParameters -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration











end LG2021.Algorithm

end
end

/- LG2021ConcentrationActualBias -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical



end LG2021.Concentration

end
end

/- LG2021ConcentrationStageBias -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical










end LG2021.Concentration

end
end

/- LG2021ConcentrationStageEvents -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm









end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm





end LG2021.Concentration

end
end

/- LG2021StageStarts -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical











end LG2021.Algorithm

end
end

/- LG2021ConcentrationActualConfidence -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ConfidencePrefix -/
section

noncomputable section

namespace LG2021.Algorithm











end LG2021.Algorithm

end
end

/- LG2021WinnerSamples -/
section

noncomputable section

namespace LG2021.Algorithm



end LG2021.Algorithm

end
end

/- LG2021ConcentrationGoodHistory -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ConcentrationConfidenceEvent -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory









end LG2021.Concentration

end
end

/- LG2021ConcentrationCandidateCoordinates -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal

private abbrev CandidateRemainder (d u n : ℕ) :=
  (Fin n → Fin u → Space d) × (Fin (n + 1) → Space d)

private def candidateBlockMeasure (d u : ℕ) (cfg : OracleConfig) : Measure (Fin u → Space d) :=
  Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ))))

private instance candidateBlockMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (candidateBlockMeasure d u cfg) := by
  unfold candidateBlockMeasure
  infer_instance

private def candidateRemainderMeasure (d u : ℕ) (cfg : OracleConfig) :
    Measure (CandidateRemainder d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin cfg.horizon => candidateBlockMeasure d u cfg)).prod
    (Measure.pi (fun _ : Fin (cfg.horizon + 1) => gaussian d))

private instance candidateRemainderMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (candidateRemainderMeasure d u cfg) := by
  unfold candidateRemainderMeasure
  infer_instance


















end LG2021.Concentration

end
end

/- LG2021CurrentConfidence -/
section

noncomputable section

namespace LG2021.Algorithm

set_option maxHeartbeats 1000000





end LG2021.Algorithm

end
end

/- LG2021FinalRateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm













end LG2021.Algorithm

end
end

/- LG2021CandidateHitGeometry -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm

open Set MeasureTheory Concentration
open scoped Classical















end LG2021.Algorithm

end
end

/- LG2021CandidateHitEvent -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm

open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical





















end LG2021.Algorithm

end
end

/- LG2021CandidateNormSupport -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal











end LG2021.Algorithm

end
end

/- LG2021CandidateHitTerminal -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical





















end LG2021.Algorithm

end
end

/- LG2021CandidateHitLift -/
section

noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration







end LG2021.Algorithm

end
end

/- LG2021PairLossMartingale -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical

















end LG2021.Concentration

end
end

/- LG2021PairLossTerminal -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical

























end LG2021.Concentration

end
end

/- LG2021PairLossTrace -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical







end LG2021.Concentration

end
end

/- LG2021ConcentrationTerminalGood -/
section

noncomputable section
set_option maxHeartbeats 1500000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory







end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ComparatorNonneg -/
section

noncomputable section

namespace LG2021.Algorithm





end LG2021.Algorithm

end
end

/- LG2021PathwiseRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration









end LG2021.Algorithm

end
end

/- LG2021DeterministicClosure -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Algorithm

open MeasureTheory Concentration Set



end LG2021.Algorithm

end
end

/- LG2021ExpectedRegret -/
section

noncomputable section

namespace LG2021

open MeasureTheory BilateralProfitMHR
open scoped ENNReal









end LG2021

end
end

/- LG2021CanonicalExpectedRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Concentration
open scoped ENNReal









end LG2021.Algorithm

end
end

/- Canonical fixed-dimensional bandit theorem -/
section

noncomputable section
set_option maxHeartbeats 2000000

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric






end LG2021

end
end

/- LG2021LipschitzExtension -/
section

/-!
The global extension needed only in the analysis of the bandit policy.
The infimal-convolution construction follows the existing real Lipschitz
extension proof in Mathlib; compact convexity additionally preserves convexity.
The infimal-convolution formulation supplies the global extension used in the formal proof.
-/

noncomputable section

namespace LG2021

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]













end LG2021

end
end

/- LG2021Erosion -/
section

/-!
The known-body erosion used in Appendix F of Lattimore and György (2021).
The interior Lipschitz proof adapts Mathlib's convex secant argument, using
the loss range [0,1] to obtain the exact constant. The loss and its extension
are analysis objects; the eroded body uses only the known body and scale.
-/

noncomputable section
namespace LG2021

open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]









































end LG2021

end
end

/- CorollaryTransport -/
section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal











section Geometry

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]















end Geometry



section Observations

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]











end Observations

end BilateralProfitMHR.CorollaryTransport

end

/- CorollaryNormalization -/
section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal

























end BilateralProfitMHR.CorollaryTransport

end

/- LG2021ErosionTransport -/
section

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal







variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]





end LG2021

end
end

/- LG2021Reduction -/
section

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open scoped ENNReal



















end LG2021

end

/- LG2021CanonicalTransport -/
section

/-! Quantifier-preserving reduction from the canonical Lipschitz problem to
continuous convex losses, arbitrary affine dimension, and the stated noise norm.
The reduction preserves the choice of policy before the unknown loss and noise. -/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal








end LG2021

end
end

/- LG2021NormalizedTransport -/
section

noncomputable section

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric



end LG2021

end
end

/- LG2021SharpClosure -/
section

noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set







end LG2021.Algorithm

end
end

/- LG2021SharpRateBase -/
section

noncomputable section

namespace LG2021

open Concentration

































end LG2021

end
end

/- LG2021SharpRateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration






















end LG2021.Algorithm

end
end

section
namespace LG2021.Algorithm

end LG2021.Algorithm
end

/- LG2021SharpStageRate -/
section

noncomputable section

namespace LG2021.Algorithm

open Set MeasureTheory Concentration










end LG2021.Algorithm

end
end

/- LG2021SharpTransport -/
section

/-!
Transport of the explicit universal dimension bound through Lipschitz extension
and the known-body erosion. The comparator is an infimum, so the convex loss
need not be continuous at the boundary of its domain.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal











section Erosion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]





end Erosion





end LG2021

end
end

/- LG2021SharpRateFixed -/
section

noncomputable section

namespace LG2021










end LG2021

end
end

/- LG2021SharpSourceTransport -/
section

/-!
The explicit source rate for arbitrary locations of the contained unit ball.
The loss comparator is its infimum on the compact action set; whenever the
minimum is attained this equals the source's minimum comparator.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal

















end LG2021

end
end

/- LG2021SharpMain -/
section

noncomputable section
set_option maxHeartbeats 2000000

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric








end LG2021

end
end

open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric



open LG2021 LG2021.Concentration MeasureTheory ProbabilityTheory

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1)
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (z η : Space d) (hz : ‖z‖ ≤ paperRadius d (parameterLog d D n) / (2 * (d : ℝ)))
    (hη : ‖η‖ ≤ 1) (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ]
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2)
    (hmean : ∀ᵐ x ∂gaussian d,
      truncation (paperLambda d (parameterLog d D n)) (paperRadius d (parameterLog d D n)) z x = 1 →
        (∫ y, y ∂κ x) = f x) :
    |(∫ p : Space d × ℝ, p.2 * scalarCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z p.1 ∂((gaussian d) ⊗ₘ κ)) -
      surrogate (paperLambda d (parameterLog d D n)) f z| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) ∧
    |(∫ p : Space d × ℝ, p.2 * directionalGradientCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z η p.1 ∂((gaussian d) ⊗ₘ κ)) -
      fderiv ℝ (surrogate (paperLambda d (parameterLog d D n)) f) z η| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) := by
  have hL := (parameterLog_bounds d n hD).1
  have hl := paperLambda_bounds hd hL
  have hb := paper_candidate_shift_le_one hd hL z hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl.1] at hb
  rw [scalarEstimator_mean (gaussian d) κ _ z hl.1 hl.2.1 hl.2.2 f hobs hmean,
    gaussian_gradientEstimator_mean κ _ z η hl.1 hl.2.1 hl.2.2 hb hη f hobs hmean]
  exact parameter_surrogate_bias_bounds hd hn hD hf hf0 hK z η hz hη
