-- Prove2me | solution 1 for LG2021.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T17:09:04.216255+00:00
-- url     : https://prove2.me/submissions/8c9bd3f9-895d-411e-95d8-02ce878cb4d0

import Mathlib
import Definitions.Def_LG2021_Policy
import Theorems.Thm_LG2021_Algorithm_terminal_regret_of_current_bounds_sharp
import Theorems.Thm_LG2021_Concentration_exists_terminal_good_event
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
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGeometry -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Matrix
open scoped Classical
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
private theorem policy_isOn {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) {anchor : Space d} (ha : anchor ∈ K) :
    (policy (u := u) cfg K hK R anchor).IsOn K := by
  intro τ seed ys
  change (if proposedQuery cfg K R τ seed ys ∈ K then proposedQuery cfg K R τ seed ys
    else anchor) ∈ K
  split_ifs with h
  · exact h
  · exact ha
end LG2021.Algorithm
end
end
/- CorollaryNormalization -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
private theorem unitNoiseCond_noiseCond {X : Type} (K : Set X) (L : X → ℝ)
    (ν : ObsKernel X) (hν : UnitNoiseCond K L ν) : NoiseCond K L 1 ν := by
  intro τ xs ys x hxs hx
  obtain ⟨hp, hi, hm, hei, hem⟩ := hν τ xs ys x hxs hx
  refine ⟨hp, hi, hm, ?_⟩
  unfold HighDimProb.Concentration.subgaussianNorm
  refine iInf_le_of_le 1 (iInf_le_of_le (by norm_num) ?_)
  refine iInf_le_of_le (by simpa using hei) (iInf_le_of_le (by simpa using hem) ?_)
  rfl
end BilateralProfitMHR.CorollaryTransport
end
end
/- LG2021Process -/
section
namespace LG2021
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
private theorem observationKernel_isMarkov {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) (τ : ℕ) :
    IsMarkovKernel (observationKernel A ν hνm τ) := by
  constructor
  intro z
  exact (hν τ (A.pastQueries z.1 z.2) z.2 (A.query τ z.1 z.2)
    (fun i => hA i z.1 _) (hA τ z.1 z.2)).1
private theorem measurable_history_snoc {Ω : Type} [MeasurableSpace Ω] (τ : ℕ) :
    Measurable (fun z : (Ω × (Fin τ → ℝ)) × ℝ =>
      (z.1.1, (Fin.snoc z.1.2 z.2 : Fin (τ + 1) → ℝ))) := by
  apply Measurable.prodMk (by fun_prop)
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · fun_prop
  · fun_prop
/-- Measurability of the actual finite-horizon nested cost, using only the
policy's measurable decisions and the environment's measurable probability kernels. -/
private theorem measurable_cumLoss_of_queryCost {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2)))
    (m τ : ℕ) :
    Measurable (fun z : Ω × (Fin τ → ℝ) => cumLoss A ν g z.1 m τ z.2) := by
  induction m generalizing τ with
  | zero => exact measurable_const
  | succ m ih =>
      let κ := observationKernel A ν hνm τ
      letI : IsMarkovKernel κ := observationKernel_isMarkov A ν hνm hA L γ hν τ
      have hnext := (ih (τ + 1)).comp (measurable_history_snoc τ)
      have hint := hnext.lintegral_kernel_prod_right' (κ := κ)
      exact (hg τ).add hint
end LG2021
end
/- LG2021Concentration -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationProducts -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationCentering -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationEstimators -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationObservation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationKernelMoments -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianMoments -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal
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
end LG2021.Concentration
end
/- LG2021ConcentrationFinite -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationTruncation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationGaussianTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationParameterTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
end LG2021.Concentration
end
/- LG2021GaussianGeometrySurrogate -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021ConcentrationEnvelopes -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationBias -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianGeometryTranslation -/
section
noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
end LG2021.GaussianTranslation
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryDensity -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021GaussianGeometryAffine -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryChangeOfMeasure -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryMollification -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
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
end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory
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
end LG2021
end
end
/- LG2021ConcentrationSurrogateBias -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationLemma4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
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
end LG2021.Concentration
end
/- LG2021ConcentrationOracleGradient -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationPathLaw -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
private theorem historyMeasure_probability {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ) :
    IsProbabilityMeasure (historyMeasure A P ν hνm τ) := by
  induction τ with
  | zero =>
      unfold historyMeasure
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | succ τ ih =>
      letI := ih
      letI := observationKernel_isMarkov A ν hνm hA L γ hν τ
      unfold historyMeasure
      exact Measure.isProbabilityMeasure_map (measurable_history_snoc τ).aemeasurable
private theorem lintegral_historyMeasure_zero {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    (F : Ω × (Fin 0 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A P ν hνm 0) = ∫⁻ ω, F (ω, Fin.elim0) ∂P := by
  exact lintegral_map hF (by fun_prop)
/-- Integration against the history law exactly reproduces one observation-kernel step. -/
private theorem lintegral_historyMeasure_succ {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ)
    (F : Ω × (Fin (τ + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A P ν hνm (τ + 1)) =
      ∫⁻ w, ∫⁻ y, F (w.1, Fin.snoc w.2 y)
        ∂ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2)
          ∂historyMeasure A P ν hνm τ := by
  letI := historyMeasure_probability A P ν hνm hA L γ hν τ
  letI := observationKernel_isMarkov A ν hνm hA L γ hν τ
  rw [historyMeasure, lintegral_map hF (measurable_history_snoc τ)]
  exact Measure.lintegral_compProd
    (show Measurable (fun z : (Ω × (Fin τ → ℝ)) × ℝ => F (z.1.1, Fin.snoc z.1.2 z.2))
      from hF.comp (measurable_history_snoc τ))
/-- The nested conditional cost is the sum of the actual query marginal costs. -/
private theorem lintegral_cumLoss_eq_sum {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2)))
    (m τ : ℕ) :
    (∫⁻ w, cumLoss A ν g w.1 m τ w.2 ∂historyMeasure A P ν hνm τ) =
      ∑ i ∈ Finset.range m, ∫⁻ w, g (A.query (τ + i) w.1 w.2)
        ∂historyMeasure A P ν hνm (τ + i) := by
  induction m generalizing τ with
  | zero => simp [cumLoss]
  | succ m ih =>
      have hnext := measurable_cumLoss_of_queryCost A ν hνm hA L γ hν g hg m (τ + 1)
      change (∫⁻ w, g (A.query τ w.1 w.2) +
        ∫⁻ y, cumLoss A ν g w.1 m (τ + 1) (Fin.snoc w.2 y)
          ∂ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2)
        ∂historyMeasure A P ν hνm τ) = _
      rw [lintegral_add_left (hg τ),
        ← lintegral_historyMeasure_succ A P ν hνm hA L γ hν τ _ hnext, ih]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun j : ℕ => ∫⁻ w, g (A.query j w.1 w.2)
        ∂historyMeasure A P ν hνm j) (by omega : τ + 1 + i = τ + (i + 1))
/-- Exact connection between the paper's seeded observation semantics and the finite history law. -/
private theorem expectedCumLoss_eq_sum_marginals {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2))) (n : ℕ) :
    expectedCumLoss A P ν g n =
      ∑ i ∈ Finset.range n, ∫⁻ w, g (A.query i w.1 w.2) ∂historyMeasure A P ν hνm i := by
  have h := lintegral_cumLoss_eq_sum A P ν hνm hA L γ hν g hg n 0
  rw [lintegral_historyMeasure_zero A P ν hνm _
    (measurable_cumLoss_of_queryCost A ν hνm hA L γ hν g hg n 0)] at h
  apply h.trans
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun j : ℕ => ∫⁻ w, g (A.query j w.1 w.2)
    ∂historyMeasure A P ν hνm j) (Nat.zero_add i)
private theorem pastQueries_snoc {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ω : Ω) {τ : ℕ} (ys : Fin τ → ℝ) (y : ℝ) :
    A.pastQueries ω (Fin.snoc ys y) = Fin.snoc (A.pastQueries ω ys) (A.query τ ω ys) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, QueryAlg.pastQueries]
    congr 1
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y k.castSucc = ys k
    simp only [Fin.snoc_castSucc]
  · simp only [Fin.snoc_castSucc, QueryAlg.pastQueries]
    congr 1
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y (Fin.castLE j.isLt.le k).castSucc = ys (Fin.castLE j.isLt.le k)
    simp only [Fin.snoc_castSucc]
private theorem pathCost_snoc {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (g : X → ℝ≥0∞) (ω : Ω) {τ : ℕ} (ys : Fin τ → ℝ) (y : ℝ) :
    pathCost A g (ω, Fin.snoc ys y) = pathCost A g (ω, ys) + g (A.query τ ω ys) := by
  simp [pathCost, pastQueries_snoc, Fin.sum_univ_castSucc]
private theorem measurable_pathCost {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2))) (τ : ℕ) :
    Measurable (pathCost (τ := τ) A g) := by
  apply Finset.measurable_fun_sum
  intro i hi
  exact (hg i).comp (show Measurable (fun w : Ω × (Fin τ → ℝ) =>
    (w.1, fun j => w.2 (Fin.castLE i.isLt.le j))) from by fun_prop)
/-- The pathwise total integrates to the sum of the actual query marginal costs. -/
private theorem lintegral_pathCost_eq_sum {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2))) (n : ℕ) :
    (∫⁻ w, pathCost A g w ∂historyMeasure A P ν hνm n) =
      ∑ i ∈ Finset.range n, ∫⁻ w, g (A.query i w.1 w.2) ∂historyMeasure A P ν hνm i := by
  induction n with
  | zero => simp [pathCost]
  | succ n ih =>
      rw [lintegral_historyMeasure_succ A P ν hνm hA L γ hν n _ (measurable_pathCost A g hg _)]
      have hinner (w : Ω × (Fin n → ℝ)) :
          (∫⁻ y, pathCost A g (w.1, Fin.snoc w.2 y)
            ∂ν n (A.pastQueries w.1 w.2) w.2 (A.query n w.1 w.2)) =
            pathCost A g w + g (A.query n w.1 w.2) := by
        letI := (hν n (A.pastQueries w.1 w.2) w.2 (A.query n w.1 w.2)
          (fun i => hA i w.1 _) (hA n w.1 w.2)).1
        simp only [pathCost_snoc]
        simp
      simp_rw [hinner]
      rw [lintegral_add_left (measurable_pathCost A g hg n), ih, Finset.sum_range_succ]
/-- Exact expected-cost semantics on one common finite path probability space. -/
private theorem expectedCumLoss_eq_lintegral_pathCost {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2))) (n : ℕ) :
    expectedCumLoss A P ν g n = ∫⁻ w, pathCost A g w ∂historyMeasure A P ν hνm n := by
  rw [expectedCumLoss_eq_sum_marginals A P ν hνm hA L γ hν g hg,
    lintegral_pathCost_eq_sum A P ν hνm hA L γ hν g hg]
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
private theorem oracleConcentrationConstant_pos : 0 < oracleConcentrationConstant := by
  norm_num [oracleConcentrationConstant]
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
private theorem sliceRadius_pos : 0 < sliceRadius := Real.sqrt_pos.mpr (by norm_num)
private theorem source_simplex_dim {d : ℕ} (hd : 0 < d) {K : Set (Space d)} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : Space d) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {x : Space d} (hx : x ∈ K) :
    ∃ v : Fin (d + 1) → Space d, Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^d * sliceRadius^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  simpa only [sliceRadius] using LG2021.nearby_simplex_volume hd hcv hball hD hδ hδD hdiam hx
private theorem source_protected_simplex {d : ℕ} (hd : 0 < d) {K : Set (Space d)} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : Space d) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) {x : Space d} (hx : x ∈ K)
    (f : Space d → ℝ) (hf : LipschitzOnWith 1 f K) :
    ∃ v : Fin (d + 1) → Space d, Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, f (v i) ≤ f x + δ) ∧
      ENNReal.ofReal ((δ / D)^d * sliceRadius^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by
  obtain ⟨v, hinj, hv0, hvK, hdist, hvol⟩ := source_simplex_dim hd hcv hball hD hδ hδD hdiam hx
  refine ⟨v, hinj, hv0, hvK, ?_, hvol⟩
  intro i
  have h := hf.le_add_mul (hvK i) hx
  simp only [NNReal.coe_one, one_mul] at h
  have hd' : dist (v i) x ≤ δ := by simpa [dist_comm] using hdist i
  linarith
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
private theorem candidateCount_pos {n : ℕ} (hn : 1 ≤ n) : 0 < candidateCount n := by
  apply Nat.one_le_ceil_iff.2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 < 3 * (n : ℝ) ^ 2 := by nlinarith
  exact mul_pos (by norm_num) (Real.log_pos hp)
end LG2021.Algorithm
end
end
/- LG2021RateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
private theorem log_horizon_lower {n : ℕ} (hn : 2 ≤ n) : (1 / 2 : ℝ) ≤ Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  exact htwo.trans (Real.log_le_log (by norm_num) hnR)
private theorem candidateCount_upper {n : ℕ} (hn : 1 ≤ n) :
    (candidateCount n : ℝ) ≤ 145 * (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have harg : 1 ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 3 * (n : ℝ) ^ 2)
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) (Real.log_nonneg harg))
  change (candidateCount n : ℝ) < _ at hceil
  nlinarith
private theorem confidenceLog_candidateCount_le (cfg : OracleConfig) {n : ℕ}
    (hn : 2 ≤ n) (horizon : cfg.horizon = n) :
    confidenceLog cfg (candidateCount n) ≤ 875 * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hupos : (0 : ℝ) < candidateCount n := by exact_mod_cast candidateCount_pos (by omega : 1 ≤ n)
  have hu := candidateCount_upper (by omega : 1 ≤ n)
  have hlogn := log_horizon_lower hn
  have hbound : 3 * (candidateCount n : ℝ) * (n : ℝ) ^ 3 ≤ 435 * (n : ℝ) ^ 5 := by
    nlinarith [mul_le_mul_of_nonneg_right hu (show 0 ≤ 3 * (n : ℝ) ^ 3 by positivity)]
  have hh := Real.log_le_log (show 0 < 3 * (candidateCount n : ℝ) * (n : ℝ) ^ 3 by positivity) hbound
  have hsplit : Real.log (435 * (n : ℝ) ^ 5) = Real.log 435 + 5 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  rw [hsplit] at hh
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 435)
  unfold confidenceLog
  rw [horizon]
  linarith
end LG2021.Algorithm
end
end
/- LG2021AlgorithmStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
private theorem sourceSimplexVolume_log_lower (d : ℕ) {D : ℝ} (hD : 0 < D) (L : ℝ) :
    -(d : ℝ) * L - (d : ℝ) * Real.log D - simplexLogPenalty d ≤
      Real.log (sourceSimplexVolume d D L / (2 : ℝ)^d) := by
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have ht := sliceRadius_pos
  have heq : Real.log (sourceSimplexVolume d D L / (2 : ℝ)^d) =
      -(d : ℝ) * L - (d : ℝ) * Real.log D +
        ((d - 1 : ℕ) : ℝ) * Real.log sliceRadius -
        Real.log (2 * (d.factorial : ℝ)) - (d : ℝ) * Real.log 2 := by
    unfold sourceSimplexVolume
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (pow_pos sliceRadius_pos _).ne',
      Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_div (Real.exp_pos _).ne' hD.ne', Real.log_exp]
    ring
  rw [heq]
  have h1 := le_abs_self (Real.log (2 * (d.factorial : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log 2)) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have h3 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log sliceRadius))
    (Nat.cast_nonneg (d - 1) : (0 : ℝ) ≤ (d - 1 : ℕ))
  unfold simplexLogPenalty
  nlinarith
private theorem parameter_delta_le_horizon (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-parameterLog d D n) ≤ 1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : 1 ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hbase : 4 * (n : ℝ) ≤ parameterBase d D n := by
    have h := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 10^6 * ((n : ℝ) + 1) by positivity)
    unfold parameterBase
    nlinarith
  have hA := (parameterBase_bounds d n hD).1
  have hlogA : 0 ≤ Real.log (parameterBase d D n) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_log (show 0 < 4 * (n : ℝ) by positivity) hbase
  have hL : Real.log (4 * (n : ℝ)) ≤ parameterLog d D n := by
    unfold parameterLog
    linarith
  calc
    _ ≤ Real.exp (-Real.log (4 * (n : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hL)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGoodHistory -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory
private theorem exists_source_analysis_simplex {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n)
    {K : Set (Space d)} (hcv : Convex ℝ K) (hball : Metric.closedBall (0 : Space d) 1 ⊆ K)
    {D : ℝ} (hD : 1 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : Space d} (hx : x ∈ K) (f : Space d → ℝ) (hf : LipschitzWith 1 f) :
    ∃ v : Fin (d + 1) → Space d, Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧
      (∀ i, f (v i) ≤ f x + Real.exp (-Concentration.parameterLog d D n)) ∧
      ENNReal.ofReal (sourceSimplexVolume d D (Concentration.parameterLog d D n)) ≤
        volume (convexHull ℝ (range v)) := by
  have hdelta := parameter_delta_le_horizon d hn (by linarith : 0 ≤ D)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdeltaD : Real.exp (-Concentration.parameterLog d D n) ≤ D := by
    apply hdelta.trans
    apply le_trans _ hD
    exact (div_le_one (by positivity : 0 < 4 * (n : ℝ))).mpr (by linarith)
  exact source_protected_simplex hd hcv hball (by linarith) (Real.exp_pos _) hdeltaD
    hdiam hx f hf.lipschitzOnWith
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
private theorem oracleConfig_bounds {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ (oracleConfig d D n).radius ∧
    0 < (oracleConfig d D n).lambda ∧ (oracleConfig d D n).lambda ≤ 1 / 2 ∧
    1 ≤ (oracleConfig d D n).momentConstant ∧
    0 < (oracleConfig d D n).concentrationConstant ∧
    (oracleConfig d D n).concentrationConstant ≤ 1 ∧
    1 ≤ confidenceLog (oracleConfig d D n) (candidateCount n) := by
  have hL := (parameterLog_bounds d n hD).1
  have hr := (paperRadius_bounds hd hL).1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := paperLambda_bounds hd hL
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (1 : ℝ) ≤ candidateCount n := by exact_mod_cast candidateCount_pos (by omega : 1 ≤ n)
  refine ⟨?_, hl.1, hl.2.1, ?_, oracleConcentrationConstant_pos, ?_, ?_⟩
  · change 1 ≤ paperRadius d (parameterLog d D n)
    nlinarith
  · norm_num [oracleConfig, oracleMomentConstant]
  · norm_num [oracleConfig, oracleConcentrationConstant]
  · unfold confidenceLog oracleConfig
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he := Real.exp_one_lt_three
    have hpow : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 3
      norm_num at hp
      exact hp
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ) ^ 3 by positivity)]
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
private theorem lintegral_le_good_bound_add_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞)
    {G : Set Ω} (hG : MeasurableSet G) {B N p : ℝ}
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hglobal : ∀ ω, X ω ≤ ENNReal.ofReal N)
    (hgood : ∀ ω ∈ G, X ω ≤ ENNReal.ofReal B)
    (hbad : μ.real Gᶜ ≤ p) :
    (∫⁻ ω, X ω ∂μ) ≤ ENNReal.ofReal (B + N * p) := by
  have hpoint (ω : Ω) : X ω ≤ ENNReal.ofReal B +
      Gᶜ.indicator (fun _ => ENNReal.ofReal N) ω := by
    by_cases hω : ω ∈ G
    · simpa [hω] using hgood ω hω
    · simpa [hω] using (hglobal ω).trans (le_add_left le_rfl)
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal B + Gᶜ.indicator (fun _ => ENNReal.ofReal N) ω) ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal B + ENNReal.ofReal N * μ Gᶜ := by
      rw [lintegral_add_left measurable_const, lintegral_indicator hG.compl]
      simp
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal N * ENNReal.ofReal p := by
      have hm : μ Gᶜ ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ Gᶜ)]
        exact ENNReal.ofReal_le_ofReal hbad
      gcongr
    _ = ENNReal.ofReal (B + N * p) := by
      rw [← ENNReal.ofReal_mul hN, ← ENNReal.ofReal_add hB (mul_nonneg hN hp)]
private theorem pathCost_le_horizon {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) {K : Set X} (hA : A.IsOn K) (g : X → ℝ≥0∞)
    (hg : ∀ x ∈ K, g x ≤ 1) {n : ℕ} (w : Ω × (Fin n → ℝ)) :
    Concentration.pathCost A g w ≤ n := by
  unfold Concentration.pathCost
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℝ≥0∞) := Finset.sum_le_sum fun i _ => hg _ (hA i w.1 _)
    _ = _ := by simp
private theorem expectedCost_le_of_path_good {X Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (g : X → ℝ≥0∞)
    (hg : ∀ τ, Measurable (fun z : Ω × (Fin τ → ℝ) => g (A.query τ z.1 z.2)))
    (hunit : ∀ x ∈ K, g x ≤ 1) (n : ℕ)
    {G : Set (Ω × (Fin n → ℝ))} (hG : MeasurableSet G) {B p : ℝ}
    (hB : 0 ≤ B) (hp : 0 ≤ p)
    (hgood : ∀ w ∈ G, Concentration.pathCost A g w ≤ ENNReal.ofReal B)
    (hbad : (Concentration.historyMeasure A P ν hνm n).real Gᶜ ≤ p) :
    expectedCumLoss A P ν g n ≤ ENNReal.ofReal (B + (n : ℝ) * p) := by
  letI := Concentration.historyMeasure_probability A P ν hνm hA L γ hν n
  rw [Concentration.expectedCumLoss_eq_lintegral_pathCost A P ν hνm hA L γ hν g hg n]
  apply lintegral_le_good_bound_add_bad _ _ hG hB (Nat.cast_nonneg _) hp _ hgood hbad
  intro w
  simpa using pathCost_le_horizon A hA g hunit w
end LG2021
end
end
/- LG2021CanonicalExpectedRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Concentration
open scoped ENNReal
private theorem pathCost_regret_eq_ofReal {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) {K : Set X} (hA : A.IsOn K) (f : X → ℝ) (baseline : ℝ)
    (hmin : ∀ x ∈ K, baseline ≤ f x) {n : ℕ} (w : Ω × (Fin n → ℝ)) :
    pathCost A (fun x => ENNReal.ofReal (f x - baseline)) w =
      ENNReal.ofReal (realPathLoss A f w - (n : ℝ) * baseline) := by
  unfold pathCost realPathLoss
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ f (A.pastQueries w.1 w.2 i) - baseline := by
    intro i _
    exact sub_nonneg.2 (hmin _ (hA i w.1 _))
  change (∑ i : Fin n, ENNReal.ofReal (f (A.pastQueries w.1 w.2 i) - baseline)) = _
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  rw [Finset.sum_sub_distrib]
  simp
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
private theorem convexLipschitzExtension_attains {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (x : E) :
    ∃ y ∈ K, convexLipschitzExtension K C f x = f y + (C : ℝ) * ‖x - y‖ ∧
      ∀ z ∈ K, convexLipschitzExtension K C f x ≤ f z + (C : ℝ) * ‖x - z‖ := by
  have hc : ContinuousOn (fun y => f y + (C : ℝ) * ‖x - y‖) K :=
    hf.add (continuousOn_const.mul (continuous_const.sub continuous_id).norm.continuousOn)
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne hc
  have hleast : IsLeast ((fun z => f z + (C : ℝ) * ‖x - z‖) '' K)
      (f y + (C : ℝ) * ‖x - y‖) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact hmin hz
  have he : convexLipschitzExtension K C f x = f y + (C : ℝ) * ‖x - y‖ := hleast.csInf_eq
  exact ⟨y, hy, he, fun z hz => he.trans_le (hmin hz)⟩
private theorem convexLipschitzExtension_agrees {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : LipschitzOnWith C f K) :
    EqOn (convexLipschitzExtension K C f) f K := by
  intro x hx
  obtain ⟨y, hy, he, hbound⟩ := convexLipschitzExtension_attains hK hne C f hf.continuousOn x
  apply le_antisymm
  · simpa using hbound x hx
  · rw [he]
    simpa only [dist_eq_norm] using hf.le_add_mul hx hy
private theorem convexLipschitzExtension_lipschitz {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) :
    LipschitzWith C (convexLipschitzExtension K C f) := by
  apply LipschitzWith.of_le_add_mul C
  intro x y
  obtain ⟨u, hu, hy, _⟩ := convexLipschitzExtension_attains hK hne C f hf y
  obtain ⟨_, _, _, hx⟩ := convexLipschitzExtension_attains hK hne C f hf x
  have htri : ‖x - u‖ ≤ ‖x - y‖ + ‖y - u‖ := norm_sub_le_norm_sub_add_norm_sub x y u
  calc
    convexLipschitzExtension K C f x ≤ f u + (C : ℝ) * ‖x - u‖ := hx u hu
    _ ≤ f u + (C : ℝ) * (‖x - y‖ + ‖y - u‖) := by gcongr
    _ = convexLipschitzExtension K C f y + (C : ℝ) * dist x y := by
      rw [hy, dist_eq_norm]
      ring
private theorem convexLipschitzExtension_convex {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (hfc : ConvexOn ℝ K f) :
    ConvexOn ℝ Set.univ (convexLipschitzExtension K C f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨u, hu, hxu, _⟩ := convexLipschitzExtension_attains hK hne C f hf x
  obtain ⟨v, hv, hyv, _⟩ := convexLipschitzExtension_attains hK hne C f hf y
  obtain ⟨_, _, _, hmix⟩ := convexLipschitzExtension_attains hK hne C f hf (a • x + b • y)
  have hz : a • u + b • v ∈ K := hfc.1 hu hv ha hb hab
  have hcost := hmix (a • u + b • v) hz
  have hconv := hfc.2 hu hv ha hb hab
  have hnorm : ‖a • x + b • y - (a • u + b • v)‖ ≤
      a * ‖x - u‖ + b * ‖y - v‖ := by
    have he : a • x + b • y - (a • u + b • v) = a • (x - u) + b • (y - v) := by module
    rw [he]
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb])
  have hmult := mul_le_mul_of_nonneg_left hnorm C.property
  simp only [smul_eq_mul] at hconv ⊢
  rw [hxu, hyv]
  nlinarith
private theorem convexLipschitzExtension_nonneg {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ≥0) (f : E → ℝ) (hf : ContinuousOn f K) (hfn : ∀ y ∈ K, 0 ≤ f y) (x : E) :
    0 ≤ convexLipschitzExtension K C f x := by
  obtain ⟨y, hy, he, _⟩ := convexLipschitzExtension_attains hK hne C f hf x
  rw [he]
  exact add_nonneg (hfn y hy) (mul_nonneg C.property (norm_nonneg _))
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
private theorem mapQuery_isOn (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    {K : Set X} {R : Set Y} (hA : A.IsOn R) (hfK : Set.MapsTo f R K) :
    (mapQuery f hf A).IsOn K := by
  intro τ ω y
  exact hfK (hA τ ω y)
private theorem pullKernel_measurable (f : Y → X) (hf : Measurable f)
    (ν : ObsKernel X) (hν : ν.IsMeasurable) : (pullKernel f ν).IsMeasurable := by
  intro τ
  change Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ν τ (fun i => f (w.1 i)) w.2.1 (f w.2.2))
  exact (hν τ).comp (show Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ((fun i => f (w.1 i)), w.2.1, f w.2.2)) from by fun_prop)
private theorem cumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (ν : ObsKernel X) (g : X → ℝ≥0∞) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (mapQuery f hf A) ν g ω m τ y =
      cumLoss A (pullKernel f ν) (g ∘ f) ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, mapQuery, Function.comp_apply]
      congr 1
      apply lintegral_congr
      intro z
      exact ih (τ + 1) (Fin.snoc y z)
private theorem expectedCumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν g n =
      expectedCumLoss A P (pullKernel f ν) (g ∘ f) n := by
  apply lintegral_congr
  intro ω
  exact cumLoss_mapQuery f hf A ν g ω n 0 Fin.elim0
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
private theorem sInf_loss_image {X Y : Type} (f : Y → X) {R : Set Y} {K : Set X}
    (himage : f '' R = K) (L : X → ℝ) :
    sInf ((L ∘ f) '' R) = sInf (L '' K) := by
  change sInf ((fun x => L (f x)) '' R) = _
  rw [← Set.image_image L f R, himage]
private theorem expectedRegret_mapQuery {X Y Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω] (f : Y → X) (hf : Measurable f)
    {R : Set Y} {K : Set X} (himage : f '' R = K) (L : X → ℝ)
    (A : QueryAlg Y Ω) (P : Measure Ω) (ν : ObsKernel X) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n =
    expectedCumLoss A P (pullKernel f ν)
      (fun x => ENNReal.ofReal ((L ∘ f) x - sInf ((L ∘ f) '' R))) n := by
  rw [expectedCumLoss_mapQuery, sInf_loss_image f himage L]
  rfl
private theorem pullKernel_unitNoiseCond {X Y : Type} (f : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hfK : Set.MapsTo f R K) (L : X → ℝ)
    (hν : UnitNoiseCond K L ν) : UnitNoiseCond R (L ∘ f) (pullKernel f ν) := by
  intro τ xs ys x hxs hx
  exact hν τ (fun i => f (xs i)) ys (f x) (fun i => hfK (hxs i)) (hfK hx)
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
private theorem sharpPathBound_nonneg (d : ℕ) (D : ℝ) (n : ℕ) : 0 ≤ sharpPathBound d D n := by
  unfold sharpPathBound separationFactor
  positivity
end LG2021.Algorithm
end
end
/- LG2021SharpRateBase -/
section
noncomputable section
namespace LG2021
open Concentration
private theorem sourceLog_lower {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    1 ≤ Real.log ((n : ℝ) * D) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hND : (4 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  apply (Real.le_log_iff_exp_le (by positivity : 0 < (n : ℝ) * D)).2
  linarith [Real.exp_one_lt_three]
private theorem parameterLog_le_sourceLog {d n : ℕ} (hdn : d ≤ n) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) :
    parameterLog d D n ≤ 416 * Real.log ((n : ℝ) * D) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hND : (4 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  have hconst : (10 ^ 6 : ℝ) ≤ ((n : ℝ) * D) ^ 10 := by
    calc
      _ ≤ (4 : ℝ) ^ 10 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hND 10
  have hd1 : (d : ℝ) + 1 ≤ (n : ℝ) * D := by nlinarith
  have hD1 : D + 1 ≤ (n : ℝ) * D := by nlinarith
  have hn1 : (n : ℝ) + 1 ≤ (n : ℝ) * D := by nlinarith
  have hbase : parameterBase d D n ≤ ((n : ℝ) * D) ^ 13 := by
    calc
      _ ≤ ((n : ℝ) * D) ^ 10 * ((n : ℝ) * D) *
          ((n : ℝ) * D) * ((n : ℝ) * D) := by
        unfold parameterBase
        gcongr
      _ = _ := by ring
  have hbasepos : 0 < parameterBase d D n := by
    unfold parameterBase
    positivity
  have hlog := Real.log_le_log hbasepos hbase
  rw [Real.log_pow] at hlog
  unfold parameterLog
  norm_num at hlog
  linarith
private theorem sharpRate_nonneg {d n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    0 ≤ sharpRate d D n := by
  unfold sharpRate
  have ht := sourceLog_lower hn hD
  positivity
private theorem sharpRate_lower {d n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n ≤ sharpRate d D n := by
  have ht := sourceLog_lower hn hD
  have hst := Real.one_le_sqrt.2 ht
  have hf : 1 ≤ Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D)) := by
    nlinarith
  have hm : (1 : ℝ) ≤ max 1 (Real.sqrt (Real.log ((n : ℝ) * D)) / (d : ℝ)) := le_max_left _ _
  unfold sharpRate
  calc
    _ = ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n) * 1 * 1 := by ring
    _ ≤ _ := by gcongr
private theorem one_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) : 1 ≤ sharpRate d D n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsd := Real.one_le_sqrt.2 hdR
  have hsn := Real.one_le_sqrt.2 hnR
  have hp : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hdR
  apply le_trans _ (sharpRate_lower hn hD)
  calc
    (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n := by gcongr
private theorem dimension_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) : (d : ℝ) ≤ sharpRate d D n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsd := Real.one_le_sqrt.2 hdR
  have hsn := Real.one_le_sqrt.2 hnR
  have hp : (d : ℝ) ≤ (d : ℝ) ^ 4 := le_self_pow₀ hdR (by decide : 4 ≠ 0)
  apply le_trans _ (sharpRate_lower hn hD)
  calc
    (d : ℝ) = (d : ℝ) * 1 * 1 := by ring
    _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n := by gcongr
private theorem trivial_horizon_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (hnd : n ≤ d) {D : ℝ} (hD : 2 ≤ D) : (n : ℝ) ≤ sharpRate d D n := by
  have hndR : (n : ℝ) ≤ d := by exact_mod_cast hnd
  exact hndR.trans (dimension_le_sharpRate hd hn hD)
private theorem sharpRate_eq_max {d n : ℕ} (hd : 0 < d) {D : ℝ}
    (ht : 0 ≤ Real.log ((n : ℝ) * D)) :
    sharpRate d D n =
      max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n *
          (Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D))))
        ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n *
          Real.log ((n : ℝ) * D) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq := Real.sq_sqrt ht
  unfold sharpRate
  rw [mul_max_of_nonneg _ _ (by positivity)]
  simp only [mul_one]
  congr 1
  field_simp
  linear_combination Real.sqrt n * Real.log ((n : ℝ) * D) * hsq
private theorem dimension_sqrt_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) : (d : ℝ) * Real.sqrt d ≤ sharpRate d D n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hsn := Real.one_le_sqrt.2 hnR
  have hp : (d : ℝ) ≤ (d : ℝ) ^ 4 := le_self_pow₀ hdR (by decide : 4 ≠ 0)
  apply le_trans _ (sharpRate_lower hn hD)
  calc
    (d : ℝ) * Real.sqrt d = (d : ℝ) * Real.sqrt d * 1 := by ring
    _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n := by gcongr
private theorem sourceLog_horizon_le {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    Real.log (n : ℝ) ≤ Real.log ((n : ℝ) * D) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact Real.log_le_log hnpos (by nlinarith)
private theorem sqrt_horizon_log_le_sharpRate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) : Real.sqrt ((n : ℝ) * Real.log n) ≤ sharpRate d D n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd := Real.one_le_sqrt.2 hdR
  have hp : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hdR
  have ht := sourceLog_lower hn hD
  have hlog := sourceLog_horizon_le hn hD
  have hs := Real.sqrt_le_sqrt hlog
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [sharpRate_eq_max hd (by linarith : 0 ≤ Real.log ((n : ℝ) * D))]
  apply le_trans _ (le_max_left _ _)
  calc
    Real.sqrt (n : ℝ) * Real.sqrt (Real.log n) =
        1 * 1 * Real.sqrt n * (1 * Real.sqrt (Real.log n)) := by ring
    _ ≤ _ := by gcongr
private theorem sharp_sample_expression_le_rate {d n : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    Real.sqrt n *
        ((d : ℝ) ^ 3 * Real.sqrt d * parameterLog d D n ^ 2 +
          (d : ℝ) ^ 4 * Real.sqrt d * parameterLog d D n *
            Real.sqrt (parameterLog d D n)) ≤
      346112 * sharpRate d D n := by
  let t := Real.log ((n : ℝ) * D)
  let L := parameterLog d D n
  have ht : 1 ≤ t := sourceLog_lower hn hD
  have hL : 1 ≤ L := (parameterLog_bounds d n (by linarith : 0 ≤ D)).1
  have hlog : L ≤ 416 * t := parameterLog_le_sourceLog hdn hn hD
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hs : Real.sqrt L ≤ 416 * Real.sqrt t := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 416 * Real.sqrt t)).2
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ t)]
  have hsq : L ^ 2 ≤ (416 * t) ^ 2 := by gcongr
  have heq := sharpRate_eq_max (n := n) hd (by dsimp [t] at ht; linarith : 0 ≤ Real.log ((n : ℝ) * D))
  have hfirst : (d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t ^ 2 ≤ sharpRate d D n := by
    rw [heq]
    exact le_max_right _ _
  have hsecond : (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t * Real.sqrt t) ≤
      sharpRate d D n := by
    rw [heq]
    exact le_max_left _ _
  calc
    _ ≤ Real.sqrt n *
        ((d : ℝ) ^ 3 * Real.sqrt d * (416 * t) ^ 2 +
          (d : ℝ) ^ 4 * Real.sqrt d * (416 * t) * (416 * Real.sqrt t)) := by
      change Real.sqrt n * ((d : ℝ) ^ 3 * Real.sqrt d * L ^ 2 +
        (d : ℝ) ^ 4 * Real.sqrt d * L * Real.sqrt L) ≤ _
      gcongr
    _ = 173056 * ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t ^ 2) +
        173056 * ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t * Real.sqrt t)) := by ring
    _ ≤ _ := by linarith
end LG2021
end
end
/- LG2021SharpRateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
/-- Each positive factor of the confidence base has logarithm at most the
confidence parameter. -/
private theorem log_le_parameterLog {d n : ℕ} {D x : ℝ} (hD : 0 ≤ D)
    (hx : 0 < x) (hxb : x ≤ parameterBase d D n) :
    Real.log x ≤ parameterLog d D n := by
  have hb := (parameterBase_bounds d n hD).1
  have hl : 0 ≤ Real.log (parameterBase d D n) :=
    Real.log_nonneg (by linarith)
  have hxlog := Real.log_le_log hx hxb
  unfold parameterLog
  linarith
private theorem parameterLog_ge_log_dim {d n : ℕ} (hd : 0 < d) {D : ℝ} (hD : 0 ≤ D) :
    Real.log (d : ℝ) ≤ parameterLog d D n := by
  apply log_le_parameterLog hD (by exact_mod_cast hd)
  linarith [(parameterBase_bounds d n hD).2.1]
private theorem parameterLog_ge_log_horizon {d n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) :
    Real.log (n : ℝ) ≤ parameterLog d D n := by
  apply log_le_parameterLog hD (by exact_mod_cast hn)
  linarith [(parameterBase_bounds d n hD).2.2.2.1]
private theorem parameterLog_ge_log_diameter {d n : ℕ} {D : ℝ} (hD : 0 < D) :
    Real.log D ≤ parameterLog d D n := by
  apply log_le_parameterLog hD.le hD
  linarith [(parameterBase_bounds d n hD.le).2.2.1]
/-- Squaring the Gaussian radius preserves its single logarithmic factor. -/
private theorem paperRadius_sq_sharp (d : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    paperRadius d L ^ 2 = 20000000000 * (d : ℝ) ^ 4 * L := by
  unfold paperRadius
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * L)]
  ring
/-- Explicit oracle scaling with separate logarithmic orders for its scalar
and gradient terms. -/
private theorem oracle_scale_sharp_le {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    max ((oracleMomentConstant / paperLambda d L + 1) ^ 2)
      ((oracleMomentConstant * paperRadius d L) ^ 2) ≤
      (10^24 : ℝ) * ((d : ℝ)^2 * L^2 + (d : ℝ)^4 * L) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdL : 1 ≤ (d : ℝ) * L := by nlinarith
  have hfirst : oracleMomentConstant / paperLambda d L + 1 ≤
      400000000001 * (d : ℝ) * L := by
    unfold oracleMomentConstant paperLambda
    rw [div_eq_mul_inv, one_div, inv_inv]
    nlinarith
  have hfirst0 : 0 ≤ oracleMomentConstant / paperLambda d L + 1 := by
    have hl := (paperLambda_bounds hd hL).1
    unfold oracleMomentConstant
    positivity
  have hfirstsq := (sq_le_sq₀ hfirst0 (by positivity :
      0 ≤ 400000000001 * (d : ℝ) * L)).2 hfirst
  have hsecond : (oracleMomentConstant * paperRadius d L)^2 =
      20000000000000000000000 * (d : ℝ)^4 * L := by
    rw [mul_pow, paperRadius_sq_sharp d (by linarith)]
    norm_num [oracleMomentConstant]
    ring
  apply max_le
  · nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg L),
      mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ d) 4) (by linarith : 0 ≤ L)]
  · rw [hsecond]
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg L),
      mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ d) 4) (by linarith : 0 ≤ L)]
/-- Sample complexity with explicit dimension and logarithmic dependence. -/
private theorem sampleBudget_le_sharp {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    sampleBudget (oracleConfig d D n) (candidateCount n) ≤
      (10^42 : ℝ) * ((d : ℝ)^2 * parameterLog d D n ^3 +
        (d : ℝ)^4 * parameterLog d D n ^2) := by
  let L := parameterLog d D n
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hscale := oracle_scale_sharp_le hd hL
  have hH := (confidenceLog_candidateCount_le (oracleConfig d D n) hn rfl).trans
    (mul_le_mul_of_nonneg_left
      (parameterLog_ge_log_horizon (d := d) (by omega : 0 < n) hD) (by norm_num : (0 : ℝ) ≤ 875))
  have hscale0 : 0 ≤ (10^24 : ℝ) * ((d : ℝ)^2 * L^2 + (d : ℝ)^4 * L) := by positivity
  have hH0 : 0 ≤ confidenceLog (oracleConfig d D n) (candidateCount n) := by
    linarith [(oracleConfig_bounds hd hn hD).2.2.2.2.2.2]
  calc
    _ ≤ 64 * ((10^24 : ℝ) * ((d : ℝ)^2 * L^2 + (d : ℝ)^4 * L)) *
        (875 * L) / oracleConcentrationConstant := by
      unfold sampleBudget oracleConfig
      gcongr
      all_goals first | exact hscale | exact hH | exact hH0 | norm_num [oracleConcentrationConstant]
    _ ≤ _ := by
      norm_num [oracleConcentrationConstant]
      nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (pow_nonneg (by linarith : 0 ≤ L) 3),
        mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ d) 4) (sq_nonneg L)]
private theorem separationFactor_sq_sharp (d : ℕ) :
    separationFactor d ^2 = 16777216 * (d : ℝ)^3 := by
  unfold separationFactor
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring
/-- The cost coefficient of one stage, before the final square root. -/
private theorem stageSampleBudget_le_sharp {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    4 * separationFactor d ^2 * sampleBudget (oracleConfig d D n) (candidateCount n) + 1 ≤
      (10^50 : ℝ) * ((d : ℝ)^5 * parameterLog d D n ^3 +
        (d : ℝ)^7 * parameterLog d D n ^2) := by
  let L := parameterLog d D n
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hb := mul_le_mul_of_nonneg_left (sampleBudget_le_sharp hd hn hD)
    (show 0 ≤ 4 * separationFactor d ^2 by positivity)
  rw [separationFactor_sq_sharp] at hb
  have hone : 1 ≤ (d : ℝ)^5 * L^3 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hdR) (one_le_pow₀ hL)
  have hsecond : 0 ≤ (d : ℝ)^7 * L^2 := by positivity
  change 4 * (16777216 * (d : ℝ)^3) * sampleBudget (oracleConfig d D n) (candidateCount n) ≤
    4 * (16777216 * (d : ℝ)^3) * ((10^42 : ℝ) * ((d : ℝ)^2 * L^3 + (d : ℝ)^4 * L^2)) at hb
  change _ ≤ (10^50 : ℝ) * ((d : ℝ)^5 * L^3 + (d : ℝ)^7 * L^2)
  rw [separationFactor_sq_sharp]
  nlinarith
/-- Square-root summation of the sample and stage bounds, retaining both
terms in the original dimension-dependent rate. -/
private theorem sqrt_stage_budget_le_sharp {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D j : ℝ} (hD : 0 ≤ D) (hj : 0 ≤ j)
    (hjbound : j ≤ 129 * (d : ℝ)^2 * parameterLog d D n) :
    Real.sqrt (4 * separationFactor d ^2 *
      sampleBudget (oracleConfig d D n) (candidateCount n) + 1) *
      Real.sqrt ((n : ℝ) * j) ≤
      (10^30 : ℝ) * Real.sqrt n *
        ((d : ℝ)^3 * Real.sqrt (d : ℝ) * parameterLog d D n ^2 +
          (d : ℝ)^4 * Real.sqrt (d : ℝ) * parameterLog d D n *
            Real.sqrt (parameterLog d D n)) := by
  let L := parameterLog d D n
  let a := 4 * separationFactor d ^2 *
    sampleBudget (oracleConfig d D n) (candidateCount n) + 1
  let X := (d : ℝ)^3 * Real.sqrt (d : ℝ) * L^2
  let Y := (d : ℝ)^4 * Real.sqrt (d : ℝ) * L * Real.sqrt L
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hL0 : 0 ≤ L := by linarith
  have hH0 : 0 ≤ confidenceLog (oracleConfig d D n) (candidateCount n) := by
    linarith [(oracleConfig_bounds hd hn hD).2.2.2.2.2.2]
  have hC0 : 0 < (oracleConfig d D n).concentrationConstant := oracleConcentrationConstant_pos
  have ha : 0 ≤ a := by
    dsimp only [a]
    unfold sampleBudget
    positivity
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXsq : X^2 = (d : ℝ)^7 * L^4 := by
    dsimp [X]
    calc
      _ = (d : ℝ)^6 * (Real.sqrt (d : ℝ))^2 * L^4 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]; ring
  have hYsq : Y^2 = (d : ℝ)^9 * L^3 := by
    dsimp [Y]
    calc
      _ = (d : ℝ)^8 * (Real.sqrt (d : ℝ))^2 * L^2 * (Real.sqrt L)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt hL0]; ring
  have hsum : (d : ℝ)^7 * L^4 + (d : ℝ)^9 * L^3 ≤ (X + Y)^2 := by
    rw [← hXsq, ← hYsq]
    nlinarith [mul_nonneg hX hY]
  have hprod : a * j ≤ (10^60 : ℝ) * (X + Y)^2 := by
    calc
      _ ≤ ((10^50 : ℝ) * ((d : ℝ)^5 * L^3 + (d : ℝ)^7 * L^2)) *
          (129 * (d : ℝ)^2 * L) := by
        apply mul_le_mul (stageSampleBudget_le_sharp hd hn hD) hjbound hj
        positivity
      _ = (129 * 10^50 : ℝ) * ((d : ℝ)^7 * L^4 + (d : ℝ)^9 * L^3) := by ring
      _ ≤ (129 * 10^50 : ℝ) * (X + Y)^2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (X + Y)]
  have hroot : Real.sqrt (a * j) ≤ (10^30 : ℝ) * (X + Y) := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ (10^30 : ℝ) * (X + Y))).2
    nlinarith
  change Real.sqrt a * Real.sqrt ((n : ℝ) * j) ≤
    (10^30 : ℝ) * Real.sqrt n * (X + Y)
  calc
    _ = Real.sqrt n * Real.sqrt (a * j) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_mul ha]
      ring
    _ ≤ Real.sqrt n * ((10^30 : ℝ) * (X + Y)) :=
      mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
    _ = _ := by ring
end LG2021.Algorithm
end
end
section
namespace LG2021.Algorithm
private theorem sliceRadius_sq : sliceRadius^2 = 3 / 4 :=
  Real.sq_sqrt (by norm_num)
end LG2021.Algorithm
end
/- LG2021SharpStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
private theorem abs_log_sliceRadius_le_one : |Real.log sliceRadius| ≤ 1 := by
  have hs0 := sliceRadius_pos
  have hslow : (1 / 2 : ℝ) ≤ sliceRadius := by
    have hs := sliceRadius_sq
    nlinarith
  have hshi : sliceRadius ≤ 1 := by
    have hs := sliceRadius_sq
    nlinarith
  have hneg : Real.log sliceRadius ≤ 0 := Real.log_nonpos hs0.le hshi
  rw [abs_of_nonpos hneg]
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hslow
  rw [Real.log_div (by norm_num) (by norm_num)] at hlo
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlo
  linarith
/-- The simplex-volume logarithmic penalty is linear in dimension times the
confidence parameter. -/
private theorem simplexLogPenalty_le_sharp {d n : ℕ} (hd : 0 < d) {D : ℝ} (hD : 0 ≤ D) :
    simplexLogPenalty d ≤ 4 * (d : ℝ) * parameterLog d D n := by
  let L := parameterLog d D n
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hlogd : Real.log (d : ℝ) ≤ L := parameterLog_ge_log_dim hd hD
  have hfpos : (0 : ℝ) < d.factorial := by positivity
  have hfone : (1 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hfac : (d.factorial : ℝ) ≤ (d : ℝ)^d := by exact_mod_cast Nat.factorial_le_pow d
  have hfaclog := Real.log_le_log hfpos hfac
  rw [Real.log_pow] at hfaclog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htwon : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hfacnonneg : 0 ≤ Real.log (2 * (d.factorial : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hmain : |Real.log (2 * (d.factorial : ℝ))| ≤ 1 + (d : ℝ) * L := by
    rw [abs_of_nonneg hfacnonneg, Real.log_mul (by norm_num) hfpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left hlogd (by positivity : (0 : ℝ) ≤ d)]
  have hlast : ((d - 1 : ℕ) : ℝ) * |Real.log sliceRadius| ≤ (d : ℝ) := by
    have hpred : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 1
    calc
      _ ≤ ((d - 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left abs_log_sliceRadius_le_one (by positivity)
      _ ≤ _ := by simp only [mul_one]; exact hpred
  have hmiddle : (d : ℝ) * |Real.log 2| ≤ (d : ℝ) := by
    rw [abs_of_nonneg htwon]
    nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : (0 : ℝ) ≤ d)]
  unfold simplexLogPenalty
  change _ ≤ 4 * (d : ℝ) * L
  nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ d)]
/-- Sharp dimension order of the source's simplex-volume stage bound. -/
private theorem source_volume_stage_bound_le_sharp {d n : ℕ} (hd : 0 < d)
    {R D : ℝ} (hR : 0 < R) (hRD : R ≤ D) :
    8 * ((d : ℝ) + 1) * ((d : ℝ) * Real.log R -
      Real.log (sourceSimplexVolume d D (parameterLog d D n) / (2 : ℝ)^d)) ≤
        128 * (d : ℝ)^2 * parameterLog d D n := by
  let L := parameterLog d D n
  have hD := hR.trans_le hRD
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := (parameterLog_bounds d n hD.le).1
  have hlogD : Real.log D ≤ L := parameterLog_ge_log_diameter hD
  have hlogR : Real.log R ≤ L := (Real.log_le_log hR hRD).trans hlogD
  have hvol := sourceSimplexVolume_log_lower d hD L
  have hpen : simplexLogPenalty d ≤ 4 * (d : ℝ) * L := simplexLogPenalty_le_sharp hd hD.le
  have hinner : (d : ℝ) * Real.log R -
      Real.log (sourceSimplexVolume d D L / (2 : ℝ)^d) ≤ 7 * (d : ℝ) * L := by
    nlinarith [mul_le_mul_of_nonneg_left hlogD (by positivity : (0 : ℝ) ≤ d),
      mul_le_mul_of_nonneg_left hlogR (by positivity : (0 : ℝ) ≤ d)]
  calc
    _ ≤ 8 * ((d : ℝ) + 1) * (7 * (d : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ _ := by
      change _ ≤ 128 * (d : ℝ)^2 * L
      nlinarith [mul_nonneg (by linarith : 0 ≤ (d : ℝ) - 1)
        (show 0 ≤ (d : ℝ) * L by positivity)]
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
private theorem cumLoss_congr_on {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) {K : Set X} (hA : A.IsOn K)
    {g h : X → ℝ≥0∞} (heq : EqOn g h K) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν g ω m τ y = cumLoss A ν h ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, heq (hA τ ω y)]
      congr 1
      exact lintegral_congr fun z => ih (τ + 1) (Fin.snoc y z)
private theorem expectedCumLoss_congr_on {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) {K : Set X}
    (hA : A.IsOn K) {g h : X → ℝ≥0∞} (heq : EqOn g h K) (n : ℕ) :
    expectedCumLoss A P ν g n = expectedCumLoss A P ν h n :=
  lintegral_congr fun ω => cumLoss_congr_on A ν hA heq ω n 0 Fin.elim0
private theorem unitNoiseCond_congr_on {X : Type} {K : Set X} {L F : X → ℝ}
    (heq : EqOn F L K) {ν : ObsKernel X} (hν : UnitNoiseCond K L ν) :
    UnitNoiseCond K F ν := by
  intro τ xs ys x hxs hx
  simpa only [heq hx] using hν τ xs ys x hxs hx
/-- The local Lipschitz loss is extended only in the analysis. Neither the
extension nor the unknown loss is supplied when the policy is chosen. -/
private theorem sharp_lipschitz_bandit_of_canonical {C : ℝ}
    (hcanonical : SharpCanonicalBandit C) {d : ℕ} (hd : 0 < d)
    {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hinner : closedBall 0 1 ⊆ K) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ K L → LipschitzOnWith 1 L K →
          (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
            UnitNoiseCond K L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * sharpRate d D n) := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    hcanonical d hd n hn D hD K hK hcv hinner hdiam
  letI := mΩ
  refine ⟨Ω, mΩ, P, hP, A, hA, ?_⟩
  intro L hLv hLl hLr ν hνm hν
  have hne : K.Nonempty := ⟨0, hinner (by simp)⟩
  let F := convexLipschitzExtension K 1 L
  have heq : EqOn F L K := convexLipschitzExtension_agrees hK hne 1 L hLl
  have hFc : ConvexOn ℝ univ F :=
    convexLipschitzExtension_convex hK hne 1 L hLl.continuousOn hLv
  have hFl : LipschitzWith 1 F :=
    convexLipschitzExtension_lipschitz hK hne 1 L hLl.continuousOn
  have hFn : ∀ x, 0 ≤ F x :=
    convexLipschitzExtension_nonneg hK hne 1 L hLl.continuousOn
      (fun x hx => (hLr x hx).1)
  have hFr : ∀ x ∈ K, F x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    rw [heq hx]
    exact hLr x hx
  have himage : F '' K = L '' K := Set.image_congr heq
  have hb := hregret F hFc hFl hFn hFr ν hνm (unitNoiseCond_congr_on heq hν)
  rw [expectedCumLoss_congr_on A P ν hA (g := fun x => ENNReal.ofReal (L x - sInf (L '' K)))
    (h := fun x => ENNReal.ofReal (F x - sInf (F '' K))) (by
      intro x hx
      dsimp only
      rw [heq hx, himage]) n]
  exact hb
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
private theorem two_le_diameter_of_unitBall {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    {a : EuclideanSpace ℝ (Fin d)} (hinner : closedBall a 1 ⊆ K) :
    2 ≤ Metric.diam K := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hball := Metric.diam_closedBall_eq a (by norm_num : (0 : ℝ) ≤ 1)
  have hm := Metric.diam_mono hinner hK.isBounded
  simpa only [hball, mul_one] using hm
/-- Theorem 2 transport with the original explicit dimension and diameter rate.
The unit ball can have any center, and the Lipschitz condition is local to `K`. -/
private theorem theorem_2_of_canonical {C : ℝ} (hcanonical : SharpCanonicalBandit C)
    {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hball : ∃ a, closedBall a 1 ⊆ K) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
        ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
          ConvexOn ℝ K L → LipschitzOnWith 1 L K →
          (∀ x ∈ K, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
            UnitNoiseCond K L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by
  obtain ⟨a, ha⟩ := hball
  let R : Set (EuclideanSpace ℝ (Fin d)) := (fun x => a + x) ⁻¹' K
  let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin d)) a).toAffineMap
  have hf : Continuous f := by change Continuous (fun x => a + x); fun_prop
  have hR : IsCompact R := (Homeomorph.addLeft a).isCompact_preimage.2 hK
  have hRc : Convex ℝ R := hcv.translate_preimage_right a
  have hRi : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ R := by
    intro x hx
    apply ha
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
  have himage : f '' R = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨x - a, ?_, ?_⟩ <;> simpa [R, f, add_comm a, sub_add_cancel] using hx
  have hmap : MapsTo f R K := fun _ hx => hx
  have hD : 2 ≤ Metric.diam K := two_le_diameter_of_unitBall hd hK ha
  have hRd : ∀ x ∈ R, ∀ y ∈ R, dist x y ≤ Metric.diam K := by
    intro x hx y hy
    have h := Metric.dist_le_diam_of_mem hK.isBounded hx hy
    simpa only [dist_add_left] using h
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    sharp_lipschitz_bandit_of_canonical hcanonical hd hn hD R hR hRc hRi hRd
  letI := mΩ
  refine ⟨Ω, mΩ, P, hP, mapQuery f hf.measurable A,
    mapQuery_isOn f hf.measurable A hA hmap, ?_⟩
  intro L hLv hLl hLr ν hνm hν
  have hcompv : ConvexOn ℝ R (L ∘ f) := (hLv.comp_affineMap f).subset hmap hRc
  have hcompl : LipschitzOnWith 1 (L ∘ f) R := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hLl.dist_le_mul (f x) (hmap hx) (f y) (hmap hy)
    simpa only [Function.comp_apply, f, AffineEquiv.coe_toAffineMap,
      AffineEquiv.constVAdd_apply, vadd_eq_add, dist_add_left] using h
  have hcompr : ∀ x ∈ R, (L ∘ f) x ∈ Icc (0 : ℝ) 1 := fun x hx => hLr _ (hmap hx)
  have hb := hregret (L ∘ f) hcompv hcompl hcompr (pullKernel f ν)
    (pullKernel_measurable f hf.measurable ν hνm) (pullKernel_unitNoiseCond f ν hmap L hν)
  rw [expectedRegret_mapQuery f hf.measurable himage L]
  exact hb
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
private theorem sharpPathBound_plus_failure_le_rate {d n : ℕ} (hd : 0 < d)
    (hdn : d ≤ n) (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    sharpPathBound d D n + 100 * ((d : ℝ) + 2) ≤
      (10^60 : ℝ) * sharpRate d D n := by
  have hD0 : 0 ≤ D := by linarith
  have hj : 0 ≤ 129 * (d : ℝ)^2 * parameterLog d D n := by
    have hL := (parameterLog_bounds d n hD0).1
    positivity
  have hs := sqrt_stage_budget_le_sharp hd hn hD0 hj le_rfl
  have he := sharp_sample_expression_le_rate hd hdn hn hD
  have hm := sqrt_horizon_log_le_sharpRate hd hn hD
  have hk := dimension_sqrt_le_sharpRate hd hn hD
  have hdim := dimension_le_sharpRate hd hn hD
  have hone := one_le_sharpRate hd hn hD
  have hs' : Real.sqrt (4 * separationFactor d ^2 *
      sampleBudget (oracleConfig d D n) (candidateCount n) + 1) *
      Real.sqrt ((n : ℝ) * (129 * (d : ℝ)^2 * parameterLog d D n)) ≤
      (10^30 : ℝ) * 346112 * sharpRate d D n := by
    calc
      _ ≤ _ := hs
      _ ≤ _ := by nlinarith
  unfold sharpPathBound separationFactor
  unfold separationFactor at hs'
  nlinarith
/-- Convert the simultaneous event for the concrete policy into its explicit
expected regret bound. -/
private theorem sharp_expected_regret_of_good_event {d n : ℕ} (hd : 0 < d)
    (hdn : d ≤ n) (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D)
    {K : Set (Space d)} (hK : IsCompact K) (R : ℝ)
    {anchor : Space d} (ha : anchor ∈ K)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f)
    (hrange : ∀ x ∈ K, f x ∈ Icc (0 : ℝ) 1)
    {xstar : Space d} (hxstar : xstar ∈ K) (hmin : ∀ x ∈ K, f xstar ≤ f x)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (hν : UnitNoiseCond K f ν)
    {G : Set (Seed d (candidateCount n) n × (Fin n → ℝ))} (hG : MeasurableSet G)
    (hgood : ∀ w ∈ G,
      realPathLoss (policy (u := candidateCount n) (oracleConfig d D n) K
        hK.isClosed.measurableSet R anchor) f w - (n : ℝ) * f xstar ≤ sharpPathBound d D n)
    (hbad : (historyMeasure
      (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm n).real Gᶜ ≤
        100 * ((d : ℝ) + 2) / (n : ℝ)) :
    expectedCumLoss (policy (u := candidateCount n) (oracleConfig d D n) K
      hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν
      (fun x => ENNReal.ofReal (f x - sInf (f '' K))) n ≤
        ENNReal.ofReal ((10^60 : ℝ) * sharpRate d D n) := by
  let cfg := oracleConfig d D n
  let A : QueryAlg (Space d) (Seed d (candidateCount n) n) :=
    policy (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor
  let P : Measure (Seed d (candidateCount n) n) := seedMeasure d (candidateCount n) cfg
  letI : IsProbabilityMeasure P := seedMeasure_probability d (candidateCount n) cfg
  have hA : A.IsOn K := policy_isOn cfg K hK.isClosed.measurableSet R ha
  have hleast : IsLeast (f '' K) (f xstar) := by
    refine ⟨⟨xstar, hxstar, rfl⟩, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hmin x hx
  rw [hleast.csInf_eq]
  have hg (τ : ℕ) : Measurable (fun w : Seed d (candidateCount n) n × (Fin τ → ℝ) =>
      ENNReal.ofReal (f (A.query τ w.1 w.2) - f xstar)) :=
    ((hf.continuous.measurable.comp (A.query_measurable τ)).sub_const _).ennreal_ofReal
  have hunit : ∀ x ∈ K, ENNReal.ofReal (f x - f xstar) ≤ 1 := by
    intro x hx
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith [(hrange x hx).2, (hrange xstar hxstar).1]
  have hgood' : ∀ w ∈ G, pathCost A (fun x => ENNReal.ofReal (f x - f xstar)) w ≤
      ENNReal.ofReal (sharpPathBound d D n) := by
    intro w hw
    rw [pathCost_regret_eq_ofReal A hA f (f xstar) hmin]
    exact ENNReal.ofReal_le_ofReal (hgood w hw)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh := expectedCost_le_of_path_good A P ν hνm hA f 1
    (unitNoiseCond_noiseCond K f ν hν) (fun x => ENNReal.ofReal (f x - f xstar))
    hg hunit n hG (sharpPathBound_nonneg d D n)
    (by positivity : 0 ≤ 100 * ((d : ℝ) + 2) / (n : ℝ)) hgood' hbad
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hcancel : (n : ℝ) * (100 * ((d : ℝ) + 2) / (n : ℝ)) = 100 * ((d : ℝ) + 2) := by
    field_simp
  rw [hcancel]
  exact sharpPathBound_plus_failure_le_rate hd hdn hn hD
/-- The concrete canonical policy, with one universal constant and the
explicit dimension dependence of the convex-bandit rate. -/
private theorem sharp_canonical_bandit : SharpCanonicalBandit (10^60 : ℝ) := by
  intro d hd n hn D hD K hK hcv hball hdiam
  let cfg := oracleConfig d D n
  let A : QueryAlg (Space d) (Seed d (candidateCount n) n) :=
    policy (u := candidateCount n) cfg K hK.isClosed.measurableSet D 0
  let P : Measure (Seed d (candidateCount n) n) := seedMeasure d (candidateCount n) cfg
  have h0 : (0 : Space d) ∈ K := hball (by simp)
  have hA : A.IsOn K := policy_isOn cfg K hK.isClosed.measurableSet D h0
  refine ⟨Seed d (candidateCount n) n, inferInstance, P,
    seedMeasure_probability d (candidateCount n) cfg, A, hA, ?_⟩
  intro f hconv hf _hnonneg hrange ν hνm hν
  obtain ⟨xstar, hxstar, hmin⟩ := hK.exists_isMinOn ⟨0, h0⟩ hf.continuous.continuousOn
  by_cases hdn : d ≤ n
  · have hD0 : 0 ≤ D := by linarith
    have hDp : 0 < D := by linarith
    have hbounded : ∀ x ∈ K, ‖x‖ ≤ D := by
      intro x hx
      simpa using hdiam x hx 0 h0
    obtain ⟨v, _, hv0, hv, hnear, hvol⟩ := exists_source_analysis_simplex hd (by omega : 1 ≤ n)
      hcv hball (by linarith : 1 ≤ D) hdiam hxstar f hf
    obtain ⟨G, hG, hbad, hgood⟩ := exists_terminal_good_event hd hn hD0 hK hcv hdiam D 0 h0
      f hf hconv hrange xstar hxstar v ν hνm hν
    have hpath : ∀ w ∈ G,
        realPathLoss (policy (u := candidateCount n) cfg K hK.isClosed.measurableSet D 0) f w -
          (n : ℝ) * f xstar ≤ sharpPathBound d D n := by
      intro w hw
      have hg := hgood w hw
      apply terminal_regret_of_current_bounds_sharp hd hn hK hcv hDp le_rfl hbounded hdiam
        w.1 (terminalPairs w.2) f hf hconv xstar hmin v hv0 hv hnear hvol (by omega : n / 2 ≤ n)
      · intro p _ s
        exact hg.candidate_norm p s
      · exact hg.scalar
      · exact hg.gradient
      · exact hg.candidate_hit
      · exact hg.path_regret
      · exact source_volume_stage_bound_le_sharp hd hDp le_rfl
    exact sharp_expected_regret_of_good_event hd hdn hn hD hK D h0 f hf hrange hxstar hmin
      ν hνm hν hG hpath hbad
  · letI : IsProbabilityMeasure P := seedMeasure_probability d (candidateCount n) cfg
    have hleast : IsLeast (f '' K) (f xstar) := by
      refine ⟨⟨xstar, hxstar, rfl⟩, ?_⟩
      rintro z ⟨x, hx, rfl⟩
      exact hmin hx
    rw [hleast.csInf_eq]
    have hg (τ : ℕ) : Measurable (fun w : Seed d (candidateCount n) n × (Fin τ → ℝ) =>
        ENNReal.ofReal (f (A.query τ w.1 w.2) - f xstar)) :=
      ((hf.continuous.measurable.comp (A.query_measurable τ)).sub_const _).ennreal_ofReal
    have hunit : ∀ x ∈ K, ENNReal.ofReal (f x - f xstar) ≤ 1 := by
      intro x hx
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      linarith [(hrange x hx).2, (hrange xstar hxstar).1]
    have hh := expectedCost_le_of_path_good A P ν hνm hA f 1
      (unitNoiseCond_noiseCond K f ν hν) (fun x => ENNReal.ofReal (f x - f xstar)) hg hunit n
      MeasurableSet.univ (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (by norm_num : (0 : ℝ) ≤ 0)
      (fun w _ => by simpa using pathCost_le_horizon A hA _ hunit w)
      (by simp : (historyMeasure A P ν hνm n).real univᶜ ≤ (0 : ℝ))
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have htriv := trivial_horizon_le_sharpRate hd hn (by omega : n ≤ d) hD
    have hrate := sharpRate_nonneg (d := d) hn hD
    nlinarith
end LG2021
end
end
open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
/-- The explicit universal regret bound for one-Lipschitz convex losses on a
known compact convex body containing a unit ball. -/
theorem LG2021.theorem_2 : ∃ C : ℝ, 0 ≤ C ∧
∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → LipschitzOnWith 1 L K →
            (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by
  refine ⟨10^60, by positivity, ?_⟩
  intro d hd n hn K hK hcv hball
  exact LG2021.theorem_2_of_canonical LG2021.sharp_canonical_bandit hd hn K hK hcv hball

theorem solution : ∃ C : ℝ, 0 ≤ C ∧
∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → LipschitzOnWith 1 L K →
            (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by
  exact LG2021.theorem_2
