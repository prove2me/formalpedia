-- Prove2me | solution 1 for LG2021.Concentration.estimatorGood_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:48:11.835266+00:00
-- url     : https://prove2.me/submissions/4616b728-2be7-4d61-a69d-eabf00943550

import Definitions.Def_LG2021_Policy
import Theorems.Thm_LG2021_Concentration_measure_gradientStageFailure_le
import Theorems.Thm_LG2021_Concentration_measure_scalarStageFailure_le
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





private theorem estimator_union_budget {d n u N : ℕ} (hn : 0 < n) (hu : 0 < u) (hN : N ≤ n) :
    ((N+1 : ℕ) : ℝ)^2 * u * (2 * Real.exp (-Real.log (3*(u : ℝ)*(n : ℝ)^3))) +
      ((N+1 : ℕ) : ℝ)^2 * u * (d+1) * (2 * Real.exp (-Real.log (3*(u : ℝ)*(n : ℝ)^3))) ≤
        3 * (d+2) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNN : ((N+1 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by
    have hNr : (N : ℝ) ≤ n := by exact_mod_cast hN
    push_cast
    linarith
  have hs : ((N+1 : ℕ) : ℝ)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ (d : ℝ)+2 by positivity)
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 3*(u : ℝ)*(n : ℝ)^3)]
  apply (le_div_iff₀ hnR).2
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hm (show 0 ≤ (u : ℝ) by positivity)]



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



open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory

theorem solution {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n) (hu : 0 < u)
    {D : ℝ} (hD : 0 ≤ D) (K : Set (Space d)) (hK : MeasurableSet K)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hN : N ≤ n) (v : Fin (d+1) → Space d) :
    (historyMeasure (policy (u := u) (oracleConfig d D n) K hK R anchor)
      (seedMeasure d u (oracleConfig d D n)) ν hνm (2*N)).real
      (estimatorGood (oracleConfig d D n) K hK R anchor ν hνm N v)ᶜ ≤ 3 * (d+2) / (n : ℝ) := by
  let cfg := oracleConfig d D n
  have hnoise := CorollaryTransport.unitNoiseCond_noiseCond K F ν hν
  letI := historyMeasure_probability (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg)
    ν hνm (policy_isOn (u := u) cfg K hK R ha) F 1 hnoise (2*N)
  have hl := paperLambda_bounds hd (parameterLog_bounds d n hD).1
  have hH : 0 ≤ confidenceLog cfg u := by
    apply Real.log_nonneg
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    change 1 ≤ 3*(u : ℝ)*(n : ℝ)^3
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn1 3]
  have hs := measure_scalarStageFailure_le (u := u) cfg K hK R anchor ha ν hνm F hν hF
    hl.1 hl.2.1 hl.2.2 N (by dsimp [cfg, oracleConfig]; omega) (confidenceLog cfg u) hH
  have hg := measure_gradientStageFailure_le (u := u) cfg K hK R anchor ha ν hνm F hν hF
    hl.1 hl.2.1 hl.2.2 N (by dsimp [cfg, oracleConfig]; omega) (confidenceLog cfg u) hH v
  unfold estimatorGood
  rw [Set.compl_inter, compl_compl, compl_compl]
  exact (measureReal_union_le _ _).trans ((add_le_add hs hg).trans (estimator_union_budget hn hu hN))
