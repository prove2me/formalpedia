-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:22:49.017463+00:00
-- url     : https://prove2.me/submissions/dc32070c-1d24-4a94-bc8a-c220b08c697f

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_angular_tailPrime_hecke_group
import Theorems.Thm_OAI_CubicFirstMoment_angular_tailPrime_middle_group
import Theorems.Thm_OAI_CubicFirstMoment_localized_integral_power_saving

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

/-- The complete smoothed series has the exact Mellin representation on
any line of absolute convergence of its norm Dirichlet series. -/
theorem smooth_mellin_series {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    (habs : Summable (fun i => ‖a i‖*(N i)^(-σ)))
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries a N (σ+(τ:ℂ)*Complex.I) := by
  let s (τ : ℝ) : ℂ := σ+(τ:ℂ)*Complex.I
  let F (i : ι) (τ : ℝ) : ℂ :=
    (a i*(N i:ℂ)^(-s τ))*((Z:ℂ)^(s τ)*mellin W (s τ))
  have hsre (τ : ℝ) : (s τ).re = σ := by simp [s]
  have hsnre (τ : ℝ) : (-s τ).re = -σ := by simp [hsre]
  have hnorm (i : ι) (τ : ℝ) : ‖F i τ‖ =
      (‖a i‖*(N i)^(-σ))*Z^σ*‖mellin W (s τ)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,hsre,hsnre]
    ring
  have hm : Integrable (fun τ => mellin W (s τ)) :=
    smooth_mellin_vertical_integrable W hW hpos hsm σ
  have hFi (i : ι) : Integrable (F i) := by
    have hn0 : (N i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN i).ne'
    have hz0 : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have : NeZero (N i:ℂ) := ⟨hn0⟩
    have : NeZero (Z:ℂ) := ⟨hz0⟩
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hc : Continuous (F i) :=
      (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hs.neg)).mul
        (((differentiable_const_cpow_of_neZero _).continuous.comp hs).mul
          ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs))
    exact (hm.norm.const_mul ((‖a i‖*(N i)^(-σ))*Z^σ)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => (hnorm i τ).le))
  have hsum : Summable (fun i => ∫ τ : ℝ, ‖F i τ‖) := by
    have he (i : ι) : (∫ τ : ℝ, ‖F i τ‖) =
        (‖a i‖*(N i)^(-σ))*(Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖)) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖))
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (i : ι) : a i*W (N i/Z) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := by
    rw [← smooth_mellin_inversion W hW hpos hsm σ (div_pos (hN i) hZ),mellinInv]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc,mul_comm (a i),mul_assoc,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with τ
    rw [mellin_scale_cpow (hN i) hZ]
    dsimp [F,s]
    ring
  calc
    _ = ∑' i, ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := tsum_congr hsingle
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∑' i, ∫ τ : ℝ, F i τ) := tsum_mul_left
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, ∑' i, F i τ) := by rw [hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      simp only [F,normDirichletSeries]
      rw [tsum_mul_right]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

theorem normTwist_mul (u : ℝ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normTwist u (a * b) = normTwist u a * normTwist u b := by
  have han : norm a ≠ 0 := (norm_eq_zero_iff.not.mpr ha)
  have hbn : norm b ≠ 0 := (norm_eq_zero_iff.not.mpr hb)
  have hn : norm (a * b) = norm a * norm b := Complex.normSq_mul _ _
  simp only [normTwist, hn, Real.log_mul han hbn, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weights and Mellin twists

The derivative cost below explains why the unweighted published Hecke
estimate continues to give any prescribed logarithmic saving after a
fixed-logarithmic-height norm twist. It is used with `weighted_cubic_prime_bound`.
-/

noncomputable section

namespace CubicFirstMoment

theorem normTwist_eq_mellinPhase (u : ℝ) (a : Eisenstein) :
    normTwist u a = mellinPhase u (norm a) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DualPolynomialScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma mellinPhase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    mellinPhase t x = (x:ℂ)^((t:ℂ)*Complex.I) := by
  simpa only [Complex.ofReal_zero,zero_add,Real.rpow_zero,Complex.ofReal_one,one_mul]
    using (positive_cpow_phase hx 0 t).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic saving furnished by corrected Cauchy--Schwarz. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bilinear_error_log_saving {x : ℂ} {M K A L z E V : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z)
    (k d : ℕ) (_hE : 0 ≤ E) (hV : 0 ≤ V)
    (herror : ‖x‖^2 ≤ E*V) (henergy : E ≤ M*A*z^d)
    (hmass : V ≤ K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) :
    ‖x‖ ≤ Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hsqA : (A^(5/6:ℝ))^2 = A^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (A^(5/6:ℝ)) 2,←Real.rpow_mul hA.le]
    norm_num
  have hsqL : (L^(5/6:ℝ))^2 = L^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (L^(5/6:ℝ)) 2,←Real.rpow_mul hL.le]
    norm_num
  have hAadd : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one A]
    rw [←Real.rpow_add hA]
    norm_num
  have hid : (Real.sqrt (M*K)*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      (M*A*z^d)*(K*A^(2/3:ℝ)*L^(5/3:ℝ)/z^(2*k+d)) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hM hK),hsqA,hsqL,
      pow_add,pow_mul]
    field_simp
    simp only [←pow_mul]
    rw [Nat.mul_comm 2 k,←hAadd]
    ring
  have hb := herror.trans (mul_le_mul henergy hmass hV (by positivity))
  rw [←hid] at hb
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem frequencyCutoff_apply (x : ℝ) : frequencyCutoff x = (frequencyBump x : ℂ) := rfl

theorem frequencyCutoff_one {x : ℝ} (hx : |x| ≤ 1/2) : frequencyCutoff x = 1 := by
  rw [frequencyCutoff_apply, frequencyBump.one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, frequencyBump] using hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The interval Fourier multiplier

Evaluation of the interval transform gives the two endpoint terms divided
by frequency. The value at zero is the interval length, so there is no
singularity in the original multiplier.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

theorem fourier_intervalStep_eq_integral {a b : ℝ} (hab : a ≤ b) (ξ : ℝ) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      ∫ x in a..b, Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) •
      (intervalStep a b x : ℂ)) = (Set.Icc a b).indicator
        (fun x => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, hx, ite_true, if_true, ite_false, if_false,
        Complex.ofReal_one, Complex.ofReal_zero, smul_eq_mul, mul_one, mul_zero]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem fourier_intervalStep_nonzero {a b ξ : ℝ} (hab : a ≤ b) (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep a b x : ℂ)) ξ =
      (Complex.exp ((-2 * Real.pi * b * ξ : ℝ) * Complex.I) -
        Complex.exp ((-2 * Real.pi * a * ξ : ℝ) * Complex.I)) /
          ((-2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_eq_integral hab]
  have hc : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero) hξ
  have he : (fun x : ℝ => Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I * x)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- The multiplier for the dyadic interval [1,2], at every nonzero frequency. -/
theorem dyadic_interval_multiplier {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ =
      (1 - Complex.exp ((-2 * Real.pi * Real.log 2 * ξ : ℝ) * Complex.I)) /
        ((2 * Real.pi * ξ : ℝ) * Complex.I) := by
  rw [fourier_intervalStep_nonzero (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hξ]
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  have hneg : ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I =
      -(((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [hneg]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for a bounded number of ordered prime factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every prime in another tuple with the same product occurs in the
reference tuple. This includes repeated primes. -/
lemma prime_tuple_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hprod : (∏ i, g i) = ∏ i, f i) (i : ι) :
    g i ∈ Finset.univ.image f := by
  have hd : g i ∣ ∏ j, f j := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
  have he : g i = f j := primary_associated_eq (hg i).1 (hf j).1
    (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩

/-- The deliberately generous `k^k` bound avoids ordering conventions and
is uniform in the norm and in all independent supports. -/
theorem prime_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    have hfs := (Finset.mem_filter.mp hf).1
    have hfb := (Finset.mem_filter.mp hf).2
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact prime_tuple_range_subset f g hprime
        (fun i => hS i (g i) ((Fintype.mem_piFinset.mp hgs) i)) (hgb.trans hfb.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by
        simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))) _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- The coefficient bound depends only on the number of prime factors
and on their separate weight bounds, including for nonsquarefree products. -/
theorem orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b)) hprod

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothNormPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit finite smooth partition on every bounded positive norm range.
Its fixed weight is supported in `[1,2]`, as required by the smooth
short-factor estimates. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma normPartitionWeight_norm (x : ℝ) : ‖normPartitionWeight x‖ ≤ 1 := by
  by_cases hx : x < 1
  · rw [normPartitionWeight_low hx,norm_zero]
    norm_num
  have hmono : normPartitionStep (3*x/4) ≤ normPartitionStep x :=
    Real.smoothTransition.monotone (by linarith)
  have hnonneg := Real.smoothTransition.nonneg (3*(3*x/4-1))
  have hone := Real.smoothTransition.le_one (3*(x-1))
  rw [normPartitionWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hmono)]
  dsimp [normPartitionStep] at *
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin separation of a finite product-norm weight. This is the
exact analytic bridge used after the smooth short-convolution partition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smooth_mellin_finite {κ : Type*} [Fintype κ]
    (a : κ → ℂ) (N : κ → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    (∑ i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        (∑ i, a i*(N i:ℂ)^(-(σ+(τ:ℂ)*Complex.I))) := by
  simpa only [normDirichletSeries,tsum_fintype] using
    smooth_mellin_series a N hN W hW hpos hsm σ (hasSum_fintype _).summable hZ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinWeight_norm (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    ‖zeroLineMellinWeight V Z τ‖ =
      (1/(2*Real.pi))*‖mellin V ((τ:ℂ)*Complex.I)‖ := by
  rw [zeroLineMellinWeight,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_self,Real.rpow_zero,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi))]

theorem zeroLineMellinWeight_integrable (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (zeroLineMellinWeight V Z) := by
  have hm : Integrable (fun τ : ℝ => mellin V ((τ:ℂ)*Complex.I)) := by
    have h := smooth_mellin_vertical_integrable V hV hpos hsm 0
    change Integrable (fun τ : ℝ => mellin V ((0:ℂ)+(τ:ℂ)*Complex.I)) at h
    simpa only [zero_add] using h
  have hz : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hp : Continuous (fun τ : ℝ => (Z:ℂ)^((τ:ℂ)*Complex.I)) :=
    (differentiable_const_cpow_of_neZero _).continuous.comp (by fun_prop)
  have ha : AEStronglyMeasurable (zeroLineMellinWeight V Z) :=
    ((hm.aestronglyMeasurable.const_mul _).mul hp.aestronglyMeasurable)
  exact (hm.norm.const_mul (1/(2*Real.pi))).mono' ha
    (Filter.Eventually.of_forall (fun τ => (zeroLineMellinWeight_norm V hZ τ).le))

lemma zeroLineMellinWeight_mass (V : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    (∫ τ : ℝ, ‖zeroLineMellinWeight V Z τ‖) = zeroLineMellinMass V := by
  simp_rw [zeroLineMellinWeight_norm V hZ]
  exact integral_const_mul _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite realization of the literal prime convolution: each coordinate
contains every primary prime on which its independent weight is nonzero. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_mem_iff {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hhi : ∀ i x, R < x → W i x = 0) (i : ι) (p : Eisenstein) :
    p ∈ fullPrimeSupport R W X i ↔ primaryPrime p ∧ W i (norm p/X i) ≠ 0 := by
  simp only [fullPrimeSupport,Finset.mem_filter,mem_primaryElementBall]
  constructor
  · rintro ⟨⟨⟨hp,_⟩,hw⟩,hq⟩
    exact ⟨⟨hp,hq⟩,hw⟩
  · rintro ⟨⟨hp,hq⟩,hw⟩
    have hn : norm p/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
    exact ⟨⟨⟨hp,(div_le_iff₀ (hX i)).mp hn⟩,hw⟩,hq⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedScalePowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_const_mul_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C*Y^a ≤ Y^b := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with Y hY hC
  calc
    _ ≤ Y^(b-a)*Y^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary published mean-value theorem applied to the literal
prime convolution, with every numerator and excluded-prime factor retained. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_prime (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primaryPrime z := by
  intro i z hz
  exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1,
    (Finset.mem_filter.mp hz).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBilinearMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the actual varying outer weights in a
finite bilinear Gauss sum. All integrability follows from smooth support. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplectic_mellin_term_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (_hx : 0 < x) (a : ℂ) :
    Integrable (fun t : ℝ => zeroLineMellinWeight W V t*(a*mellinPhase (-t) x)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hV).mul_bdd
    (c := ‖a‖)
  · have hc : Continuous (fun t : ℝ => a*mellinPhase (-t) x) := by
      unfold mellinPhase
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with t
    simp [mellinPhase,Complex.norm_exp]

lemma metaplectic_mellin_term (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (hx : 0 < x) (a : ℂ) :
    a*W (x/V) = ∫ t : ℝ, zeroLineMellinWeight W V t*(a*mellinPhase (-t) x) := by
  have h := smooth_mellin_finite (fun _ : Unit => a) (fun _ : Unit => x)
    (fun _ => hx) W hW hpos hsm 0 hV
  simp only [Fintype.sum_unique,Complex.ofReal_zero,zero_add] at h
  rw [h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [mellinPhase_eq_cpow hx]
  have he : ((-t:ℝ):ℂ)*Complex.I = -((t:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullSquarefreePrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) {b : Eisenstein} (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
    primary b ∧ Squarefree b := by
  have hm := Finset.mem_filter.mp hb
  exact ⟨orderedPrimarySupport_primary _ (fun i b hb => (fullPrimeSupport_prime R W X i b hb).1) hm.1,hm.2.1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed log-norm range for an unchanged prime convolution is derived
from its coordinate supports. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeProduct_norm_bounds (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport (fullPrimeSupport R W X)) :
    (∏ i, X i) ≤ norm b ∧ norm b ≤ R^(Fintype.card ι)*(∏ i, X i) := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  have hbound (i : ι) : X i ≤ norm (f i) ∧ norm (f i) ≤ R*X i := by
    have hmem := Fintype.mem_piFinset.mp hf i
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i (f i)).mp hmem).2
    constructor
    · have hn : 1 ≤ norm (f i)/X i := le_of_not_gt (fun h => hw (hlo i _ h))
      simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hn
    · have hn : norm (f i)/X i ≤ R := le_of_not_gt (fun h => hw (hhi i _ h))
      exact (div_le_iff₀ (hX i)).mp hn
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod (fun i _ => (hX i).le) (fun i _ => (hbound i).1)
  · calc
      _ ≤ ∏ i, R*X i := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (hbound i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeMellinEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial coarse envelope for the unchanged full prime rows,
uniform in Mellin height and the ambient set of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeSupport_card_bound {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤ 18*(R^Fintype.card ι*(∏ i, X i)) := by
  apply primary_support_card_le _ (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => (hX i).le)))
  intro b hb
  exact ⟨(fullSquarefreePrimeSupport_primary R W X e hb).1,
    (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient support for divisor-restricted prime coefficients.
No independent-prime condition is asserted for the shortened coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeCoefficient_norm_bound (R : ℝ) (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (b : Eisenstein) :
    ‖fullPrimeCoefficient R W X b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simpa only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_left hs] using
      orderedConvolution_norm_bound (fullPrimeSupport R W X)
        (fun i n => W i (norm n/X i)) M
        (fun i p hp => fullPrimeSupport_prime R W X i p hp) hM
        (fun i p _ => hW i _) b
  · simp only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_right hs,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular Gauss product and its coefficient-mass bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma theta_coefficient_energy (ℓ : ℤ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (hS : ∀ b ∈ S, primary b) :
    (∑ b ∈ S, ‖theta ℓ b*α b‖^2) = ∑ b ∈ S, ‖α b‖^2 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [norm_theta_mul (primary_ne_zero (hS b hb))]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionSavingPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomially bounded exclusion remains negligible compared with
a rough prime coordinate, with every prescribed logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma exclusion_log_absorption {c d ε : ℝ} (hε : 0 < ε) (hgap : d*ε < c)
    {C : ℝ} (hC : 0 ≤ C) (m k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y E : ℝ, 0 ≤ E → E ≤ L^d → L^c ≤ Y →
      C*E^ε*(1+Real.log L)^m ≤ Y/(1+Real.log L)^k := by
  let s := (c-d*ε)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hexp : d*ε+s < c := by dsimp [s]; linarith
  obtain ⟨K,hK,hlog⟩ := log_power_normalization_bound (m+k) hs
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_const_mul_rpow_le hexp (C*K)]
    with L hL hbound
  intro Y E hE hEd hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  have hlog' : (1+Real.log L)^(m+k) ≤ K*L^s := by
    calc
      _ = L^s*(L^(-s)*(1+Real.log L)^(m+k)) := by
        rw [← mul_assoc,← Real.rpow_add hLp]
        simp
      _ ≤ L^s*K := mul_le_mul_of_nonneg_left (hlog L hL) (Real.rpow_nonneg hLp.le _)
      _ = _ := mul_comm _ _
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    _ = C*E^ε*(1+Real.log L)^(m+k) := by rw [pow_add]; ring
    _ ≤ C*(L^d)^ε*(K*L^s) := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEd hε.le) hC) hlog'
      (pow_nonneg hz.le _) (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _))
    _ = (C*K)*L^(d*ε+s) := by
      rw [← Real.rpow_mul hLp.le,Real.rpow_add hLp]
      ring
    _ ≤ L^c := hbound
    _ ≤ Y := hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyads with the strict lower endpoint used by stopped rows.
The partition is finite and its count depends only on the norm envelope. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedNormDyad_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hnorm : 2 ≤ norm n) :
    stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  have hN : 2 ≤ normNat n := by exact_mod_cast (show (2:ℝ) ≤ (normNat n:ℝ) by
    simpa only [normNat_cast] using hnorm)
  have hne : normNat n-1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hne
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat n-1)
  have hj := (Finset.mem_filter.mp hn).2
  change Nat.log 2 (normNat n-1) = j at hj
  rw [hj] at hlo hhi
  have hl : (2:ℕ)^j < normNat n := by omega
  have hu : normNat n ≤ (2:ℕ)^(j+1) := by omega
  have hlr : (2:ℝ)^j < norm n := by
    rw [←normNat_cast]
    exact_mod_cast hl
  have hur : norm n ≤ (2:ℝ)^(j+1) := by
    rw [←normNat_cast]
    exact_mod_cast hu
  unfold stoppedNormDyadLength
  rw [pow_succ]
  constructor
  · nlinarith
  · simpa only [pow_succ] using hur

lemma stoppedNormDyad_outer_bounds {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hn : n ∈ stoppedNormDyad S j) (hp : primary n) :
    stoppedNormDyadLength j/2 ≤ norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  by_cases htwo : 2 ≤ norm n
  · have hh := stoppedNormDyad_bounds hn htwo
    exact ⟨hh.1.le,hh.2⟩
  · have hone : 1 ≤ norm n := one_le_norm (primary_ne_zero hp)
    have hN : normNat n = 1 := by
      have hl : 1 ≤ normNat n := by exact_mod_cast (show (1:ℝ) ≤ (normNat n:ℝ) by
        simpa only [normNat_cast] using hone)
      have hu : normNat n < 2 := by exact_mod_cast (show (normNat n:ℝ) < 2 by
        simpa only [normNat_cast] using lt_of_not_ge htwo)
      omega
    have hj : j = 0 := by
      have he := (Finset.mem_filter.mp hn).2
      simpa only [stoppedNormDyadIndex,hN,Nat.sub_self,Nat.log_zero_right] using he.symm
    subst j
    simp only [stoppedNormDyadLength,zero_add,pow_one,div_self (by norm_num : (2:ℝ) ≠ 0)]
    rw [←normNat_cast,hN]
    norm_num

lemma stoppedNormDyad_partition (S : Finset Eisenstein) (f : Eisenstein → ℂ) :
    (∑ n ∈ S, f n) = ∑ j ∈ S.image stoppedNormDyadIndex,
      ∑ n ∈ stoppedNormDyad S j, f n := by
  unfold stoppedNormDyad
  exact (Finset.sum_fiberwise_of_maps_to (s := S)
    (t := S.image stoppedNormDyadIndex) (g := stoppedNormDyadIndex)
    (fun n hn => Finset.mem_image_of_mem _ hn) f).symm

lemma stoppedNormDyad_count (S : Finset Eisenstein) {Y : ℝ}
    (hS : ∀ n ∈ S, norm n ≤ Y) :
    (S.image stoppedNormDyadIndex).card ≤ Nat.log 2 ⌊Y⌋₊+1 := by
  apply le_trans (Finset.card_le_card (show S.image stoppedNormDyadIndex ⊆
    Finset.range (Nat.log 2 ⌊Y⌋₊+1) from ?_)) (by rw [Finset.card_range])
  intro j hj
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.log_mono_right
  exact (Nat.sub_le _ _).trans (Nat.le_floor (by simpa only [normNat_cast] using hS n hn))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightIntegrationByParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact twofold integration by parts for the actual height exponential. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace CubicFirstMoment

lemma heightFourierIntegral_eq (h : ℝ → ℂ) (ℓ : ℝ) :
    heightFourierIntegral h ℓ = ∫ t : ℝ, h t*Complex.exp ((ℓ*t:ℝ)*Complex.I) := by
  rw [heightFourierIntegral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have he : -2*Real.pi*t*(-ℓ/(2*Real.pi)) = ℓ*t := by
    field_simp
  rw [he,smul_eq_mul,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightPolynomialIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interchange between finite height Fourier coefficients and the
actual norm polynomial. No frequency truncation is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma integrable_height_phase (h : ℝ → ℂ) (hi : Integrable h) (ℓ : ℝ) :
    Integrable (fun t : ℝ => h t*Complex.exp ((ℓ*t:ℝ)*Complex.I)) := by
  apply hi.mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ*t:ℝ)*Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun _ => by simp [Complex.norm_exp])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightWindow_norm_le (T t : ℝ) : ‖heightWindow T t‖ ≤ 1 := by
  rw [heightWindow, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [heightPartitionBump.nonneg (x := t/((3/2)*T)),
    heightPartitionBump.le_one (x := t/((3/2)*T)),
    heightPartitionBump.nonneg (x := t/T), heightPartitionBump.le_one (x := t/T)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite height partition. Every nonzero window lies below
the Fourier cap, and the number of windows costs only one logarithm. -/
noncomputable section
namespace CubicFirstMoment

lemma heightWindowCount_scale_bounds {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    {j : ℕ} (hj : j < heightWindowCount S T) :
    T ≤ T*(3/2:ℝ)^j ∧ T*(3/2:ℝ)^j < 2*Real.pi*S := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hj' : (j:ℝ) < Real.log ((2*Real.pi*S)/T)/Real.log (3/2:ℝ) := Nat.lt_ceil.mp hj
  have hlog : Real.log ((3/2:ℝ)^j) < Real.log ((2*Real.pi*S)/T) := by
    rw [Real.log_pow]
    exact (lt_div_iff₀ hr).mp hj'
  have hb := (Real.log_lt_log_iff (by positivity : 0 < (3/2:ℝ)^j)
    (div_pos (by positivity) hT)).mp hlog
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hT.le
  · simpa only [mul_comm] using (lt_div_iff₀ hT).mp hb

theorem heightWindowCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 1 ≤ S → 1 ≤ T →
      (heightWindowCount S T:ℝ) ≤ K*(1+Real.log S) := by
  let r := Real.log (3/2:ℝ)
  let a := 1+Real.log (2*Real.pi)/r
  let b := 1/r
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hc : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have ha : 0 ≤ a := by
    have hc' := Real.log_nonneg hc
    dsimp [a]
    positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b, by linarith, ?_⟩
  intro S T hS hT
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hcap : 1 ≤ 2*Real.pi*S := by nlinarith
  have hmono : heightWindowCount S T ≤ ⌈Real.log (2*Real.pi*S)/r⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hr.le
    rw [Real.log_div (by positivity : 2*Real.pi*S ≠ 0) hTp.ne']
    linarith [Real.log_nonneg hT]
  have hceil := (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hcap) hr.le)).le
  have hstart := (Nat.cast_le.mpr hmono).trans hceil
  rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hSp.ne', add_div] at hstart
  have he : Real.log (2*Real.pi)/r+Real.log S/r+1 = a+b*Real.log S := by
    dsimp [a,b]
    ring
  apply hstart.trans
  rw [he]
  nlinarith [mul_nonneg ha hlogS]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightWindowSum
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual finite ratio-3/2 height windows costs one logarithm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem height_window_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H T E : ℝ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 0 ≤ E →
      (∀ t, T ≤ t → t < 2*Real.pi*H → ‖f t‖ ≤ E) →
      ‖∑ j ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^j)‖ ≤
        K*(1+Real.log H)*E := by
  obtain ⟨K,hK,hcount⟩ := heightWindowCount_log_bound
  refine ⟨K,hK,?_⟩
  intro H T E f hH hT hE hf
  calc
    _ ≤ ∑ j ∈ Finset.range (heightWindowCount H T), ‖f (T*(3/2:ℝ)^j)‖ :=
      norm_sum_le _ _
    _ ≤ (heightWindowCount H T:ℝ)*E := by
      have hb (j : ℕ) (hj : j ∈ Finset.range (heightWindowCount H T)) :
          ‖f (T*(3/2:ℝ)^j)‖ ≤ E := by
        have hs := heightWindowCount_scale_bounds (zero_lt_one.trans_le hH)
          (zero_lt_one.trans_le hT) (Finset.mem_range.mp hj)
        exact hf _ hs.1 hs.2
      simpa using Finset.sum_le_sum hb
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcount H T hH hT) hE

theorem height_window_sum_log_saving :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (H T Z B K : ℝ) (j : ℕ) (f : ℝ → ℂ),
      1 ≤ H → 1 ≤ T → 1 ≤ Z → H ≤ Z^3 → 0 ≤ B → 0 ≤ K →
      (∀ t, T ≤ t → t < 2*Real.pi*H →
        ‖f t‖ ≤ K*B/(1+Real.log Z)^(j+1)) →
      ‖∑ i ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^i)‖ ≤
        K₀*K*B/(1+Real.log Z)^j := by
  obtain ⟨K₀,hK₀,hbound⟩ := height_window_sum_bound
  refine ⟨3*K₀,by positivity,?_⟩
  intro H T Z B K j f hH hT hZ hHZ hB hK hf
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  have hlog : 1+Real.log H ≤ 3*(1+Real.log Z) := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hH) hHZ
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  apply (hbound H T (K*B/(1+Real.log Z)^(j+1)) f hH hT (by positivity) hf).trans
  calc
    _ ≤ K₀*(3*(1+Real.log Z))*(K*B/(1+Real.log Z)^(j+1)) := by gcongr
    _ = (3*K₀)*K*B/(1+Real.log Z)^j := by
      rw [pow_succ]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoordinateWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform joint Mellin moments from the actual common support and derivative
bounds of the coordinate weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMass_nonneg (W : ℝ → ℂ) : 0 ≤ zeroLineMellinMass W := by
  unfold zeroLineMellinMass
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoreBlockMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One logarithmic saving on every actual core dyad above the small
core cutoff, obtained by joining the ordinary and exceptional estimates. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma negative_power_log_saving {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, L^(-ν) ≤ 1/(1+Real.log L)^k := by
  have h := exclusion_log_absorption (c := ν) (d := 0) (ε := 1)
    (by norm_num) (by simpa using hν) (C := 1) (by norm_num) k 0
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L h hL
  have hp := h (L^ν) 1 (by norm_num) (by simp) le_rfl
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hp
  have hz : 0 < (1+Real.log L)^k := pow_pos (by linarith [Real.log_nonneg hL]) _
  rw [Real.rpow_neg (zero_le_one.trans hL),← one_div]
  exact one_div_le_one_div_of_le hz hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBLogScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit outer-length and logarithmic losses for the small-B
variance. Only positive real powers and the proved logarithm bound occur. -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_nondiagonal_log_scale {A Z L H δ : ℝ}
    (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L) (k d : ℕ)
    (hbound : Z^(-δ)*L^(k+d) ≤ H) :
    A^(2/3:ℝ)*Z^(5/3-δ)*L^d ≤ H*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  apply (le_div_iff₀ (pow_pos hL k)).mpr
  have hz : Z^(5/3-δ) = Z^(5/3:ℝ)*Z^(-δ) := by
    rw [← Real.rpow_add hZ]
    congr 1
  rw [hz]
  have hh := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ A^(2/3:ℝ)*Z^(5/3:ℝ) by positivity)
  rw [pow_add] at hh
  nlinarith only [hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LocalizedLogSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic savings for the actual localized height integral. The
coefficient energies may have any fixed logarithmic losses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma localized_root_log_saving {A Z γ K Mα Mβ H : ℝ}
    (hA : 0 < A) (hZ : 1 ≤ Z) (hK : 0 ≤ K) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hH : 0 ≤ H) (j dα dβ : ℕ)
    (hlog : Z^(-(2*γ/3))*(1+Real.log Z)^(2*j+dα+dβ) ≤ H)
    {Ea Eb : ℝ} (ha : 0 ≤ Ea) (hb : 0 ≤ Eb)
    (hea : Ea ≤ Mα*A*(1+Real.log Z)^dα)
    (heb : Eb ≤ Mβ*Z*(1+Real.log Z)^dβ) :
    K*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*Real.sqrt Ea*Real.sqrt Eb ≤
      Real.sqrt (Mα*(K^2*Mβ*H))*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  let L := 1+Real.log Z
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hZ]
  let Q := A^(2/3:ℝ)*Z^(2/3-2*γ/3)
  let R := K*Real.sqrt Q*Real.sqrt Ea*Real.sqrt Eb
  let V := K^2*Q*Eb
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsquare : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hQ,Real.sq_sqrt ha,Real.sq_sqrt hb]
    exact le_of_eq (by ring)
  have hz : Z^(2/3-2*γ/3)*Z = Z^(5/3-2*γ/3) := by
    nth_rw 2 [←Real.rpow_one Z]
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  have hmass : V ≤ (K^2*Mβ*H)*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    have hh := smallB_nondiagonal_log_scale hA.le hZp hL (2*j+dα) dβ hlog
    calc
      V ≤ K^2*Q*(Mβ*Z*L^dβ) := mul_le_mul_of_nonneg_left heb (by positivity)
      _ = (K^2*Mβ)*(A^(2/3:ℝ)*Z^(5/3-2*γ/3)*L^dβ) := by dsimp [Q]; rw [←hz]; ring
      _ ≤ (K^2*Mβ)*(H*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  have hh := bilinear_error_log_saving hMα (show 0 ≤ K^2*Mβ*H by positivity)
    hA hZp hL j dα ha hV hsquare hea hmass
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDetectorCutoff_nonneg (x : ℝ) : 0 ≤ primeDetectorCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma primeDetectorCutoff_le_one (x : ℝ) : primeDetectorCutoff x ≤ 1 := by
  unfold primeDetectorCutoff
  linarith [Real.smoothTransition.nonneg (x-1)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightMultiplier
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint phases of the actual cutoff. On each smooth height
window the normalized reciprocal factor is uniformly bounded. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma frequencyCutoff_norm_le (x : ℝ) : ‖frequencyCutoff x‖ ≤ 1 := by
  rw [frequencyCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

lemma cutoffHeightMultiplier_eq_endpoints (S : ℝ) {t : ℝ} (ht : t ≠ 0) :
    cutoffHeightMultiplier S t = frequencyCutoff ((t/(2*Real.pi))/S) *
      ((1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I))/((t:ℂ)*Complex.I)) := by
  rw [cutoffHeightMultiplier, dyadic_interval_multiplier
    (div_ne_zero ht (by positivity))]
  have he : -2*Real.pi*Real.log 2*(t/(2*Real.pi)) = -Real.log 2*t := by field_simp
  have hd : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  rw [he,hd]

lemma localizedEndpointWeight_norm_le {T : ℝ} (S : ℝ) (hT : 0 < T) (t : ℝ) :
    ‖localizedEndpointWeight S T t‖ ≤ 1 := by
  by_cases ht : t ∈ dyadicHeightSupport T
  · have habs : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    have hp : 0 < |t| := hT.trans_le habs
    rw [localizedEndpointWeight, norm_mul, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (T*1)/|t| * 1 := by
        gcongr
        · exact frequencyCutoff_norm_le _
        · exact heightWindow_norm_le _ _
      _ ≤ 1 := by simpa only [mul_one] using (div_le_one hp).mpr habs
  · rw [localizedEndpointWeight_zero S hT t ht, norm_zero]
    norm_num

lemma cutoffHeightMultiplier_window_endpoints {T : ℝ} (S : ℝ) (hT : 0 < T) (t : ℝ) :
    cutoffHeightMultiplier S t*heightWindow T t =
      (T:ℂ)⁻¹*localizedEndpointWeight S T t*
        (1-Complex.exp ((-Real.log 2*t : ℝ)*Complex.I)) := by
  by_cases ht : t = 0
  · subst t
    have hz : (0:ℝ) ∉ dyadicHeightSupport T := by
      simp only [dyadicHeightSupport, Set.mem_union, Set.mem_Icc, not_or]
      constructor <;> rintro ⟨ha,hb⟩ <;> linarith
    rw [heightWindow_zero hT hz, localizedEndpointWeight_zero S hT 0 hz]
    simp
  · rw [cutoffHeightMultiplier_eq_endpoints S ht, localizedEndpointWeight]
    have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness at the removable reciprocal singularity, compact support,
and the exact two-endpoint formula for a localized cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma localizedEndpointWeight_integrable (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (localizedEndpointWeight S T) :=
  (localizedEndpointWeight_smooth S hT).continuous.integrable_of_hasCompactSupport
    (localizedEndpointWeight_compact S hT)

lemma localizedEndpointWeight_derivatives (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (deriv (localizedEndpointWeight S T)) ∧
    Differentiable ℝ (deriv (localizedEndpointWeight S T)) ∧
    Integrable (deriv (deriv (localizedEndpointWeight S T))) := by
  have hd := (contDiff_infty_iff_deriv.mp (localizedEndpointWeight_smooth S hT)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := (localizedEndpointWeight_compact S hT).deriv
  exact ⟨hd.continuous.integrable_of_hasCompactSupport hc,
    hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hdd.continuous.integrable_of_hasCompactSupport hc.deriv⟩

lemma localizedEndpointWeight_second_zero (S : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ)
    (ht : t ∉ dyadicHeightSupport T) :
    deriv (deriv (localizedEndpointWeight S T)) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hh
  exact ht (localizedEndpointWeight_tsupport S hT (tsupport_deriv_subset hh))

lemma cutoff_window_fourier_endpoints (S : ℝ) {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t) ℓ =
      (T:ℂ)⁻¹*(heightFourierIntegral (localizedEndpointWeight S T) ℓ -
        heightFourierIntegral (localizedEndpointWeight S T) (ℓ-Real.log 2)) := by
  have hi := localizedEndpointWeight_integrable S hT
  simp only [heightFourierIntegral_eq]
  rw [← integral_sub (integrable_height_phase _ hi ℓ)
    (integrable_height_phase _ hi (ℓ-Real.log 2)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [cutoffHeightMultiplier_window_endpoints S hT t]
  have he : Complex.exp (((ℓ-Real.log 2)*t:ℝ)*Complex.I) =
      Complex.exp ((ℓ*t:ℝ)*Complex.I)*Complex.exp ((-Real.log 2*t:ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem bilinear_cutoff_window_endpoints (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (S : ℝ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t)
        (Real.log (norm (a*b))-Real.log X)) =
      heightBilinearValue P B α β (localizedEndpointWeight S T) X T -
        heightBilinearValue P B α β (localizedEndpointWeight S T) (2*X) T := by
  simp only [heightBilinearValue, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [cutoff_window_fourier_endpoints S hT,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']
  have he : Real.log (norm (a*b))-Real.log X-Real.log 2 =
      Real.log (norm (a*b))-(Real.log 2+Real.log X) := by ring
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma endpointProfile_eq (x : ℝ) :
    endpointProfile x = heightWindow 1 x/((x:ℂ)*Complex.I) := by
  change localizedEndpointWeight (2/Real.pi) 1 x = _
  by_cases hx : x ∈ dyadicHeightSupport 1
  · have hnorm : |x| ≤ 2 := by
      rcases hx with hx | hx
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have he : (x/(2*Real.pi))/(2/Real.pi) = x/4 := by field_simp; ring
    have hf : frequencyCutoff ((x/(2*Real.pi))/(2/Real.pi)) = 1 := by
      rw [he]
      apply frequencyCutoff_one
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith
    simp only [localizedEndpointWeight, hf, Complex.ofReal_one, one_mul]
    ring
  · rw [localizedEndpointWeight_zero _ (by norm_num) _ hx,
      heightWindow_zero (by norm_num) hx, zero_div]

lemma heightWindow_dilation {T : ℝ} (hT : 0 < T) (t : ℝ) :
    heightWindow T t = heightWindow 1 (t/T) := by
  have he : t/((3/2)*T) = (t/T)/((3/2)*1)  := by field_simp [hT.ne']
  simp only [heightWindow, he, mul_one, div_one]

lemma localizedEndpointWeight_dilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (t : ℝ) :
    localizedEndpointWeight S T t =
      frequencyCutoff ((T/(2*Real.pi*S))*(t/T))*endpointProfile (t/T) := by
  have hf : (T/(2*Real.pi*S))*(t/T) = (t/(2*Real.pi))/S := by field_simp
  rw [hf, endpointProfile_eq, ← heightWindow_dilation hT]
  unfold localizedEndpointWeight
  by_cases ht : t = 0
  · subst t
    simp
  · have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp

private lemma secondDerivativeBudget_pos (f : SchwartzMap ℝ ℂ) :
    0 < secondDerivativeBudget f := by
  have hs : 0 ≤ ∑ i ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 i f :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  dsimp [secondDerivativeBudget]
  linarith

private lemma norm_iteratedDeriv_le_budget (f : SchwartzMap ℝ ℂ) {i : ℕ}
    (hi : i ≤ 2) (x : ℝ) : ‖iteratedDeriv i f x‖ ≤ secondDerivativeBudget f := by
  have hb := SchwartzMap.le_seminorm' ℝ 0 i f x
  simp only [pow_zero, one_mul] at hb
  have hs : SchwartzMap.seminorm ℝ 0 i f ≤
      ∑ j ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 j f :=
    Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
  exact hb.trans (by dsimp [secondDerivativeBudget]; linarith)

/-- Only two derivatives are needed for the far-cell integration by parts. -/
lemma scaled_schwartz_product_second_bound (f g : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x : ℝ,
      ‖deriv (deriv (fun y => f (a*y)*g y)) x‖ ≤ K := by
  let A := secondDerivativeBudget f
  let B := secondDerivativeBudget g
  have hA : 0 < A := secondDerivativeBudget_pos f
  have hB : 0 < B := secondDerivativeBudget_pos g
  refine ⟨4*A*B, by positivity, ?_⟩
  intro a ha ha1 x
  have hf : ContDiff ℝ (2:ℕ) (fun y => f (a*y)) :=
    (f.smooth 2).comp (contDiff_const.mul contDiff_id)
  have he := iteratedDeriv_mul (n := 2) (x := x) hf.contDiffAt (g.smooth 2).contDiffAt
  have hb (i : ℕ) (hi : i ∈ Finset.range 3) :
      ‖((2:ℕ).choose i : ℂ)*iteratedDeriv i (fun y => f (a*y)) x*
          iteratedDeriv (2-i) g x‖ ≤ ((2:ℕ).choose i : ℝ)*A*B := by
    have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
    have hfi : ‖iteratedDeriv i (fun y => f (a*y)) x‖ ≤ A := by
      rw [iteratedDeriv_comp_const_smul (f.smooth i), norm_smul, Real.norm_eq_abs,
        abs_pow, abs_of_nonneg ha]
      apply (mul_le_mul (pow_le_one₀ ha ha1) (norm_iteratedDeriv_le_budget f hi2 (a*x))
        (_root_.norm_nonneg _) (by norm_num)).trans_eq
      exact one_mul _
    have hgi : ‖iteratedDeriv (2-i) g x‖ ≤ B :=
      norm_iteratedDeriv_le_budget g (by omega) x
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    gcongr
  have hsum := (norm_sum_le (Finset.range 3) _).trans (Finset.sum_le_sum hb)
  rw [← he] at hsum
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hsum
  norm_num [Finset.sum_range_succ] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem localizedEndpointWeight_second_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 0 < S → 0 < T → T ≤ 2*Real.pi*S →
      ∀ t : ℝ, ‖(T:ℂ)^2*deriv (deriv (localizedEndpointWeight S T)) t‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := scaled_schwartz_product_second_bound frequencyCutoff endpointProfile
  refine ⟨K,hK,?_⟩
  intro S T hS hT hTS t
  let a := T/(2*Real.pi*S)
  let q := fun x => frequencyCutoff (a*x)*endpointProfile x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).mpr hTS
  have hq : ContDiff ℝ (2:ℕ) q :=
    ((frequencyCutoff.smooth 2).comp (contDiff_const.mul contDiff_id)).mul
      (endpointProfile.smooth 2)
  have he : localizedEndpointWeight S T = fun x => q (T⁻¹*x) := by
    funext x
    simpa only [q,a,div_eq_mul_inv,mul_comm T⁻¹] using
      localizedEndpointWeight_dilation hS hT x
  have hd := congrFun (iteratedDeriv_comp_const_smul (n := 2) hq T⁻¹) t
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hd
  rw [he,hd,norm_mul,norm_pow,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hT,Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hT]
  calc
    T^2*(T⁻¹^2*‖deriv (deriv q) (T⁻¹*t)‖) = ‖deriv (deriv q) (T⁻¹*t)‖ := by field_simp
    _ ≤ K := hbound a ha ha1 (T⁻¹*t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation of the total-product envelope in a
finite height tail. No Mellin frequency is discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem envelopeCutoffBilinearTail_mellin (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X : ℝ} (hX : 0 < X) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∫ τ : ℝ, zeroLineMellinWeight W X τ*
        cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
          (fun b => β b*normTwist (-τ) b) H T X := by
  let c := fun j a b => α a*β b*gauss (a*b)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
      (Real.log (norm (a*b))-Real.log X)
  let f := fun j a b τ => zeroLineMellinWeight W X τ*
    (c j a b*mellinPhase (-τ) (norm (a*b)))
  have hn (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      0 < norm (a*b) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb)))
  have hi (j : ℕ) (a : Eisenstein) (ha : a ∈ P) (b : Eisenstein) (hb : b ∈ S) :
      Integrable (f j a b) :=
    metaplectic_mellin_term_integrable W hW hpos hsm hX (hn a ha b hb) (c j a b)
  calc
    _ = ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, ∫ τ : ℝ, f j a b τ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have he := metaplectic_mellin_term W hW hpos hsm hX (hn a ha b hb) (c j a b)
      simpa only [c,f,mul_assoc,mul_left_comm,mul_comm] using he
    _ = ∫ τ : ℝ, ∑ j ∈ Finset.range (heightWindowCount H T),
        ∑ a ∈ P, ∑ b ∈ S, f j a b τ := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum P
        (fun a ha => integrable_finsetSum S (hi j a ha)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum P (fun a ha => integrable_finsetSum S (hi j a ha))]
      apply Finset.sum_congr rfl
      intro a ha
      exact (integral_finsetSum S (hi j a ha)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [cutoffBilinearTail,cutoffBilinearWindow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [f,c]
      rw [←normTwist_eq_mellinPhase,normTwist_mul (-τ)
        (primary_ne_zero (hP a ha)) (primary_ne_zero (hS b hb))]
      ring

theorem envelopeCutoffBilinearTail_bound (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (H T : ℝ) {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hb : ∀ u : ℝ,
      ‖cutoffBilinearTail P S (fun a => α a*normTwist u a)
        (fun b => β b*normTwist u b) H T X‖ ≤ M) :
    ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤ zeroLineMellinMass W*M := by
  let F := fun τ : ℝ => cutoffBilinearTail P S (fun a => α a*normTwist (-τ) a)
    (fun b => β b*normTwist (-τ) b) H T X
  have hc : Continuous F := by
    unfold F cutoffBilinearTail cutoffBilinearWindow normTwist
    fun_prop
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hi : Integrable (fun τ => zeroLineMellinWeight W X τ*F τ) :=
    hw.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => hb (-τ)))
  rw [envelopeCutoffBilinearTail_mellin P S α β hP hS W hW hpos hsm H T hX]
  change ‖∫ τ : ℝ, zeroLineMellinWeight W X τ*F τ‖ ≤ _
  calc
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ*F τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖*M := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const M)
      filter_upwards with τ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (-τ)) (_root_.norm_nonneg _)
    _ = (∫ τ : ℝ, ‖zeroLineMellinWeight W X τ‖)*M := integral_mul_const _ _
    _ = _ := by rw [zeroLineMellinWeight_mass W hX]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dyadic decomposition of both coefficient supports in the original
product-envelope tail. The triangle inequality is applied only after this
finite identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma envelopeCutoffBilinearTail_dyads (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X : ℝ) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∑ r ∈ P.image stoppedNormDyadIndex, ∑ s ∈ S.image stoppedNormDyadIndex,
        envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
          α β W H T X := by
  unfold envelopeCutoffBilinearTail
  have hb (v : ℕ) (a : Eisenstein) := stoppedNormDyad_partition S
    (fun b => α a*β b*gauss (a*b)*W (norm (a*b)/X)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*
        heightWindow (T*(3/2:ℝ)^v) t) (Real.log (norm (a*b))-Real.log X))
  simp_rw [hb]
  conv_lhs =>
    arg 2
    ext v
    rw [stoppedNormDyad_partition P]
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]

lemma envelopeCutoffBilinearTail_dyads_bound (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X M : ℝ)
    (hb : ∀ r ∈ P.image stoppedNormDyadIndex, ∀ s ∈ S.image stoppedNormDyadIndex,
      ‖envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
        α β W H T X‖ ≤ M) :
    ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
      ((P.image stoppedNormDyadIndex).card:ℝ)*
        ((S.image stoppedNormDyadIndex).card:ℝ)*M := by
  rw [envelopeCutoffBilinearTail_dyads]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun r hr => (norm_sum_le _ _).trans
    (Finset.sum_le_sum (hb r hr)))).trans_eq
  simp [mul_assoc]

theorem stoppedNormDyad_count_power :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (Q A B : ℝ),
      1 ≤ Q → 1 ≤ A → 1 ≤ B → A ≤ B^3 →
      (∀ a ∈ P, norm a ≤ Q*A) →
      ((P.image stoppedNormDyadIndex).card:ℝ) ≤
        (3*C*(1+Real.log Q))*(1+Real.log B) := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  refine ⟨C,hC,?_⟩
  intro P Q A B hQ hA hB hAB hP
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hm : Nat.log 2 ⌊Q*A⌋₊+1 ≤ Nat.log 2 ⌊3*(Q*A)⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
  apply (Nat.cast_le.mpr ((stoppedNormDyad_count P hP).trans hm)).trans
  apply (hcount (Q*A) (one_le_mul_of_one_le_of_one_le hQ hA)).trans
  rw [Real.log_mul hQp.ne' hAp.ne']
  have hlog := Real.log_le_log hAp hAB
  rw [Real.log_pow] at hlog
  have hq := Real.log_nonneg hQ
  have hb := Real.log_nonneg hB
  have hmul : 0 ≤ Real.log Q*Real.log B := mul_nonneg hq hb
  have hh : 1+Real.log Q+Real.log A ≤ 3*(1+Real.log Q)*(1+Real.log B) := by
    norm_num at hlog
    nlinarith
  nlinarith only [mul_le_mul_of_nonneg_left hh hC.le]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformLocalizedSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the analytic power-width before any coefficient losses or
requested logarithmic savings. This order is needed to fix the stopping
parameters before the finite prime arity is known. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem localized_integral_log_saving_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ : ℝ), 0 ≤ Mα → 0 ≤ Mβ →
      ∀ (j dα dβ : ℕ),
    ∃ K Z₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := localized_integral_power_saving hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ hMα hMβ j dα dβ
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound (2*j+dα+dβ)
    (s := 2*γ/3) (by positivity)
  let K' := Real.sqrt (Mα*(K^2*Mβ*H))+1
  refine ⟨K',max Z₀ 65536,by dsimp [K']; positivity,?_⟩
  intro P S α β Z A X₀ T M hZ hA hAu hX hT hM hP hS hea heb h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hZ1 : 1 ≤ Z := by have := (le_max_right Z₀ 65536).trans hZ; linarith
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hLp : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  have hb := hbound P S α β Z A X₀ T M ((le_max_left _ _).trans hZ)
    hA hAu hX hT hM hP hS h hi hd hi' hd' hi'' hh hs hh2 hs2
  have hr := localized_root_log_saving hAp hZ1 hK.le hMα hMβ hH j dα dβ
    (hlog Z hZ1) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hea heb
  calc
    _ ≤ M*(K*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*
        Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)) := by
      convert hb using 1 <;> first | rfl | ring
    _ ≤ M*(Real.sqrt (Mα*(K^2*Mβ*H))*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) :=
      mul_le_mul_of_nonneg_left hr hM
    _ ≤ K'*M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
      dsimp [K']
      have hp : 0 ≤ M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by positivity
      calc
        _ = Real.sqrt (Mα*(K^2*Mβ*H))*(M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) := by ring
        _ ≤ (Real.sqrt (Mα*(K^2*Mβ*H))+1)*(M*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j) :=
          mul_le_mul_of_nonneg_right (by linarith) hp
        _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformHighTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single positive power width works for all coefficient energies and
logarithmic savings. The stopping parameter can therefore be fixed before
the finite prime arity, without a circular choice of constants. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem high_energy_cutoff_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ : ℝ), 0 ≤ Mα → 0 ≤ Mβ →
      ∀ (n dα dβ : ℕ), ∃ K Z₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^(2+γ) → 0 < X₀ →
      Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖cutoffBilinearTail P S α β H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Kh,hKh,hsecond⟩ := localizedEndpointWeight_second_uniform
  let Mh := 1+Kh
  have hMh : 0 ≤ Mh := by dsimp [Mh]; positivity
  obtain ⟨γ,hγ,huniform⟩ := localized_integral_log_saving_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ hMα hMβ n dα dβ
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform Mα Mβ hMα hMβ (n+1) dα dβ
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨K₀*(2*K*Mh),max Z₀ 1,by dsimp [Mh]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hHZ hP hS hea heb
  have hZ1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hT1 : 1 ≤ T := (Real.one_le_rpow hZ1 (by norm_num : (0:ℝ) ≤ 1/50)).trans hT
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖cutoffBilinearWindow P S α β H t X₀‖ ≤
        (2*K*Mh)*(A^(5/6:ℝ)*Z^(5/6:ℝ))/(1+Real.log Z)^(n+1) := by
    have htp : 0 < t := zero_lt_one.trans_le (hT1.trans ht)
    let w := localizedEndpointWeight H t
    have hi : Integrable w := localizedEndpointWeight_integrable H htp
    have hd : Differentiable ℝ w := (localizedEndpointWeight_smooth H htp).differentiable (by simp)
    have hder := localizedEndpointWeight_derivatives H htp
    have hw (u : ℝ) : ‖w u‖ ≤ Mh := (localizedEndpointWeight_norm_le H htp u).trans
      (by dsimp [Mh]; linarith)
    have hz (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : w u = 0 :=
      localizedEndpointWeight_zero H htp u hu
    have hw2 (u : ℝ) : ‖(t:ℂ)^2*deriv (deriv w) u‖ ≤ Mh :=
      (hsecond H t (zero_lt_one.trans_le hH) htp htH.le u).trans
        (by dsimp [Mh]; linarith)
    have hz2 (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : deriv (deriv w) u = 0 :=
      localizedEndpointWeight_second_zero H htp u hu
    have hb := hbound P S α β Z A X₀ t Mh ((le_max_left _ _).trans hZ) hA hAu hX (hT.trans ht) hMh
      hP hS hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    have hb2 := hbound P S α β Z A (2*X₀) t Mh ((le_max_left _ _).trans hZ) hA hAu (by positivity)
      (hT.trans ht) hMh hP hS hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    unfold cutoffBilinearWindow
    rw [bilinear_cutoff_window_endpoints P S α β H htp hX]
    exact (norm_sub_le _ _).trans ((add_le_add hb hb2).trans_eq (by ring))
  have hb := hsum H T Z (A^(5/6:ℝ)*Z^(5/6:ℝ)) (2*K*Mh) n
    (fun t => cutoffBilinearWindow P S α β H t X₀) hH hT1 hZ1 hHZ
    (by positivity) (by positivity) hf
  simpa only [cutoffBilinearTail,mul_assoc] using hb

theorem high_energy_envelope_cutoff_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ : ℝ), 0 ≤ Mα → 0 ≤ Mβ →
      ∀ (n dα dβ : ℕ) (W : ℝ → ℂ), HasCompactSupport W →
        tsupport W ⊆ Set.Ioi 0 → ContDiff ℝ ∞ W →
        ∃ K Z₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X T H : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X →
      Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_energy_cutoff_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ hMα hMβ n dα dβ W hW hpos hsm
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform Mα Mβ hMα hMβ n dα dβ
  have hmass := zeroLineMellinMass_nonneg W
  refine ⟨(zeroLineMellinMass W+1)*K,max Z₀ 1,by positivity,?_⟩
  intro P S α β Z A X T H hZ hA hAu hX hT hH hHZ hP hS hea heb
  have hZ1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hAp : 0 < A := (by positivity : 0 < 2*Z^(3/2:ℝ)).trans_le hA
  have hM : 0 ≤ K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
    have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
    positivity
  have hb := envelopeCutoffBilinearTail_bound P S α β
    (fun b hb => (hP b hb).1) (fun b hb => (hS b hb).1)
    W hW hpos hsm H T hX hM (fun u => by
      apply hbound P S (fun b => α b*normTwist u b)
        (fun b => β b*normTwist u b) Z A X T H ((le_max_left _ _).trans hZ) hA hAu hX hT hH hHZ hP hS
      · simpa only [norm_mul,norm_normTwist,mul_one] using hea
      · simpa only [norm_mul,norm_normTwist,mul_one] using heb)
  calc
    _ ≤ zeroLineMellinMass W*(K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n) := hb
    _ ≤ (zeroLineMellinMass W+1)*(K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n) :=
      mul_le_mul_of_nonneg_right (by linarith) hM
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HighWideTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-width support version of the uniform power-width tail. The same
positive exponent is chosen before all coefficient arities and energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem high_wide_envelope_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ D Q : ℝ),
      0 ≤ Mα → 0 ≤ Mβ → 1 ≤ D → 1 ≤ Q → ∀ (n dα dβ : ℕ)
      (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
      ContDiff ℝ ∞ W → ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (B A X T H : ℝ),
      B₀ ≤ B → 4*(2*D*B)^(3/2:ℝ) ≤ A →
      Q*A ≤ B^(2+γ) → A ≤ B^3 → 0 < X →
      (2*D*B)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ B^3 →
      (∀ x ∈ P, primary x ∧ A ≤ norm x ∧ norm x ≤ Q*A) →
      (∀ y ∈ S, primary y ∧ Squarefree y ∧ B ≤ norm y ∧ norm y ≤ D*B) →
      (∑ x ∈ P, ‖α x‖^2) ≤ Mα*A*(1+Real.log B)^dα →
      (∑ y ∈ S, ‖β y‖^2) ≤ Mβ*B*(1+Real.log B)^dβ →
      ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_energy_envelope_cutoff_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ D Q hMα hMβ hD hQ n dα dβ W hW hpos hsm
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform (2*Mα) Mβ (by positivity) hMβ
    (n+2) dα dβ W hW hpos hsm
  obtain ⟨C₀,hC₀,hcount⟩ := stoppedNormDyad_count_power
  let KP := 3*C₀*(1+Real.log Q)
  let KS := 3*C₀*(1+Real.log D)
  let R := K*Q^(5/6:ℝ)*(2*D)^(5/6:ℝ)
  refine ⟨KP*KS*R,max Z₀ ((65536:ℝ)^2),
    by dsimp [KP,KS,R]; positivity [Real.log_nonneg hQ,Real.log_nonneg hD],?_⟩
  intro P S α β B A X T H hB hAlow hAup hA3 hX hT hH hHB hP hS hea heb
  have hBbig : (65536:ℝ)^2 ≤ B := (le_max_right _ _).trans hB
  have hB1 : 1 ≤ B := by nlinarith
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAB : B ≤ A := by
    have hb : B ≤ (2*D*B)^(3/2:ℝ) := by
      calc
        B ≤ 2*D*B := by nlinarith
        _ = (2*D*B)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith : (1:ℝ) ≤ 2*D*B) (by norm_num)
    have hp := Real.rpow_nonneg (by positivity : 0 ≤ 2*D*B) (3/2:ℝ)
    linarith
  have hA1 : 1 ≤ A := hB1.trans hAB
  have hAp : 0 < A := hBp.trans_le hAB
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hrow (r : ℕ) (hr : r ∈ P.image stoppedNormDyadIndex)
      (s : ℕ) (hs : s ∈ S.image stoppedNormDyadIndex) :
      ‖envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
        α β W H T X‖ ≤ R*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(n+2) := by
    let A' := stoppedNormDyadLength r/2
    let Z := stoppedNormDyadLength s
    obtain ⟨x,hx,hxr⟩ := Finset.mem_image.mp hr
    obtain ⟨y,hy,hys⟩ := Finset.mem_image.mp hs
    have hxd := stoppedNormDyad_outer_bounds (Finset.mem_filter.mpr ⟨hx,hxr⟩) (hP x hx).1
    have hyd := stoppedNormDyad_outer_bounds (Finset.mem_filter.mpr ⟨hy,hys⟩) (hS y hy).1
    have hAr : A/2 ≤ A' := by dsimp [A']; linarith [(hP x hx).2.1]
    have hArup : A' ≤ Q*A := hxd.1.trans (hP x hx).2.2
    have hBZ : B ≤ Z := (hS y hy).2.2.1.trans hyd.2
    have hZB : Z ≤ 2*D*B := by dsimp [Z]; linarith [(hS y hy).2.2.2]
    have hZ1 : 1 ≤ Z := hB1.trans hBZ
    have hZp : 0 < Z := hBp.trans_le hBZ
    have hArp : 0 < A' := (div_pos hAp (by norm_num)).trans_le hAr
    have hlog : 1+Real.log B ≤ 1+Real.log Z := by linarith [Real.log_le_log hBp hBZ]
    have hAlow' : 2*Z^(3/2:ℝ) ≤ A' := by
      have hh := Real.rpow_le_rpow hZp.le hZB (by norm_num : (0:ℝ) ≤ 3/2)
      linarith
    have hAup' : A' ≤ Z^(2+γ) :=
      (hArup.trans hAup).trans (Real.rpow_le_rpow hBp.le hBZ (by linarith))
    have hT' : Z^(1/50:ℝ) ≤ T :=
      (Real.rpow_le_rpow hZp.le hZB (by norm_num)).trans hT
    have hPa : ∀ x ∈ stoppedNormDyad P r, primary x ∧ 1 ≤ norm x/A' ∧ norm x/A' ≤ 2 := by
      intro x hx
      have hpx := (hP x (Finset.mem_filter.mp hx).1).1
      have hd := stoppedNormDyad_outer_bounds hx hpx
      exact ⟨hpx,(le_div_iff₀ hArp).mpr (by simpa only [one_mul] using hd.1),
        (div_le_iff₀ hArp).mpr (by dsimp [A']; linarith)⟩
    have hSb : ∀ y ∈ stoppedNormDyad S s,
        primary y ∧ Squarefree y ∧ Z/2 ≤ norm y ∧ norm y ≤ Z := by
      intro y hy
      have hpy := hS y (Finset.mem_filter.mp hy).1
      have hd := stoppedNormDyad_outer_bounds hy hpy.1
      exact ⟨hpy.1,hpy.2.1,hd⟩
    have hea' : (∑ x ∈ stoppedNormDyad P r, ‖α x‖^2) ≤
        (2*Mα)*A'*(1+Real.log Z)^dα := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)).trans
      apply hea.trans
      have hh := mul_le_mul
        (mul_le_mul_of_nonneg_left (show A ≤ 2*A' by linarith) hMα)
        (pow_le_pow_left₀ hL.le hlog dα) (by positivity) (by positivity)
      convert hh using 1 <;> first | rfl | ring
    have heb' : (∑ y ∈ stoppedNormDyad S s, ‖β y‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)).trans
      exact heb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hBZ hMβ)
        (pow_le_pow_left₀ hL.le hlog dβ) (by positivity) (by positivity))
    have hh := hbound (stoppedNormDyad P r) (stoppedNormDyad S s) α β Z A' X T H
      (((le_max_left _ _).trans hB).trans hBZ) hAlow' hAup' hX hT' hH
      (hHB.trans (pow_le_pow_left₀ hBp.le hBZ 3)) hPa hSb
      hea' heb'
    apply hh.trans
    calc
      _ ≤ K*(Q*A)^(5/6:ℝ)*(2*D*B)^(5/6:ℝ)/(1+Real.log B)^(n+2) := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hArp.le hArup (by norm_num)) hK.le)
            (Real.rpow_le_rpow hZp.le hZB (by norm_num)) (by positivity) (by positivity))
          (pow_pos hL _) (pow_le_pow_left₀ hL.le hlog _)
      _ = _ := by
        rw [Real.mul_rpow hQp.le hAp.le,Real.mul_rpow (by positivity : 0 ≤ 2*D) hBp.le]
        dsimp [R]
        ring
  have hPc := hcount P Q A B hQ hA1 hB1 hA3 (fun x hx => (hP x hx).2.2)
  have hBc : B ≤ B^3 := le_self_pow₀ hB1 (by norm_num : 3 ≠ 0)
  have hSc := hcount S D B B hD hB1 hB1 hBc (fun y hy => (hS y hy).2.2.2)
  have hb := envelopeCutoffBilinearTail_dyads_bound P S α β W H T X _ hrow
  apply hb.trans
  calc
    _ ≤ (KP*(1+Real.log B))*(KS*(1+Real.log B))*
        (R*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(n+2)) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [R]; positivity)
      exact mul_le_mul hPc hSc (Nat.cast_nonneg _) (by dsimp [KP]; positivity [Real.log_nonneg hQ])
    _ = _ := by rw [pow_add]; norm_num; field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform second moments of the finite squarefree prime convolutions with
unit coordinate weights. Only actual support counting and finite multiplicity
are used. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrimeCoefficient_l2_unit {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hW : ∀ i x, ‖W i x‖ ≤ 1) (e : Eisenstein) :
    (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2) ≤
      (18*R^Fintype.card ι*((Fintype.card ι)^(Fintype.card ι):ℕ)^2)*(∏ i, X i) := by
  have hb (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
    simpa using fullPrimeCoefficient_norm_bound R W X (fun _ => 1)
      (fun _ => by norm_num) hW b
  calc
    _ ≤ ∑ _b ∈ fullSquarefreePrimeSupport R W X e,
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)^2 :=
      Finset.sum_le_sum (fun b _ => pow_le_pow_left₀ (_root_.norm_nonneg _) (hb b) 2)
    _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)^2 := by simp
    _ ≤ (18*(R^Fintype.card ι*(∏ i, X i)))*
        (((Fintype.card ι)^(Fintype.card ι):ℕ):ℝ)^2 :=
      mul_le_mul_of_nonneg_right (fullPrimeSupport_card_bound hR W X hX hlo hhi e) (sq_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeTailHighProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single power-width exponent for every actual independent prime
product. The exponent is chosen before the coordinate types and arities;
all finite energies follow from unit weights and actual support counting. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_high_full_prime_envelope_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ] (R : ℝ), 1 ≤ R →
      ∀ (n : ℕ) (W : ℝ → ℂ), HasCompactSupport W →
      tsupport W ⊆ Set.Ioi 0 → ContDiff ℝ ∞ W →
      ∃ K B₀ : ℝ, 0 < K ∧
    ∀ (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
        (X T H : ℝ),
      (∀ i, 1 ≤ XA i) → (∀ i, 1 ≤ XB i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, R < x → WA i x = 0) →
      (∀ i x, x < 1 → WB i x = 0) → (∀ i x, R < x → WB i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) → (∀ i x, ‖WB i x‖ ≤ 1) →
      let A := ∏ i, XA i
      let B := ∏ i, XB i
      B₀ ≤ B → 4*(2*R^Fintype.card ι*B)^(3/2:ℝ) ≤ A →
      R^Fintype.card κ*A ≤ B^(2+γ) → A ≤ B^3 → 0 < X →
      (2*R^Fintype.card ι*B)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (fullSquarefreePrimeSupport R WA XA 1)
        (fullSquarefreePrimeSupport R WB XB 1)
        (fun a => theta ℓ a*fullPrimeCoefficient R WA XA a)
        (fun b => theta ℓ b*fullPrimeCoefficient R WB XB b) W H T X‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_wide_envelope_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro ι κ _ _ _ _ R hR n W hW hpos hsm
  let MA : ℝ := 18*R^Fintype.card κ*((Fintype.card κ)^(Fintype.card κ):ℕ)^2
  let MB : ℝ := 18*R^Fintype.card ι*((Fintype.card ι)^(Fintype.card ι):ℕ)^2
  obtain ⟨K,B₀,hK,hbound⟩ := huniform MA MB
    (R^Fintype.card ι) (R^Fintype.card κ)
    (by dsimp [MA]; positivity) (by dsimp [MB]; positivity)
    (one_le_pow₀ hR) (one_le_pow₀ hR) n 0 0 W hW hpos hsm
  refine ⟨K,B₀,hK,?_⟩
  intro WA WB XA XB X T H hXA hXB hAlo hAhi hBlo hBhi hWA hWB
  dsimp only
  intro hB hAlow hAup hA3 hX hT hH hHB
  have hXAp : ∀ i, 0 < XA i := fun i => zero_lt_one.trans_le (hXA i)
  have hXBp : ∀ i, 0 < XB i := fun i => zero_lt_one.trans_le (hXB i)
  have henergyA := (theta_coefficient_energy ℓ _ _
    (fun x hx => (fullSquarefreePrimeSupport_primary R WA XA 1 hx).1)).trans_le
    (fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WA XA hXAp hAlo hAhi hWA 1)
  have henergyB := (theta_coefficient_energy ℓ _ _
    (fun y hy => (fullSquarefreePrimeSupport_primary R WB XB 1 hy).1)).trans_le
    (fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WB XB hXBp hBlo hBhi hWB 1)
  apply hbound _ _ _ _ (∏ i, XB i) (∏ i, XA i) X T H
    hB hAlow hAup hA3 hX hT hH hHB
  · intro x hx
    exact ⟨(fullSquarefreePrimeSupport_primary R WA XA 1 hx).1,
      fullPrimeProduct_norm_bounds R WA XA hXAp hAlo hAhi (Finset.mem_filter.mp hx).1⟩
  · intro y hy
    exact ⟨(fullSquarefreePrimeSupport_primary R WB XB 1 hy).1,
      (fullSquarefreePrimeSupport_primary R WB XB 1 hy).2,
      fullPrimeProduct_norm_bounds R WB XB hXBp hBlo hBhi (Finset.mem_filter.mp hy).1⟩
  · simpa only [MA,pow_zero,mul_one] using henergyA
  · simpa only [MB,pow_zero,mul_one] using henergyB

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OverlapScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary powers and logarithmic absorption for model overlap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma overlap_power_log_saving {c : ℝ} (hc : 0 < c) (a k : ℕ) :
    ∀ᶠ L : ℝ in atTop, (1+Real.log L)^a/L^c ≤ 1/(1+Real.log L)^(2*k) := by
  filter_upwards [negative_power_log_saving hc (a+2*k),eventually_ge_atTop (1:ℝ)] with L h hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  calc
    _ = (1+Real.log L)^a*L^(-c) := by rw [Real.rpow_neg hLp.le]; ring
    _ ≤ (1+Real.log L)^a*(1/(1+Real.log L)^(a+2*k)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hz.le _)
    _ = _ := by rw [pow_add]; field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma semiprimeSmoothWeight_high (r : ℝ) {x : ℝ} (hx : 2 < x) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_high hx,zero_mul]

lemma semiprimeSmoothWeight_norm (r x : ℝ) : ‖semiprimeSmoothWeight r x‖ ≤ 1 := by
  have hc : ‖1-(primeDetectorCutoff (r*x):ℂ)‖ ≤ 1 := by
    have he : (1-(primeDetectorCutoff (r*x):ℂ)) =
        ((1-primeDetectorCutoff (r*x):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (sub_nonneg.mpr (primeDetectorCutoff_le_one _))]
    linarith [primeDetectorCutoff_nonneg (r*x)]
  rw [semiprimeSmoothWeight,norm_mul]
  exact (mul_le_mul (normPartitionWeight_norm x) hc (_root_.norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma distinguishedSmoothWeight_low (r : ℝ × ℝ) {x : ℝ} (hx : x < 1) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_low _ hx,sub_self]

lemma distinguishedSmoothWeight_high (r : ℝ × ℝ) {x : ℝ} (hx : 2 < x) :
    distinguishedSmoothWeight r x = 0 := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_high _ hx,sub_self]

lemma distinguishedSmoothWeight_norm (r : ℝ × ℝ) (x : ℝ) :
    ‖distinguishedSmoothWeight r x‖ ≤ 1 := by
  have he : distinguishedSmoothWeight r x = normPartitionWeight x*
      ((primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x):ℝ):ℂ) := by
    simp only [distinguishedSmoothWeight,semiprimeSmoothWeight,Complex.ofReal_sub]
    ring
  have hb : |primeDetectorCutoff (r.1*x)-primeDetectorCutoff (r.2*x)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [primeDetectorCutoff_nonneg (r.1*x),
      primeDetectorCutoff_nonneg (r.2*x),primeDetectorCutoff_le_one (r.1*x),
      primeDetectorCutoff_le_one (r.2*x)]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (normPartitionWeight_norm x) hb (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCoordinateWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

lemma largeTupleCoordinateWeight_norm {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) (x : ℝ) :
    ‖largeTupleCoordinateWeight ξ X k a x‖ ≤ 1 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_norm _ x
  · exact semiprimeSmoothWeight_norm _ x

lemma largeTupleCoordinateWeight_low {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : x < 1) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_low _ hx
  · exact semiprimeSmoothWeight_low _ hx

lemma largeTupleCoordinateWeight_high {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : 2 < x) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_high _ hx
  · exact semiprimeSmoothWeight_high _ hx

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRestrictedWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate weights restricted to either predicate in a fixed
partition of the tuple indices. This preserves the predicate-subtype
indexing in the exact finite convolution identity. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {i j : ℕ} (P : (Fin i ⊕ Fin j) → Prop) [DecidablePred P]

lemma largeTupleRestrictedLength_notMem (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) :
    largeTupleRestrictedLength (fun a => a ∉ s) z =
      largeTupleGroupLength (Finset.univ\s) z := by
  exact (Finset.prod_subtype (Finset.univ\s) (by simp)
    (fun a => largeTupleNormScale z.1.2 a)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryGroupRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict grouping gap above one third implies the actual logarithmic
upper-length condition in the published-input bilinear theorem. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem ordinary_group_upper_range {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3+δ:ℝ) ≤ B → A*B ≤ C*X → A ≤ B^2/(1+Real.log B)^G := by
  let α : ℝ := 1/3+δ
  let ε : ℝ := δ/α
  have hα : 0 < α := by dsimp [α]; linarith
  have hε : 0 < ε := div_pos hδ hα
  have hε1 : ε < 1 := (div_lt_one hα).mpr (by dsimp [α]; linarith)
  have hpower : α*(3-ε) = 1+2*δ := by
    dsimp [ε]
    field_simp [hα.ne']
    dsimp [α]
    ring
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (overlap_power_log_saving hε G 0)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hα).eventually_ge_atTop B₀,
    eventually_const_mul_rpow_le (by linarith : (1:ℝ) < 1+2*δ) C]
    with X hX hXB hgap
  intro A B hB hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX hα.le).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hlog : (1+Real.log B)^G ≤ B^ε := by
    have hh := hB₀ B (hXB.trans hB)
    simpa only [Nat.mul_zero,pow_zero,div_one,one_mul] using
      (div_le_iff₀ (Real.rpow_pos_of_pos hBp ε)).mp hh
  have hp : X^(1+2*δ) ≤ B^(3-ε) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le α) hB (by linarith : 0 ≤ 3-ε)
    rw [←Real.rpow_mul hXp.le,hpower] at hh
    exact hh
  have hCX : C*X ≤ B^(3-ε) := by
    have hh : C*X ≤ X^(1+2*δ) := by simpa only [Real.rpow_one] using hgap
    exact hh.trans hp
  have hm : (A*B)*(1+Real.log B)^G ≤ B^3 := by
    calc
      _ ≤ (C*X)*(1+Real.log B)^G := mul_le_mul_of_nonneg_right hAB (pow_nonneg hL.le _)
      _ ≤ (C*X)*B^ε := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC.le hXp.le)
      _ ≤ B^(3-ε)*B^ε := mul_le_mul_of_nonneg_right hCX (Real.rpow_nonneg hBp.le _)
      _ = B^3 := by rw [←Real.rpow_add hBp]; norm_num
  apply (le_div_iff₀ (pow_pos hL G)).mpr
  apply (mul_le_mul_iff_right₀ hBp).mp
  first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBoxRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both length inequalities in the bilinear theorem follow from a
shorter grouped side and a strict gap above one third. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_prime_box_range {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (n G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X/(2*2^n) ≤ A*B → A*B ≤ 3*X → B^2 ≤ 3*X → X^(1/3+δ:ℝ) ≤ B →
      B^(1-η/16) ≤ A ∧ A ≤ B^2/(1+Real.log B)^G := by
  let D : ℝ := 2*2^n
  let K : ℝ := 3*D
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := mul_pos (by norm_num) hD
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le (by linarith : (1-η/16:ℝ) < 1) K)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : (0:ℝ) < 1/3+δ)).eventually_ge_atTop T,
    ordinary_group_upper_range hδ (by norm_num : (0:ℝ) < 3) G]
    with X hX hXT hupper
  intro A B hABlow hABhi hBsq hBlow
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by linarith : (0:ℝ) ≤ 1/3+δ)).trans hBlow
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hAX : X ≤ D*(A*B) := by
    have hh := (div_le_iff₀ hD).mp hABlow
    simpa only [mul_comm] using hh
  have hBA : B ≤ K*A := by
    apply (mul_le_mul_iff_right₀ hBp).mp
    have hm := hBsq.trans (mul_le_mul_of_nonneg_left hAX (by norm_num : (0:ℝ) ≤ 3))
    dsimp only [K]
    nlinarith
  have hpower : K*B^(1-η/16) ≤ B := by
    simpa only [Real.rpow_one] using hT B (hXT.trans hBlow)
  refine ⟨(mul_le_mul_iff_right₀ hK).mp ?_,hupper A B hBlow hABhi⟩
  simpa only [mul_comm] using hpower.trans hBA

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeHeckeGroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the full-envelope Hecke tail to the literal
independent coordinates supplied by a surviving prime tuple. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma envelopeCutoffBilinearTail_swap (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (W : ℝ → ℂ) (H T X : ℝ) :
    envelopeCutoffBilinearTail P S α β W H T X =
      envelopeCutoffBilinearTail S P β α W H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm b a]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeHighGroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The power-width tail specialized to every actual prime group. The
positive width exponent is chosen before the arities and the group. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_high_group_uniform
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (ξ : ℝ) (k : ℕ),
      ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → 4*(2*(2:ℝ)^s.card*B)^(3/2:ℝ) ≤ A →
      (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})*A ≤
        B^(2+γ) → A ≤ B^3 →
      (2*(2:ℝ)^s.card*B)^(1/50:ℝ) ≤ T →
      1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ z.1.1 z.1.2 s a)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨γ,hγ,huniform⟩ := angular_high_full_prime_envelope_tail_uniform ℓ hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro i j s ξ k
  obtain ⟨K,B₀,hK,hbound⟩ := huniform s {x : Fin i ⊕ Fin j // x ∉ s}
    2 (by norm_num) k primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨K,B₀,hK,?_⟩
  intro z H T
  dsimp only
  intro hB hAlow hAhigh hA3 hT hH hHcube
  have hb := hbound (largeTupleRestrictedWeight (fun x => x ∉ s) ξ z)
    (largeTupleGroupWeight ξ s z)
    (fun x : {x : Fin i ⊕ Fin j // x ∉ s} => largeTupleNormScale z.1.2 x)
    (fun x : s => largeTupleNormScale z.1.2 x) z.1.1 T H
    (fun x => z.property x) (fun x => z.property x)
    (fun x _y hy => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 x hy)
    (fun x y => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 x y)
    (fun x y => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 x y)
  have hprodA : (∏ x : {x : Fin i ⊕ Fin j // x ∉ s}, largeTupleNormScale z.1.2 x) =
      largeTupleGroupLength (Finset.univ\s) z := largeTupleRestrictedLength_notMem s z
  have hprodB : (∏ x : s, largeTupleNormScale z.1.2 x) = largeTupleGroupLength s z :=
    Finset.prod_coe_sort s (fun x => largeTupleNormScale z.1.2 x)
  simp only [hprodA,hprodB,Fintype.card_coe] at hb
  have hh := hb hB hAlow hAhigh hA3 z.1.1.property hT hH hHcube
  rw [envelopeCutoffBilinearTail_swap]
  exact hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The enlarged conductor range overlaps the published-Hecke height
range. Fixed dyadic support constants are absorbed by a strict power gap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_small_group_length {D K : ℝ} (hD : 0 < D) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → X/D ≤ A*B →
      B ≤ X^(12/25:ℝ) → K*B^(27/25:ℝ) ≤ A := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (624/625:ℝ) < 1 by norm_num) (D*K)]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hpow : B^(52/25:ℝ) ≤ X^(624/625:ℝ) := by
    calc
      _ ≤ (X^(12/25:ℝ))^(52/25:ℝ) :=
        Real.rpow_le_rpow hB.le hBX (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hXp.le]; norm_num
  have hprod : D*(B*(K*B^(27/25:ℝ))) ≤ D*(A*B) := by
    calc
      _ = (D*K)*B^(52/25:ℝ) := by
        have he : B*B^(27/25:ℝ) = B^(52/25:ℝ) := by
          calc
            _ = B^(1:ℝ)*B^(27/25:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hB]; norm_num
        calc
          _ = (D*K)*(B*B^(27/25:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ (D*K)*X^(624/625:ℝ) := mul_le_mul_of_nonneg_left hpow (mul_pos hD hK).le
      _ ≤ X := by simpa only [Real.rpow_one] using hgap
      _ ≤ D*(A*B) := by
        have hh := (div_le_iff₀ hD).mp hAB
        nlinarith
  have he : D*B*(K*B^(27/25:ℝ)) ≤ D*B*A := by nlinarith [hprod]
  exact (mul_le_mul_iff_right₀ (mul_pos hD hB)).mp he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeMiddleRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual intermediate prime-group range meets both length and
height hypotheses of the enlarged dispersion estimate, with fixed support
widths retained. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_middle_upper :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → A*B ≤ 3*X →
      X^(39/100:ℝ) ≤ B → A ≤ B^(19/10:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (1:ℝ) < 1131/1000 by norm_num) 3]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp : 3*X ≤ B^(29/10:ℝ) := by
    calc
      _ = 3*X^(1:ℝ) := by rw [Real.rpow_one]
      _ ≤ X^(1131/1000:ℝ) := hgap
      _ = (X^(39/100:ℝ))^(29/10:ℝ) := by rw [←Real.rpow_mul hXp.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBX (by norm_num)
  have he : B*B^(19/10:ℝ) = B^(29/10:ℝ) := by
    calc
      _ = B^(1:ℝ)*B^(19/10:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hB]; norm_num
  apply (mul_le_mul_iff_left₀ hB).mp
  calc
    A*B ≤ 3*X := hAB
    _ ≤ B^(29/10:ℝ) := hp
    _ = B^(19/10:ℝ)*B := by rw [←he]; ring

theorem eventually_tailPrime_middle_height {C : ℝ} (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 0 < B → B ≤ X^(12/25:ℝ) →
      (C*B)^(1/50:ℝ) ≤ X^(1/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (6/625:ℝ) < 1/100 by norm_num) (C^(1/50:ℝ))]
    with X hX hgap
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  calc
    _ = C^(1/50:ℝ)*B^(1/50:ℝ) := Real.mul_rpow hC.le hB.le
    _ ≤ C^(1/50:ℝ)*(X^(12/25:ℝ))^(1/50:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB.le hBX (by norm_num)) (by positivity)
    _ = C^(1/50:ℝ)*X^(6/625:ℝ) := by rw [←Real.rpow_mul hXp.le]; norm_num
    _ ≤ _ := hgap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeSmallRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual small prime groups meet the localized length range. Constants
from their fixed support widths are retained until a genuine exponent or
logarithmic margin absorbs them. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_small_localized_length {D K : ℝ} (hD : 0 < D) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → X/D ≤ A*B →
      B ≤ X^(39/100:ℝ) → K*B^(3/2:ℝ) ≤ A := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (39/40:ℝ) < 1 by norm_num) (D*K)]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hpow : B^(5/2:ℝ) ≤ X^(39/40:ℝ) := by
    calc
      _ ≤ (X^(39/100:ℝ))^(5/2:ℝ) :=
        Real.rpow_le_rpow hB.le hBX (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hXp.le]; norm_num
  have hprod : D*(B*(K*B^(3/2:ℝ))) ≤ D*(A*B) := by
    calc
      _ = (D*K)*B^(5/2:ℝ) := by
        have he : B*B^(3/2:ℝ) = B^(5/2:ℝ) := by
          calc
            _ = B^(1:ℝ)*B^(3/2:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hB]; norm_num
        calc
          _ = (D*K)*(B*B^(3/2:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ (D*K)*X^(39/40:ℝ) := mul_le_mul_of_nonneg_left hpow (mul_pos hD hK).le
      _ ≤ X := by simpa only [Real.rpow_one] using hgap
      _ ≤ D*(A*B) := by
        have hh := (div_le_iff₀ hD).mp hAB
        nlinarith
  have he : D*B*(K*B^(3/2:ℝ)) ≤ D*B*A := by nlinarith [hprod]
  exact (mul_le_mul_iff_right₀ (mul_pos hD hB)).mp he


theorem eventually_tailPrime_small_high_upper {κ γ Q : ℝ} (hκ : 0 < κ)
    (hκsmall : κ < 1/12) (hQ : 0 < Q)
    (hmargin : 1 < (1/3-3*κ)*(3+γ)) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3-3*κ) ≤ B → A*B ≤ 3*X → Q*A ≤ B^(2+γ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le hmargin (3*Q)] with X hX hgap
  intro A B hBlo hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hBp : 0 < B := (Real.rpow_pos_of_pos hXp _).trans_le hBlo
  have hexp : 0 ≤ 3+γ := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1/3-3*κ) (le_of_not_ge hh)
    linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBlo hexp
  rw [←Real.rpow_mul hXp.le] at hp
  have htop : 3*Q*X ≤ B^(3+γ) := by
    simpa only [Real.rpow_one] using hgap.trans hp
  apply (mul_le_mul_iff_left₀ hBp).mp
  calc
    Q*A*B ≤ 3*Q*X := by nlinarith only [mul_le_mul_of_nonneg_left hAB hQ.le]
    _ ≤ B^(3+γ) := htop
    _ = B^(2+γ)*B := by
      calc
        _ = B^((2+γ)+1) := by congr 1; ring
        _ = B^(2+γ)*B^((1:ℝ)) := Real.rpow_add hBp _ _
        _ = _ := by rw [Real.rpow_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TripleKernelScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest coordinate of a triple has a fixed power lower bound.
These normalizations preserve the fractional logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma triple_log_comparison {X B : ℝ} (hX : 1 ≤ X)
    (hB : X^(1/4:ℝ) ≤ B) :
    (1/4:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp (1/4:ℝ)) hB
  rw [Real.log_rpow hXp] at hh
  linarith

lemma triple_bilinear_nat_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(1/4:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) (k : ℕ) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLB.le _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((1/4:ℝ)*(1+Real.log X))^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hL k)
    _ = _ := by rw [mul_pow]; field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeHeightRanges
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original logarithmic and power height thresholds meet the group
estimates, with every fixed support constant retained. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma tailPrime_height_cube {X B η : ℝ} (hX : 1 ≤ X) (hη : η ≤ 1/1500)
    (hB : X^(1/4:ℝ) ≤ B) : X^(1/6+η) ≤ B^3 := by
  calc
    _ ≤ X^((1/4:ℝ)*3) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = (X^(1/4:ℝ))^3 := (Real.rpow_mul_natCast (zero_le_one.trans hX) _ _)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hB 3

theorem eventually_tailPrime_large_height_cap {η : ℝ} (hη : η ≤ 1/1500) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(12/25:ℝ) ≤ B →
      2*Real.pi*X^(1/6+η) ≤ B^(7/20:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (1/6+η:ℝ) < (12/25)*(7/20) by linarith)
      (2*Real.pi)] with X hX hgap
  intro B hB
  apply hgap.trans
  rw [Real.rpow_mul (zero_le_one.trans hX)]
  exact Real.rpow_le_rpow (by positivity) hB (by norm_num)

theorem eventually_tailPrime_power_height_log (m : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 1 ≤ B → B ≤ 3*X →
      (1+Real.log B)^m ≤ X^(1/100:ℝ) := by
  let C : ℝ := (1+Real.log 3)^m
  filter_upwards [eventually_ge_atTop (1:ℝ),
    overlap_power_log_saving (by norm_num : (0:ℝ) < 1/200) m 0,
    eventually_const_mul_rpow_le (show (1/200:ℝ) < 1/100 by norm_num) C]
    with X hX hlog hgap
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hblog := Real.log_le_log (zero_lt_one.trans_le hB) hBX
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hblog
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hb : 1+Real.log B ≤ (1+Real.log 3)*(1+Real.log X) := by
    nlinarith [Real.log_nonneg hX,mul_nonneg hlog3 (Real.log_nonneg hX)]
  have hh : (1+Real.log X)^m ≤ X^(1/200:ℝ) := by
    simp only [Nat.mul_zero,pow_zero,div_one] at hlog
    exact (div_le_one (Real.rpow_pos_of_pos hXp (1/200:ℝ))).mp hlog
  calc
    _ ≤ ((1+Real.log 3)*(1+Real.log X))^m :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hB]) hb m
    _ = C*(1+Real.log X)^m := by rw [mul_pow]
    _ ≤ C*X^(1/200:ℝ) := mul_le_mul_of_nonneg_left hh (by dsimp [C]; positivity)
    _ ≤ _ := hgap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeUpperGroupBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three overlapping length ranges bound the literal upper-height prime
product tail. The stopping exponent is chosen before arity and logarithmic
saving, and may be decreased to match the low-scale stopping argument. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_upper_group_bound_uniform_oai
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (k : ℕ),
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      X^(1/3-3*κ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ z.1.1 z.1.2 s a)
        primeProductEnvelope H T z.1.1‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨γ,hγ,hhigh⟩ := angular_tailPrime_high_group_uniform ℓ hHuxley hMV hC
  let κ₀ : ℝ := min (1/1000) (γ/(100*(3+γ)))
  have hden : 0 < 100*(3+γ) := by positivity
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (div_pos hγ hden)
  have hκ₀small : κ₀ < 1/36 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i j s k
  have hκsmall : κ < 1/12 := by linarith
  have hκtiny : κ ≤ 1/1000 := hκle.trans (min_le_left _ _)
  have hκγ : κ*(3+γ) ≤ γ/100 := by
    have hh := mul_le_mul_of_nonneg_right (hκle.trans (min_le_right _ _))
      (show 0 ≤ 3+γ by positivity)
    have he : γ/(100*(3+γ))*(3+γ) = γ/100 := by field_simp
    rwa [he] at hh
  have hmargin : 1 < (1/3-3*κ)*(3+γ) := by nlinarith
  have hmargin₃ : 1 < (1/3-3*κ)*(3+(1:ℝ)) := by linarith
  have hquarter : (1/4:ℝ) ≤ 1/3-3*κ := by linarith
  let D : ℝ := 2*2^(i+j)
  let W : ℝ := 2*(2:ℝ)^s.card
  let Q : ℝ := (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨K₁,B₁,hK₁,hb₁⟩ := hhigh i j s ξ k
  obtain ⟨K₂,B₂,hK₂,hb₂⟩ := angular_tailPrime_middle_group ℓ s hHuxley hMV hC k
  obtain ⟨η,G,K₃,B₃,m,hη,_hηone,hK₃,hb₃⟩ :=
    angular_tailPrime_hecke_group ℓ s hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ k
  let K := K₁+K₂+K₃
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*3^(5/6:ℝ)/(1/4:ℝ)^k,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < 1/3-3*κ)).eventually_ge_atTop (max B₁ (max B₂ B₃)),
    eventually_tailPrime_small_localized_length hD (show 0 < 4*W^(3/2:ℝ) by positivity),
    eventually_tailPrime_small_group_length hD (show 0 < W^(27/25:ℝ) by positivity),
    eventually_tailPrime_small_high_upper hκ hκsmall hQ hmargin,
    eventually_tailPrime_small_high_upper hκ hκsmall (by norm_num : (0:ℝ) < 1) hmargin₃,
    eventually_tailPrime_middle_upper,
    eventually_tailPrime_middle_height hW,
    eventually_prime_box_range (show (0:ℝ) < 39/100-1/3 by norm_num) hη (i+j) G,
    eventually_tailPrime_power_height_log m,
    eventually_tailPrime_large_height_cap (by norm_num : (1/3000:ℝ) ≤ 1/1500)]
    with X hX hlarge hlocal hmiddle hlowerpower hcube hupper hheight hbox hlog hcap
  intro z H T hz
  dsimp only
  intro hBlo hBsq hABlo hABhi hrough hT hH hHX
  let B := largeTupleGroupLength s z
  let A := largeTupleGroupLength (Finset.univ\s) z
  have hBp : 0 < B := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
  have hAp : 0 < A := zero_lt_one.trans_le (largeTupleGroupLength_one _ z)
  have hB₁ : B₁ ≤ B := (le_max_left _ _).trans (hlarge.trans hBlo)
  have hB₂ : B₂ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (hlarge.trans hBlo))
  have hB₃ : B₃ ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans (hlarge.trans hBlo))
  have hBquarter : X^(1/4:ℝ) ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hX hquarter).trans hBlo
  have hBX : B ≤ 3*X := by nlinarith [largeTupleGroupLength_one s z]
  have hHcube : H ≤ B^3 := hHX.trans (tailPrime_height_cube hX (by norm_num) hBquarter)
  have hA3 : A ≤ B^3 := by
    have hh := hcube A B hBlo hABhi
    rw [one_mul,show (2+(1:ℝ)) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast] at hh
    exact hh
  have hscale : K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k :=
    triple_bilinear_nat_scale hX hAp.le hBquarter hK.le hABhi k
  apply le_trans _ hscale
  have hnonneg : 0 ≤ A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    have hl := Real.log_nonneg (largeTupleGroupLength_one s z)
    positivity
  have henlarge {K' : ℝ} (hh : K' ≤ K) :
      K'*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_right hh hnonneg
  by_cases hsmall : B ≤ X^(39/100:ℝ)
  · have hlo : 4*(W*B)^(3/2:ℝ) ≤ A := by
      rw [Real.mul_rpow hW.le hBp.le]
      simpa only [mul_assoc] using hlocal A B hBp hABlo hsmall
    have hup : Q*A ≤ B^(2+γ) := hlowerpower A B hBlo hABhi
    have ht : (W*B)^(1/50:ℝ) ≤ T :=
      (hheight B hBp (hsmall.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)))).trans hT
    exact (hb₁ z H T hB₁ hlo hup hA3 ht hH hHcube).trans
      (henlarge (by dsimp [K]; linarith))
  · have hbig : X^(39/100:ℝ) ≤ B := le_of_lt (lt_of_not_ge hsmall)
    by_cases hmid : B ≤ X^(12/25:ℝ)
    · have hlo : (W*B)^(27/25:ℝ) ≤ A := by
        rw [Real.mul_rpow hW.le hBp.le]
        exact hmiddle A B hBp hABlo hmid
      have hup : A ≤ B^(19/10:ℝ) := hupper A B hBp hABhi hbig
      have ht : (W*B)^(1/50:ℝ) ≤ T := (hheight B hBp hmid).trans hT
      exact (hb₂ z H T hB₂ hlo hup ht hH hHcube).trans
        (henlarge (by dsimp [K]; linarith))
    · have hlargeB : X^(12/25:ℝ) ≤ B := le_of_lt (lt_of_not_ge hmid)
      have hrange := hbox A B hABlo hABhi hBsq (by
        simpa only [show (1/3+(39/100-1/3):ℝ) = 39/100 by ring] using hbig)
      have ht : (1+Real.log B)^m ≤ T :=
        (hlog B (largeTupleGroupLength_one s z) hBX).trans hT
      have hh : 2*Real.pi*H ≤ B^(7/20:ℝ) :=
        (mul_le_mul_of_nonneg_left hHX (by positivity)).trans (hcap B hlargeB)
      exact (hb₃ z H T hB₃ hrough hrange.1 hrange.2 ht hH hHcube hh).trans
        (henlarge (by dsimp [K]; linarith))

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform_oai := @OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform_oai
