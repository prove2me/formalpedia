-- Prove2me | solution 1 for OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:23:11.978709+00:00
-- url     : https://prove2.me/submissions/c856e1a8-1801-4127-b055-9e457d2eefad

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026
import Theorems.Thm_OAI_CubicFirstMoment_hecke_logDeriv_norm_uniform_from_analytic_pair
import Theorems.Thm_OAI_CubicFirstMoment_hecke_zero_free_log_from_analytic_pair

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_eq_sum (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum f X = ∑ p ∈ primeCutoff X, f p := by
  unfold primeCutoffSum
  rw [tsum_eq_sum (s := primeCutoff X)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mem_primeCutoff.mp hp]
  · intro p hp
    simp only [mem_primeCutoff] at hp
    simp [hp]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

@[simp] theorem primeCutoffSum_add (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p + g p) X =
      primeCutoffSum f X + primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_add_distrib]

@[simp] theorem primeCutoffSum_sub (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p - g p) X =
      primeCutoffSum f X - primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_sub_distrib]

@[simp] theorem primeCutoffSum_const_mul (z : ℂ) (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => z * f p) X = z * primeCutoffSum f X := by
  simp only [primeCutoffSum_eq_sum, Finset.mul_sum]

end CubicFirstMoment

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

lemma idealExponentNorm_mono {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentNorm ν ≤ idealExponentNorm κ := by
  rw [← add_tsub_cancel_of_le h, idealExponentNorm_add]
  exact le_mul_of_one_le_right (idealExponentNorm_pos ν).le (idealExponentNorm_ge_one _)

/-- On the powers of one prime ideal, Dirichlet convolution with the
constant-one function is the ordinary partial sum of coefficients. -/
lemma coeff_mul_zeta_single (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) =
      ∑ k ∈ Finset.range (n + 1), MvPowerSeries.coeff (Finsupp.single p k) A := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    MvPowerSeries.coeff_apply, idealZeta, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k _ => A (Finsupp.single p k)) n

lemma coeff_single_eq_zeta_difference (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) A =
      MvPowerSeries.coeff (Finsupp.single p (n + 1)) (A * idealZeta) -
        MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) := by
  rw [coeff_mul_zeta_single, coeff_mul_zeta_single, Finset.sum_range_succ]
  ring

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The ideal von Mangoldt weight on every positive prime power is
exactly the logarithm of the prime-ideal norm. -/
lemma idealVonMangoldt_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealVonMangoldt =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  rw [coeff_single_eq_zeta_difference, mul_comm idealVonMangoldt idealZeta,
    idealZeta_mul_vonMangoldt]
  simp only [MvPowerSeries.coeff_apply, idealLogNorm, idealExponentNorm_single,
    Real.log_pow]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

lemma primeSetExponent_le_iff (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    primeSetExponent S ≤ ν ↔ ∀ p ∈ S, 0 < ν p := by
  constructor
  · intro h p hp
    have h1 := h p
    simpa only [primeSetExponent_apply,ite_eq_left hp,Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero] using h1
  · intro h p
    by_cases hp : p ∈ S
    · simpa only [primeSetExponent_apply,ite_eq_left hp] using (Nat.succ_le_iff.mpr (h p hp))
    · simp [hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedAbel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weighting of prime-character sums

Partial summation applies the
published unweighted Hecke prime estimate to independently specified
smooth prime weights. It also retains the derivative cost of a norm twist.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Complex partial summation with an explicit bound for the cumulative
coefficients. The right side records endpoint values and total variation. -/
theorem weighted_abel_bound (c : ℕ → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hc : ∀ t ∈ Set.Icc a b, ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ H) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hSa : ‖S a‖ ≤ H := hc a ⟨le_rfl, hab⟩
  have hSb : ‖S b‖ ≤ H := hc b ⟨hab, le_rfl⟩
  have hp : IntegrableOn (fun t => deriv f t * S t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c ha hderiv).mono_set Set.Ioc_subset_Icc_self
  have hd0 : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Icc a b) :=
    hderiv.norm.const_mul H
  have hd : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Ioc a b) :=
    hd0.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖deriv f t * S t‖ ≤ H * ‖deriv f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, mul_comm H]
    exact mul_le_mul_of_nonneg_left (hc t (Set.Ioc_subset_Icc_self ht))
      (_root_.norm_nonneg _)
  have hIntegral : ‖∫ t in Set.Ioc a b, deriv f t * S t‖ ≤
      H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, ‖deriv f t * S t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, H * ‖deriv f t‖ := integral_mono_ae hp.norm hd hpoint
      _ = _ := integral_const_mul H _
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hdiff hderiv]
  change ‖f b * S b - f a * S a - ∫ t in Set.Ioc a b, deriv f t * S t‖ ≤ _
  calc
    _ ≤ ‖f b * S b - f a * S a‖ + ‖∫ t in Set.Ioc a b, deriv f t * S t‖ :=
      norm_sub_le _ _
    _ ≤ (‖f b * S b‖ + ‖f a * S a‖) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ :=
      add_le_add (norm_sub_le _ _) hIntegral
    _ ≤ (‖f b‖ * H + ‖f a‖ * H) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hSb (_root_.norm_nonneg _))
        (mul_le_mul_of_nonneg_left hSa (_root_.norm_nonneg _))) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma primeNormCoefficient_cumulative (R t : ℝ) (χ : Eisenstein → ℂ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeNormCoefficient R χ n) = primeCutoffSum χ t := by
  simp only [primeNormCoefficient]
  rw [Finset.sum_comm, primeCutoffSum_eq_sum]
  have he (p : Eisenstein) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, if n = normNat p then χ p else 0) =
        if norm p ≤ t then χ p else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.zero_le, true_and]
    simp only [Nat.le_floor_iff ht, normNat_cast]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans htR⟩, hp.2⟩

lemma primeNormCoefficient_weighted (a b : ℝ) (f : ℝ → ℂ) (χ : Eisenstein → ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * primeNormCoefficient b χ n) =
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : normNat p ≤ ⌊b⌋₊ := (Nat.le_floor_iff (ha.trans hab)).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Ioc, hpb, and_true]
  simp only [Nat.floor_lt ha, normNat_cast]

/-- Weighted interval sums inherit a uniform bound for all their unweighted
prime prefixes, at the explicit cost of total variation of the weight. -/
theorem weighted_prime_bound (χ : Eisenstein → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hχ : ∀ t ∈ Set.Icc a b, ‖primeCutoffSum χ t‖ ≤ H) :
    ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  rw [← primeNormCoefficient_weighted a b f χ ha hab]
  apply weighted_abel_bound (primeNormCoefficient b χ) f ha hab hdiff hderiv
  intro t ht
  rw [primeNormCoefficient_cumulative b t χ (ha.trans ht.1) ht.2]
  exact hχ t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

lemma idealExponentOf_le_log_norm {b : Eisenstein} (hb : b ≠ 0)
    (p : EisensteinIdealPrime) : idealExponentOf b p ≤ Nat.log 2 (normNat b) := by
  have hle : Finsupp.single p (idealExponentOf b p) ≤ idealExponentOf b :=
    Finsupp.single_le_iff.mpr le_rfl
  have hreal : (normNat (idealPrimeRepresentative p) : ℝ) ^ idealExponentOf b p ≤
      (normNat b : ℝ) := by
    calc
      _ = idealExponentNorm (Finsupp.single p (idealExponentOf b p)) :=
        (idealExponentNorm_single _ _).symm
      _ ≤ idealExponentNorm (idealExponentOf b) := idealExponentNorm_mono hle
      _ = norm b := idealExponentOf_norm hb
      _ = _ := (normNat_cast b).symm
  have hpow : normNat (idealPrimeRepresentative p) ^ idealExponentOf b p ≤ normNat b := by
    exact_mod_cast hreal
  exact Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left (idealPrimeRepresentative_normNat_ge_two p) _).trans hpow)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealGenerator_coprime_three_iff (ν : EisensteinIdealExponent) :
    IsCoprime (idealExponentGenerator ν) 3 ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) (by norm_num),
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hν | h3
    · exact hν
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) h3)
  · intro h p
    by_cases hp : p ∈ ramifiedIdealPrimes
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

/-- Primary normalization succeeds exactly on the ideals prime to three. -/
theorem idealPrimaryGenerator_primary_iff (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [← idealGenerator_coprime_three_iff]
  constructor
  · intro h
    exact (primary_coprime_three h).of_isCoprime_of_dvd_left
      (primaryNormalize_associated (idealExponentGenerator ν)).dvd
  · intro h
    exact primaryNormalize_primary (residue_isUnit_of_isCoprime h.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite character attached to the primary mixed cubic
symbol. Including the modulus 3 makes primary normalization periodic
and removes its dependence on the choice of a unit associate. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryNormalize_unit {x : Eisenstein} (hx : IsUnit x) : primaryNormalize x = 1 :=
  primary_unit_eq_one ((primaryNormalize_associated x).isUnit_iff.mp hx)
    (primaryNormalize_primary (hx.map (Ideal.Quotient.mk (modulus 3))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary conductor reduction for the finite residue characters.
Minimality is measured by the positive ideal norm; the inducing character
and exact deleted Euler factors are not supplied as extra assumptions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ResidueCharacterInduces.refl (q : Eisenstein) (χ : MulChar (Residues q) ℂ) :
    ResidueCharacterInduces q q χ χ := ⟨dvd_refl q,fun _ _ => rfl⟩

lemma ResidueCharacterInduces.trans {q d e : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    {ω : MulChar (Residues e) ℂ}
    (hqd : ResidueCharacterInduces q d χ ψ) (hde : ResidueCharacterInduces d e ψ ω) :
    ResidueCharacterInduces q e χ ω := by
  refine ⟨hde.1.trans hqd.1,?_⟩
  intro x hx
  exact (hde.2 x (hx.of_isCoprime_of_dvd_left hqd.1)).trans (hqd.2 x hx)

/-- Every finite character has an actual primitive inducing character,
of modulus dividing the original one and of no larger norm. -/
theorem primitive_residue_conductor_exists {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ ResidueCharacterInduces q d χ ψ ∧
      normNat d ≤ normNat q ∧ PrimitiveResidueCharacter d ψ := by
  let E : ℕ → Prop := fun n => ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
    normNat d = n ∧ ResidueCharacterInduces q d χ ψ
  have hex : ∃ n, E n := ⟨normNat q,q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  obtain ⟨d,ψ,hdn,hd⟩ := Nat.find_spec hex
  refine ⟨d,ψ,ne_zero_of_dvd_ne_zero hq hd.1,hd,?_,?_⟩
  · rw [hdn]
    exact Nat.find_min' hex ⟨q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  · intro e ω he
    rw [hdn]
    exact Nat.find_min' hex ⟨e,ω,rfl,hd.trans he⟩

lemma ResidueCharacterInduces.global_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) :
    ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1 := by
  intro u
  have hc : IsCoprime q (u:Eisenstein) := ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩
  exact (h.2 u hc).trans (hu u)

lemma ResidueCharacterInduces.restriction {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (x : Eisenstein) :
    χ (Ideal.Quotient.mk (modulus q) x) =
      if IsCoprime q x then ψ (Ideal.Quotient.mk (modulus d) x) else 0 := by
  by_cases hx : IsCoprime q x
  · rw [ite_eq_left hx,h.2 x hx]
  · rw [ite_eq_right hx]
    exact MulChar.map_nonunit χ (fun hu => hx (isCoprime_of_residue_isUnit hu))

lemma ResidueCharacterInduces.nonprincipal {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ)
    (hw : ∃ x : Eisenstein, IsCoprime q x ∧ χ (Ideal.Quotient.mk (modulus q) x) ≠ 1) :
    ψ ≠ 1 := by
  intro he
  obtain ⟨x,hx,hχx⟩ := hw
  have hdx := residue_isUnit_of_isCoprime (hx.of_isCoprime_of_dvd_left h.1)
  have hval := h.2 x hx
  rw [he,MulChar.one_apply hdx] at hval
  exact hχx hval.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

lemma ideal_coprime_support {q : Eisenstein} (hq : q ≠ 0)
    (ν : EisensteinIdealExponent) :
    IsCoprime q (idealExponentGenerator ν) ↔
      ∀ p ∈ (idealExponentOf q).support, ν p = 0 := by
  rw [isCoprime_comm,isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) hq,
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hn | hq
    · exact hn
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) hq)
  · intro h p
    by_cases hp : p ∈ (idealExponentOf q).support
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

lemma induced_residueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ν : EisensteinIdealExponent) :
    residueIdealChar q χ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
  simpa only [residueIdealChar,ideal_coprime_support hq] using
    h.restriction (idealExponentGenerator ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

lemma angular_character_associated {q x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hxy : Associated x y) :
    χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x =
      χ (Ideal.Quotient.mk (modulus q) y)*theta ℓ y := by
  obtain ⟨u,rfl⟩ := hxy
  rw [map_mul, map_mul, theta_mul]
  symm
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x)*
        (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u) := by ring
    _ = _ := by rw [hu u, mul_one]

lemma angularResidueIdealChar_at_element {q x : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hx : x ≠ 0) :
    angularResidueIdealChar q χ ℓ (idealExponentOf x) =
      χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x :=
  angular_character_associated χ hu (idealExponentOf_associated hx)

lemma induced_angularResidueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then
        angularResidueIdealChar d ψ ℓ ν else 0 := by
  rw [angularResidueIdealChar, induced_residueIdealChar hq h]
  split <;> simp [angularResidueIdealChar]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicReconstruction
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping on contracting dyads. Functions that vanish below
one have a finite, hence unambiguous, dyadic reconstruction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicDifference_sum (F : ℝ → ℂ) (X : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicDifference F (X/(2:ℝ)^j)) =
      F X-F (X/(2:ℝ)^N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold dyadicDifference
    have he : X/(2:ℝ)^N/2 = X/(2:ℝ)^(N+1) := by rw [pow_succ,div_div]
    rw [he]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite numerator character needed for arbitrary v in the
exceptional moments. The only conditional input here is the periodicity
consequence of cubic reciprocity and the unit/ramified supplementary laws:
Dunn–Radziwiłł (2024), equations (1.4)–(1.5). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicNumeratorLift_unit (v : Eisenstein) {x : Eisenstein} (hx : IsUnit x) :
    cubicNumeratorLift v x = 1 := by
  rw [cubicNumeratorLift,ite_eq_left (hx.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit hx,cubicSymbol_one_lower]

lemma cubicNumeratorChar_units (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (u : Eisensteinˣ) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) u) = 1 := by
  rw [cubicNumeratorChar_mk,cubicNumeratorLift_unit v u.isUnit]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeightTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rapid Mellin truncation with an explicit integrable moment. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma outside_interval_abs {T t : ℝ} (ht : t ∈ (Icc (-T) T)ᶜ) : T ≤ |t| := by
  by_contra h
  have ha : |t| < T := lt_of_not_ge h
  exact ht ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩

lemma weighted_height_tail (w : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T : ℝ} (hT : 0 < T) :
    (∫ t in (Icc (-T) T)ᶜ, ‖w t‖) ≤
      (∫ t : ℝ, |t|^A*‖w t‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall (fun _ => by positivity)))
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hT.le (outside_interval_abs ht) A) (_root_.norm_nonneg _)

lemma bounded_product_height_tail (w f : ℝ → ℂ) (hw : Integrable w) (A : ℕ)
    (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖)) {T B : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B) (hf : ∀ t, ‖f t‖ ≤ B) :
    ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      (B/T^A)*(∫ t : ℝ, |t|^A*‖w t‖) := by
  have hn : ‖∫ t in (Icc (-T) T)ᶜ, w t*f t‖ ≤
      B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hw.norm.restrict.const_mul B)
    filter_upwards with t
    rw [norm_mul,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf t) (_root_.norm_nonneg _)
  calc
    _ ≤ B*(∫ t in (Icc (-T) T)ᶜ, ‖w t‖) := hn
    _ ≤ B*((∫ t : ℝ, |t|^A*‖w t‖)/T^A) :=
      mul_le_mul_of_nonneg_left (weighted_height_tail w hw A hA hT) hB
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletHolomorphic
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphy and termwise differentiation of the complete ideal series
on its half-plane of absolute convergence. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma idealDirichlet_term_differentiable (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) :
    Differentiable ℂ (fun s : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
  let : NeZero (idealExponentNorm ν:ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'⟩
  exact (differentiable_const (χ ν)).mul
    ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg)

lemma idealDirichlet_uniform_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (ν : EisensteinIdealExponent)
    {s : ℂ} (hs : σ < s.re) :
    ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-σ) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
  exact Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (by linarith)

lemma idealDirichlet_term_hasDerivAt (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) (s : ℂ) :
    HasDerivAt (fun z : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-z))
      (χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*(idealExponentNorm ν:ℂ)^(-s)) s := by
  have hn : (idealExponentNorm ν:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
  have h := (((hasDerivAt_id s).neg).const_cpow (Or.inl hn)).const_mul (χ ν)
  rw [←Complex.ofReal_log (idealExponentNorm_pos ν).le] at h
  refine h.congr_deriv ?_
  · simp only [Pi.neg_apply,id_eq]
    ring

lemma idealDirichlet_hasSum_deriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun ν => χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*
      (idealExponentNorm ν:ℂ)^(-s)) (deriv (normDirichletSeries χ idealExponentNorm) s) := by
  have hσ : 1 < (1+s.re)/2 := by linarith
  have hm : (1+s.re)/2 < s.re := by linarith
  have h := Complex.hasSum_deriv_of_summable_norm (summable_ideal_norm_rpow hσ)
    (fun ν => (idealDirichlet_term_differentiable χ ν).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun ν z hz => idealDirichlet_uniform_bound χ hχ ν hz) hm
  simpa only [normDirichletSeries,(idealDirichlet_term_hasDerivAt χ _ _).deriv] using! h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDirichlet
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the logarithmically weighted ideal series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_ideal_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ν : EisensteinIdealExponent =>
      Real.log (idealExponentNorm ν)*idealExponentNorm ν^(-σ)) := by
  let ε : ℝ := (σ-1)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hmid : 1 < σ-ε := by dsimp [ε]; linarith
  apply ((summable_ideal_norm_rpow hmid).mul_left ε⁻¹).of_nonneg_of_le
    (fun ν => mul_nonneg (Real.log_nonneg (idealExponentNorm_ge_one ν))
      (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))
  intro ν
  have hp := idealExponentNorm_pos ν
  have h := mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp.le hε)
    (Real.rpow_nonneg hp.le (-σ))
  calc
    _ ≤ (idealExponentNorm ν^ε/ε)*idealExponentNorm ν^(-σ) := h
    _ = ε⁻¹*idealExponentNorm ν^(-(σ-ε)) := by
      rw [div_eq_mul_inv]
      calc
        _ = ε⁻¹*(idealExponentNorm ν^ε*idealExponentNorm ν^(-σ)) := by ring
        _ = _ := by rw [←Real.rpow_add hp]; congr 2; ring

lemma idealVonMangoldtDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν*
      (idealExponentNorm ν:ℂ)^(-s)‖) := by
  apply (summable_ideal_log_rpow hs).of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans (idealVonMangoldt_coeff_abs_le_logNorm ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic derivative of the complete ideal series is the
actual ideal von Mangoldt Dirichlet series on `Re(s)>1`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealVonMangoldt_antidiagonal (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))=(Real.log (idealExponentNorm ν):ℂ) := by
  have h := congrArg (MvPowerSeries.coeff ν) idealZeta_mul_vonMangoldt
  rw [MvPowerSeries.coeff_mul] at h
  simp only [MvPowerSeries.coeff_apply,idealZeta,one_mul,idealLogNorm] at h
  simpa only [Complex.ofReal_sum,MvPowerSeries.coeff_apply] using congrArg Complex.ofReal h

lemma idealVonMangoldt_twist_convolution (f : EisensteinIdealExponent → ℂ)
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2))=
        (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))*f ν := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2)=
          ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*(f p.1*f p.2) by ring,
        ←hfadd,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    _ = _ := by rw [idealVonMangoldt_antidiagonal]

lemma idealVonMangoldt_tsum_mul (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖))
    (hg : Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν‖))
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) :
    (∑' ν, f ν)*(∑' ν, ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν)=
      ∑' ν, (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2) :=
      ideal_cauchy_product _ _ hf hg
    _ = _ := tsum_congr (idealVonMangoldt_twist_convolution f hfadd)

theorem idealDirichlet_neg_logDeriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (normDirichletSeries χ idealExponentNorm) s=
      normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm s := by
  have hM := idealVonMangoldt_tsum_mul (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s))
    (idealDirichlet_norm_summable χ hχ hs)
    (by simpa only [mul_assoc] using idealVonMangoldtDirichlet_norm_summable χ hχ hs)
    (idealDirichlet_weight_add χ hχadd s)
  have hD := (idealDirichlet_hasSum_deriv χ hχ hs).tsum_eq
  have hlog : deriv (normDirichletSeries χ idealExponentNorm) s=
      -(∑' ν, (Real.log (idealExponentNorm ν):ℂ)*(χ ν*(idealExponentNorm ν:ℂ)^(-s))) := by
    rw [←hD,←tsum_neg]
    apply tsum_congr
    intro ν
    ring
  have hn := idealDirichlet_ne_zero χ hχ hχ0 hχadd hs
  rw [logDeriv_apply,hlog,neg_div,neg_neg,div_eq_iff hn]
  simpa only [normDirichletSeries,mul_assoc,mul_comm,mul_left_comm] using hM.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerPositivity
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative 3-4-1 combination for the actual ideal logarithmic
derivatives. This is the Euler-coefficient positivity used in the zero-free
argument, including the primes where a character vanishes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealMangoldt_term_re (χ : EisensteinIdealExponent → ℂ)
    (σ : ℝ) (ν : EisensteinIdealExponent) :
    ((((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*
      (idealExponentNorm ν:ℂ)^(-(σ:ℂ))).re =
      (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*idealExponentNorm ν^(-σ) := by
  rw [←Complex.ofReal_neg,←Complex.ofReal_cpow (idealExponentNorm_pos ν).le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_mul]

lemma idealMangoldt_real_hasSum (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun ν => (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*
      idealExponentNorm ν^(-σ))
      (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm (σ:ℂ)).re := by
  have hs := (idealVonMangoldtDirichlet_norm_summable χ hχ
    (s := (σ:ℂ)) (by simpa using hσ)).of_norm
  simpa only [normDirichletSeries,idealMangoldt_term_re] using! Complex.hasSum_re hs.hasSum

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivativeTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical translation and the zero-free positivity inequality for the
literal complete ideal series. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma idealSeries_logDeriv_eq {χ : EisensteinIdealExponent → ℂ} {L : ℂ → ℂ}
    (hseries : ∀ z : ℂ, 1 < z.re → L z=normDirichletSeries χ idealExponentNorm z)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv L s=logDeriv (normDirichletSeries χ idealExponentNorm) s := by
  have he : L =ᶠ[𝓝 s] normDirichletSeries χ idealExponentNorm := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hseries z hz
  exact (logDeriv_congr_nhds he).self_of_nhds

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin inversion of the actual character-twisted ideal von
Mangoldt sum, on its half-plane of absolute convergence. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem idealMangoldt_smooth_mellin
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    idealMangoldtSmooth χ W X=((1/(2*Real.pi):ℝ):ℂ)*
      ∫ t : ℝ, mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*(X:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)*
        (-logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  have habs : Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖*
      idealExponentNorm ν^(-σ)) := by
    have h := idealVonMangoldtDirichlet_norm_summable χ hχ
      (s := (σ:ℂ)) (by simpa using hσ)
    simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos _),
      Complex.neg_re,Complex.ofReal_re] using h
  rw [idealMangoldtSmooth,smooth_mellin_series _ _ idealExponentNorm_pos W hW hpos hsm σ habs hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  have hst : 1 < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by simpa using hσ
  rw [idealSeries_logDeriv_eq hs hst,idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd hst]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSchwartzWeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact logarithmic Schwartz profile gives an actual smooth norm
weight supported away from zero, with no loss in its logarithmic seminorms. -/
noncomputable section
open Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

lemma logSchwartzWeight_exp (H : 𝓢(ℝ,ℂ)) (u : ℝ) :
    logSchwartzWeight H (Real.exp (-u))=H u := by
  simp only [logSchwartzWeight,Real.exp_pos,ite_true, if_true,Real.log_exp,neg_neg]

lemma logSchwartzWeight_log_profile (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    mellinLogSchwartz (logSchwartzWeight H) (logSchwartzWeight_compact H hR)
      (logSchwartzWeight_positive_support H hR) (logSchwartzWeight_smooth H hR) 0=H := by
  ext u
  simp only [mellinLogSchwartz_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,
    logSchwartzWeight_exp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinFiniteSeminorm
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite seminorm control of vertical Mellin transforms. This keeps the
cost of a varying smooth cutoff visible instead of hiding it in a constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment

lemma mellinLogSchwartz_seminorm_cost {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤
        C*((Finset.Iic ((0,n) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
          (mellinLogSchwartz W hW hpos hsm 0) := by
  let A := ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*M^i*Real.exp (M*R)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨1+R^k*A,by positivity,?_⟩
  intro W hW hpos hsm hsupport σ hσ
  let G := mellinLogSchwartz W hW hpos hsm 0
  let B := ((Finset.Iic ((0,n) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) G
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg (i : ℕ) (hi : i ≤ n) (u : ℝ) : ‖iteratedFDeriv ℝ i G u‖ ≤ B := by
    apply (show ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G from by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u).trans
    exact Seminorm.le_def.mp (Finset.le_sup (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (show (0,i) ∈ Finset.Iic ((0,n) : ℕ × ℕ) from by simpa using hi)) G
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hfun : (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ)=
        fun v => Real.exp (-σ*v) • G v := by
      ext v
      simp [G,mellinLogSchwartz_apply]
    have hexp (i : ℕ) : ‖iteratedFDeriv ℝ i (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
        M^i*Real.exp (M*R) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
      simp only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ i) _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      calc
        -σ*u ≤ |-σ*u| := le_abs_self _
        _ = |σ| * |u| := by rw [abs_mul,abs_neg]
        _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ A*B := by
      rw [hfun]
      apply hd.trans
      dsimp [A]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _hi
      calc
        _ ≤ (n.choose i:ℝ)*(M^i*Real.exp (M*R))*B := by
          gcongr
          · exact hexp i
          · exact hg (n-i) (Nat.sub_le _ _) u
        _ = _ := by ring
    calc
      ‖u‖^k*‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ R^k*(A*B) := by
        rw [Real.norm_eq_abs]
        gcongr
      _ ≤ (1+R^k*A)*B := by nlinarith
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u=0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      exact hu (hsupport u hs')
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_finite_seminorm {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (I : Finset (ℕ × ℕ)) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      ∀ σ : ℝ, |σ| ≤ M →
      (I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinVerticalSchwartz W hW hpos hsm σ) ≤
      C*(J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinLogSchwartz W hW hpos hsm 0) := by
  let q : Seminorm ℝ 𝓢(ℝ,ℂ) := I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun i _ => (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s,C,hC,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ)
    (q.comp mellinVerticalCLM.toLinearMap) (hq.comp mellinVerticalCLM.continuous)
  choose D hD hd using fun i : ℕ × ℕ => mellinLogSchwartz_seminorm_cost hR hM i.1 i.2
  let J := s.biUnion (fun i => Finset.Iic ((0,i.2) : ℕ × ℕ))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ s) => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨J,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro W hW hpos hsm hsupport σ hσ
  let B := (J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
    (mellinLogSchwartz W hW hpos hsm 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      SchwartzMap.seminorm ℝ i.1 i.2 (mellinLogSchwartz W hW hpos hsm σ) ≤ E*B := by
    have hsub : Finset.Iic ((0,i.2) : ℕ × ℕ) ⊆ J := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hsup := Seminorm.le_def.mp (show
      (Finset.Iic ((0,i.2) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) ≤
        J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub)
      (mellinLogSchwartz W hW hpos hsm 0)
    have hDE : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ s) => (hD j).le) his
      dsimp [E]
      linarith
    exact (hd i W hW hpos hsm hsupport σ hσ).trans
      ((mul_le_mul_of_nonneg_left hsup (hD i).le).trans
        (mul_le_mul_of_nonneg_right hDE hB))
  have hsup : (s.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
      (mellinLogSchwartz W hW hpos hsm σ) ≤ E*B :=
    Seminorm.finset_sup_apply_le (by positivity) hi
  have ht := Seminorm.le_def.mp hb (mellinLogSchwartz W hW hpos hsm σ)
  change q (mellinVerticalSchwartz W hW hpos hsm σ) ≤
    (C:ℝ)*(s.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
      (mellinLogSchwartz W hW hpos hsm σ) at ht
  exact ht.trans (by
    change (C:ℝ)*_ ≤ (C:ℝ)*E*B
    nlinarith [C.coe_nonneg])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinPrimeControl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two Mellin moments and the edge decay needed for prime contour
shifts are controlled by finitely many norms of the logarithmic cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem primeMellinControl_finite_seminorm {R : ℝ} (hR : 0 ≤ R) :
    ∃ (J : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W)
      (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W),
      (∀ u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))), |u| ≤ R) →
      PrimeMellinControl W (C*(J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (mellinLogSchwartz W hW hpos hsm 0)) := by
  let n : ℕ := (volume : Measure ℝ).integrablePower
  let I : Finset (ℕ × ℕ) := Finset.Iic ((2,0) : ℕ × ℕ) ∪ {(0,0),(n,0),(2+n,0)}
  obtain ⟨J,C,hC,hbound⟩ := mellinVertical_finite_seminorm hR (by norm_num : (0:ℝ) ≤ 2) I
  let A : ℝ := 2^n*(∫ t : ℝ, (1+‖t‖)^(-(n:ℝ)))
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  refine ⟨J,(4+2*A)*C,by positivity,?_⟩
  intro W hW hpos hsm hsupport
  let B := (J.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
    (mellinLogSchwartz W hW hpos hsm 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI (σ : ℝ) (hσ : |σ| ≤ 2) := hbound W hW hpos hsm hsupport σ hσ
  have hsem (σ : ℝ) (hσ : |σ| ≤ 2) (i : ℕ × ℕ) (hi : i ∈ I) :
      SchwartzMap.seminorm ℝ i.1 i.2 (mellinVerticalSchwartz W hW hpos hsm σ) ≤ C*B :=
    (Seminorm.le_def.mp (Finset.le_sup (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) hi)
      _).trans (hI σ hσ)
  have hm (σ : ℝ) (hσ : |σ| ≤ 2) (k : ℕ) (hk : (k+n,0) ∈ I) :
      (∫ t : ℝ, |t|^k*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) ≤ 2*A*C*B := by
    let F := mellinVerticalSchwartz W hW hpos hsm σ
    have hb := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume F k 0
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
    change (∫ t : ℝ, |t|^k*‖F t‖) ≤
      A*(SchwartzMap.seminorm ℝ 0 0 F+SchwartzMap.seminorm ℝ (k+n) 0 F) at hb
    have he : (∫ t : ℝ, |t|^k*‖F t‖) =
        ∫ t : ℝ, |t|^k*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ := by
      simp only [F,mellinVerticalSchwartz_apply]
    rw [he] at hb
    have hz := hsem σ hσ (0,0) (by simp [I])
    have hh := hsem σ hσ (k+n,0) hk
    exact hb.trans (by dsimp [F] at *; nlinarith)
  refine ⟨by positivity,?_,?_,?_⟩
  · intro σ hσ t
    have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
    have hsub : Finset.Iic ((2,0) : ℕ × ℕ) ⊆ I := Finset.subset_union_left
    have hs := Seminorm.le_def.mp (show
      (Finset.Iic ((2,0) : ℕ × ℕ)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) ≤
        I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub)
      (mellinVerticalSchwartz W hW hpos hsm σ)
    have hh := hI σ hσ
    dsimp [B] at *
    nlinarith [mul_nonneg hA (mul_nonneg hC.le hB)]
  · intro σ hσ
    have h := hm σ hσ 0 (by simp [I])
    simp only [pow_zero,one_mul] at h
    dsimp [B] at *
    nlinarith
  · intro σ hσ
    have h := hm σ hσ 2 (by simp [I])
    dsimp [B] at *
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShrinkingProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial seminorm costs for affine shrinking of a fixed cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

lemma iteratedFDeriv_comp_sub_real (f : ℝ → ℂ) (c : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f (x-c)) = fun x => iteratedFDeriv ℝ n f (x-c) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    funext x
    simp only [iteratedFDeriv_succ_eq_comp_left,ih,Function.comp_apply,fderiv_comp_sub]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSmoothTransition
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded derivatives of the fixed smooth step, before narrowing the
transition in the logarithmic prime cutoff. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma primeSmoothStep_norm (x : ℝ) : ‖primeSmoothStep x‖ ≤ 1 := by
  rw [primeSmoothStep,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma primeSmoothStep_derivatives_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n primeSmoothStep x‖ ≤ C := by
  cases n with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [norm_iteratedFDeriv_zero] using primeSmoothStep_norm x
  | succ n =>
    refine ⟨SchwartzMap.seminorm ℝ 0 n primeSmoothStepDerivative,by positivity,?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_succ']
    have h := SchwartzMap.le_seminorm ℝ 0 n primeSmoothStepDerivative x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_eq_norm_iteratedDeriv] using! h

lemma smoothStep_affine_deriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J c x : ℝ), 0 ≤ J →
      ‖iteratedFDeriv ℝ n (fun y => primeSmoothStep (J*(y-c))) x‖ ≤ C*J^n := by
  obtain ⟨C,hC,hb⟩ := primeSmoothStep_derivatives_bounded n
  refine ⟨C,hC,?_⟩
  intro J c x hJ
  have he : (fun y => primeSmoothStep (J*(y-c)))=
      fun y => (fun z => primeSmoothStep (J • z)) (y-c) := rfl
  rw [he,iteratedFDeriv_comp_sub_real (fun z : ℝ => primeSmoothStep (J • z)) c n,
    iteratedFDeriv_comp_const_smul J (primeSmoothStep_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    norm_smul,Real.norm_eq_abs,abs_pow,abs_of_nonneg hJ]
  simpa only [smul_eq_mul,mul_comm C] using mul_le_mul_of_nonneg_left (hb (J*(x-c))) (pow_nonneg hJ n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine smooth approximation to the dyadic interval in logarithmic
coordinates. The two endpoint transitions have width exactly 1/J. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma primeLogWindow_one {J u : ℝ} (hJ : 0 ≤ J)
    (hu : -Real.log 2 ≤ u ∧ u ≤ 0) : primeLogWindow J u=1 := by
  have hlo : 1 ≤ J*(u+Real.log 2)+1 := by nlinarith
  have hhi : J*u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hJ hu.2
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.one_of_one_le hlo,
    Real.smoothTransition.zero_of_nonpos hhi,Complex.ofReal_one,Complex.ofReal_zero,sub_zero]

lemma primeLogWindow_tsupport {J : ℝ} (hJ : 0 < J) :
    tsupport (primeLogWindow J) ⊆ Icc (-Real.log 2-1/J) (1/J) :=
  closure_minimal (primeLogWindow_support hJ) isClosed_Icc

lemma primeLogWindow_support_two {J u : ℝ} (hJ : 1 ≤ J)
    (hu : u ∈ tsupport (primeLogWindow J)) : |u| ≤ 2 := by
  have hp : 0 < J := by linarith
  have hi : 1/J ≤ 1 := (div_le_one hp).mpr hJ
  have hl : Real.log 2 ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  obtain ⟨hhlo,hhhi⟩ := primeLogWindow_tsupport hp hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma primeLogWindow_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J u : ℝ, 1 ≤ J →
      ‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ C*J^n := by
  obtain ⟨C,hC,hb⟩ := smoothStep_affine_deriv_bound n
  refine ⟨2*C,by positivity,?_⟩
  intro J u hJ
  have hp : 0 < J := by linarith
  let c : ℝ := -Real.log 2-1/J
  have he : primeLogWindow J=(fun y => primeSmoothStep (J*(y-c)))-
      (fun y => primeSmoothStep (J*(y-0))) := by
    funext y
    have hh : J*(y-c)=J*(y+Real.log 2)+1 := by dsimp [c]; field_simp; ring
    simp only [primeLogWindow,Pi.sub_apply,hh,sub_zero]
  have hf : ContDiff ℝ n (fun y : ℝ => primeSmoothStep (J*(y-c))) :=
    (primeSmoothStep_smooth.comp (by fun_prop)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg : ContDiff ℝ n (fun y : ℝ => primeSmoothStep (J*(y-0))) :=
    (primeSmoothStep_smooth.comp (by fun_prop)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [he,iteratedFDeriv_sub hf hg,Pi.sub_apply]
  exact (norm_sub_le _ _).trans (by nlinarith [hb J c u hp.le,hb J 0 u hp.le])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogWindowCost
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial finite-seminorm cost of the actual narrowing cutoff. -/
noncomputable section
open scoped ContDiff SchwartzMap BigOperators
namespace CubicFirstMoment

lemma primeLogWindow_seminorm_bound (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      SchwartzMap.seminorm ℝ k n (primeLogWindowSchwartz J (by linarith)) ≤ C*J^n := by
  obtain ⟨C,hC,hder⟩ := primeLogWindow_derivative_bound n
  refine ⟨2^k*C,by positivity,?_⟩
  intro J hJ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2
  · have hb := hder J u hJ
    change ‖u‖^k*‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2^k*(C*J^n) := mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) hu k) hb (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (primeLogWindow J) u=0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := primeLogWindow J) n hn
      exact hu (primeLogWindow_support_two hJ hs)
    change ‖u‖^k*‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ _
    rw [hz,norm_zero,mul_zero]
    positivity

theorem primeLogWindow_finite_cost (I : Finset (ℕ × ℕ)) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      (I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (primeLogWindowSchwartz J (by linarith)) ≤ K*J^d := by
  classical
  choose C hC hb using fun m : ℕ × ℕ => primeLogWindow_seminorm_bound m.1 m.2
  let d := I.sup Prod.snd
  let K := 1+∑ m ∈ I, C m
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun m (_ : m ∈ I) => hC m)
    dsimp [K]
    linarith
  refine ⟨d,K,hK,?_⟩
  intro J hJ
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro m hm
  have hn : m.2 ≤ d := Finset.le_sup (f := Prod.snd) hm
  have hmK : C m ≤ K := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ I) => hC j) hm
    dsimp [K]
    linarith
  exact (hb m J hJ).trans
    (mul_le_mul hmK (pow_le_pow_right₀ hJ hn) (by positivity) hK.le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth dyadic norm cutoff, with a polynomial bound on all
Mellin quantities needed in the prime contour argument. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma primeLogWindow_norm {J : ℝ} (hJ : 0 ≤ J) (u : ℝ) : ‖primeLogWindow J u‖ ≤ 1 := by
  have hm : Real.smoothTransition (J*u) ≤ Real.smoothTransition (J*(u+Real.log 2)+1) := by
    apply Real.smoothTransition.monotone
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hp := Real.smoothTransition.le_one (J*(u+Real.log 2)+1)
  have hz := Real.smoothTransition.nonneg (J*u)
  rw [primeLogWindow,primeSmoothStep,primeSmoothStep,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hm)]
  linarith

lemma primeLogWindowSchwartz_support_two {J : ℝ} (hJ : 1 ≤ J) :
    ∀ u ∈ tsupport (primeLogWindowSchwartz J (by linarith) : ℝ → ℂ), |u| ≤ 2 :=
  fun _u hu => primeLogWindow_support_two hJ hu

lemma primeDyadicWeight_compact {J : ℝ} (hJ : 1 ≤ J) :
    HasCompactSupport (primeDyadicWeight J hJ) :=
  logSchwartzWeight_compact _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_positive_support {J : ℝ} (hJ : 1 ≤ J) :
    tsupport (primeDyadicWeight J hJ) ⊆ Ioi 0 :=
  logSchwartzWeight_positive_support _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_smooth {J : ℝ} (hJ : 1 ≤ J) :
    ContDiff ℝ ∞ (primeDyadicWeight J hJ) :=
  logSchwartzWeight_smooth _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_exp {J : ℝ} (hJ : 1 ≤ J) (u : ℝ) :
    primeDyadicWeight J hJ (Real.exp (-u))=primeLogWindow J u :=
  logSchwartzWeight_exp _ u

lemma primeDyadicWeight_one {J x : ℝ} (hJ : 1 ≤ J) (hx : 1 ≤ x ∧ x ≤ 2) :
    primeDyadicWeight J hJ x=1 := by
  have hxp : 0 < x := by linarith
  change (if 0 < x then primeLogWindow J (-Real.log x) else 0)=1
  rw [ite_eq_left hxp]
  apply primeLogWindow_one (by linarith)
  have hl0 := Real.log_nonneg hx.1
  have hl2 := Real.log_le_log hxp hx.2
  exact ⟨by linarith,by linarith⟩

lemma primeDyadicWeight_norm {J : ℝ} (hJ : 1 ≤ J) (x : ℝ) :
    ‖primeDyadicWeight J hJ x‖ ≤ 1 := by
  change ‖if 0 < x then primeLogWindow J (-Real.log x) else 0‖ ≤ 1
  split_ifs
  · exact primeLogWindow_norm (by linarith) _
  · norm_num

lemma PrimeMellinControl.mono {W : ℝ → ℂ} {D E : ℝ}
    (hD : PrimeMellinControl W D) (hDE : D ≤ E) : PrimeMellinControl W E :=
  ⟨hD.nonneg.trans hDE,fun σ hσ t => (hD.decay σ hσ t).trans hDE,
    fun σ hσ => (hD.mass σ hσ).trans hDE,fun σ hσ => (hD.moment σ hσ).trans hDE⟩

theorem primeDyadicWeight_mellin_control :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      PrimeMellinControl (primeDyadicWeight J hJ) (K*J^d) := by
  obtain ⟨I,C,hC,hcontrol⟩ := primeMellinControl_finite_seminorm (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨d,K,hK,hcost⟩ := primeLogWindow_finite_cost I
  refine ⟨d,C*K,mul_pos hC hK,?_⟩
  intro J hJ
  have hfun : (fun u : ℝ => primeDyadicWeight J hJ (Real.exp (-u)))=primeLogWindow J :=
    funext (primeDyadicWeight_exp hJ)
  have hc := hcontrol (primeDyadicWeight J hJ) (primeDyadicWeight_compact hJ)
    (primeDyadicWeight_positive_support hJ) (primeDyadicWeight_smooth hJ) (by
      rw [hfun]
      exact fun u hu => primeLogWindow_support_two hJ hu)
  have he := logSchwartzWeight_log_profile _ (primeLogWindowSchwartz_support_two hJ)
  change mellinLogSchwartz (primeDyadicWeight J hJ) _ _ _ 0=primeLogWindowSchwartz J _ at he
  rw [he] at hc
  apply hc.mono
  calc
    _ ≤ C*(K*J^d) := mul_le_mul_of_nonneg_left (hcost J hJ) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicBoundary
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localization of the smoothing error to the two endpoint annuli. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDyadicWeight_support_interval {J x : ℝ} (hJ : 1 ≤ J)
    (hx : primeDyadicWeight J hJ x ≠ 0) :
    Real.exp (-1/J) ≤ x ∧ x ≤ 2*Real.exp (1/J) := by
  have hxp : 0 < x := by
    by_contra h
    have hn : ¬0 < x := h
    exact hx (by change (if 0 < x then _ else 0)=0; rw [ite_eq_right hn])
  have hn : primeLogWindow J (-Real.log x) ≠ 0 := by
    change (if 0 < x then primeLogWindow J (-Real.log x) else 0) ≠ 0 at hx
    rwa [ite_eq_left hxp] at hx
  obtain ⟨hl,hr⟩ := primeLogWindow_support (by linarith) hn
  constructor
  · have h := Real.exp_le_exp.mpr (show -1/J ≤ Real.log x by simpa only [neg_div] using (show -(1/J) ≤ Real.log x by linarith))
    rwa [Real.exp_log hxp] at h
  · have h := Real.exp_le_exp.mpr (show Real.log x ≤ Real.log 2+1/J by linarith)
    rw [Real.exp_log hxp,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at h
    exact h

theorem primeDyadicWeight_boundary_error {α : Type*} (S : Finset α)
    (N : α → ℝ) (c : α → ℂ) {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X) :
    ‖(∑ ν ∈ S, c ν*primeDyadicWeight J hJ (N ν/X))-
      (∑ ν ∈ S with X ≤ N ν ∧ N ν ≤ 2*X, c ν)‖ ≤
    ∑ ν ∈ S with
      (Real.exp (-1/J)*X ≤ N ν ∧ N ν < X) ∨
      (2*X < N ν ∧ N ν ≤ 2*Real.exp (1/J)*X), ‖c ν‖ := by
  have he : (∑ ν ∈ S, c ν*primeDyadicWeight J hJ (N ν/X))-
      (∑ ν ∈ S with X ≤ N ν ∧ N ν ≤ 2*X, c ν)=
      ∑ ν ∈ S, if X ≤ N ν ∧ N ν ≤ 2*X then 0 else
        c ν*primeDyadicWeight J hJ (N ν/X) := by
    rw [Finset.sum_filter,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hi : X ≤ N ν ∧ N ν ≤ 2*X
    · have hw := primeDyadicWeight_one hJ
        (show 1 ≤ N ν/X ∧ N ν/X ≤ 2 by
          constructor
          · exact (le_div_iff₀ hX).mpr (by simpa using hi.1)
          · exact (div_le_iff₀ hX).mpr hi.2)
      simp [hi,hw]
    · simp only [hi,ite_false, if_false,sub_zero]
  rw [he,Finset.sum_filter]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν hν
  by_cases hi : X ≤ N ν ∧ N ν ≤ 2*X
  · simp only [hi,true_and,ite_true, if_true,norm_zero]
    split_ifs <;> positivity
  · simp only [hi,ite_false, if_false]
    by_cases hw : primeDyadicWeight J hJ (N ν/X)=0
    · simp only [hw,mul_zero,norm_zero]
      split_ifs <;> positivity
    · obtain ⟨hl,hr⟩ := primeDyadicWeight_support_interval hJ hw
      have hl' : Real.exp (-1/J)*X ≤ N ν := (le_div_iff₀ hX).mp hl
      have hr' : N ν ≤ 2*Real.exp (1/J)*X := (div_le_iff₀ hX).mp hr
      have hb : (Real.exp (-1/J)*X ≤ N ν ∧ N ν < X) ∨
          (2*X < N ν ∧ N ν ≤ 2*Real.exp (1/J)*X) := by
        by_cases hlo : N ν < X
        · exact Or.inl ⟨hl',hlo⟩
        · exact Or.inr ⟨lt_of_not_ge (fun h => hi ⟨le_of_not_gt hlo,h⟩),hr'⟩
      rw [ite_eq_left hb,norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (primeDyadicWeight_norm hJ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThinAnnulusCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine thin-annulus lattice count. Disjoint half-unit disks
around Eisenstein integers fit inside the thickened annulus. -/
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_dist_ge_one {a b : Eisenstein} (hab : a ≠ b) :
    1 ≤ dist (a:ℂ) (b:ℂ) := by
  have hn := one_le_norm (sub_ne_zero.mpr hab)
  rw [norm,Subalgebra.coe_sub,Complex.normSq_eq_norm_sq] at hn
  rw [dist_eq_norm]
  nlinarith [_root_.norm_nonneg ((a:ℂ)-(b:ℂ))]

lemma complex_ball_real_volume (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball z r) = r^2*Real.pi := by
  simp only [measureReal_def,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.coe_toReal,NNReal.coe_real_pi]

theorem eisenstein_annulus_card (S : Finset Eisenstein) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ a ∈ S, A ≤ norm a ∧ norm a ≤ B) :
    (S.card:ℝ) ≤ 4*(B-A+Real.sqrt B+Real.sqrt A) := by
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := hA0.trans hAB
  let r := Real.sqrt A-1/2
  let R := Real.sqrt B+1/2
  have hsqA := Real.sq_sqrt hA0
  have hsqB := Real.sq_sqrt hB0
  have hsA := Real.sqrt_nonneg A
  have hsB := Real.sqrt_nonneg B
  have hr : 0 ≤ r := by dsimp [r]; nlinarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrR : r ≤ R := by
    dsimp [r,R]
    linarith [Real.sqrt_le_sqrt hAB]
  let U : Set ℂ := ⋃ a ∈ S, ball (a:ℂ) (1/2)
  have hdisj : PairwiseDisjoint (S:Set Eisenstein)
      (fun a => ball (a:ℂ) (1/2:ℝ)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by convert eisenstein_dist_ge_one hab using 1; norm_num)
  have hsub : U ⊆ ball (0:ℂ) R \ ball 0 r := by
    intro z hz
    obtain ⟨a,ha,hz⟩ := mem_iUnion₂.mp hz
    have haN := hS a ha
    have haL : Real.sqrt A ≤ ‖(a:ℂ)‖ := by
      have hn := haN.1
      rw [norm,Complex.normSq_eq_norm_sq] at hn
      nlinarith [_root_.norm_nonneg (a:ℂ)]
    have haU : ‖(a:ℂ)‖ ≤ Real.sqrt B := by
      have hn := haN.2
      rw [norm,Complex.normSq_eq_norm_sq] at hn
      nlinarith [_root_.norm_nonneg (a:ℂ)]
    have hz' : dist z (a:ℂ) < (1/2:ℝ) := hz
    refine ⟨?_,?_⟩
    · change dist z 0 < R
      have ht := dist_triangle z (a:ℂ) 0
      simp only [dist_zero_right] at ht ⊢
      dsimp [R]
      linarith
    · intro hz0
      have hz0' : dist z 0 < r := hz0
      have ht := dist_triangle (a:ℂ) z 0
      rw [dist_comm (a:ℂ) z] at ht
      simp only [dist_zero_right] at ht hz0'
      dsimp [r] at hz0'
      linarith
  have hvolU : volume.real U = (S.card:ℝ)*((1/2:ℝ)^2*Real.pi) := by
    rw [show U = ⋃ a ∈ S, ball (a:ℂ) (1/2:ℝ) from rfl,
      measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    simp only [complex_ball_real_volume _ (by norm_num : (0:ℝ) ≤ 1/2),
      Finset.sum_const,nsmul_eq_mul]
  have hfin : volume (ball (0:ℂ) R) ≠ ⊤ := by
    rw [Complex.volume_ball]
    finiteness
  have hvol : volume.real U ≤ (R^2-r^2)*Real.pi := by
    apply (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hfin)).trans_eq
    rw [measureReal_sdiff (ball_subset_ball hrR) measurableSet_ball hfin,
      complex_ball_real_volume _ hR,complex_ball_real_volume _ hr]
    ring
  rw [hvolU] at hvol
  have hp := Real.pi_pos
  have he : R^2-r^2 = B-A+Real.sqrt B+Real.sqrt A := by
    dsimp [R,r]
    nlinarith
  rw [he] at hvol
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lattice annulus estimate for actual ideals, and its von Mangoldt
weighted form. Injectivity of the canonical generator retains multiplicity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem idealExponent_annulus_card (S : Finset EisensteinIdealExponent) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ ν ∈ S, A ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ B) :
    (S.card:ℝ) ≤ 4*(B-A+Real.sqrt B+Real.sqrt A) := by
  have hc := eisenstein_annulus_card (S.image idealExponentGenerator) hA hAB (by
    intro a ha
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp ha
    simpa only [idealExponentNorm, normNat_cast] using hS ν hν)
  rw [Finset.card_image_of_injective _ idealExponentGenerator_injective] at hc
  exact hc

theorem idealMangoldt_annulus_mass (S : Finset EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ ν ∈ S, A ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ B) :
    (∑ ν ∈ S, ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖) ≤
      4*(B-A+Real.sqrt B+Real.sqrt A)*Real.log B := by
  have hB : 1 ≤ B := hA.trans hAB
  calc
    _ ≤ ∑ _ν ∈ S, Real.log B := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      calc
        _ ≤ |(MvPowerSeries.coeff ν idealVonMangoldt:ℝ)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hχ ν)
        _ ≤ Real.log (idealExponentNorm ν) := idealVonMangoldt_coeff_abs_le_logNorm ν
        _ ≤ Real.log B := Real.log_le_log (idealExponentNorm_pos ν) (hS ν hν).2
    _ = (S.card:ℝ)*Real.log B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (idealExponent_annulus_card S hA hAB hS)
      (Real.log_nonneg hB)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtDyadic
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sharp dyadic ideal sums and the two endpoint errors of the
logarithmic smooth cutoff. All ideals, including those above three, remain. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealMangoldtDyadic_eq_sum (χ : EisensteinIdealExponent → ℂ)
    {X B : ℝ} (hB : 2*X ≤ B) :
    idealMangoldtDyadic χ X =
      ∑ ν ∈ fullIdealBall B with X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtDyadic
  congr 1
  ext ν
  simp only [Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨hhi,hlo⟩
    exact ⟨hhi.trans hB,hlo,hhi⟩
  · rintro ⟨_,hlo,hhi⟩
    exact ⟨hhi,hlo⟩

lemma idealMangoldtSmooth_dyadic_eq_sum (χ : EisensteinIdealExponent → ℂ)
    {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X) :
    idealMangoldtSmooth χ (primeDyadicWeight J hJ) X =
      ∑ ν ∈ fullIdealBall (2*Real.exp (1/J)*X),
        (((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*
          primeDyadicWeight J hJ (idealExponentNorm ν/X) := by
  apply tsum_eq_sum
  intro ν hν
  have hw : primeDyadicWeight J hJ (idealExponentNorm ν/X)=0 := by
    by_contra hn
    have hh := (primeDyadicWeight_support_interval hJ hn).2
    exact hν (mem_fullIdealBall.mpr ((div_le_iff₀ hX).mp hh))
  rw [hw,mul_zero]

theorem idealMangoldt_dyadic_smoothing_error (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J X : ℝ} (hJ : 1 ≤ J) (hX : 0 < X)
    (hlo : 1 ≤ Real.exp (-1/J)*X) :
    ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ ≤
      4*(X-Real.exp (-1/J)*X+Real.sqrt X+Real.sqrt (Real.exp (-1/J)*X))*Real.log X+
      4*(2*Real.exp (1/J)*X-2*X+Real.sqrt (2*Real.exp (1/J)*X)+Real.sqrt (2*X))*
        Real.log (2*Real.exp (1/J)*X) := by
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have he : 1 ≤ Real.exp (1/J) := Real.one_le_exp (by positivity)
  have he' : Real.exp (-1/J) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hJ0.le)
  have hAX : Real.exp (-1/J)*X ≤ X := mul_le_of_le_one_left hX.le he'
  have hXB : 2*X ≤ 2*Real.exp (1/J)*X := by nlinarith
  have hX1 : 1 ≤ X := hlo.trans hAX
  let S := fullIdealBall (2*Real.exp (1/J)*X)
  let c := fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν
  rw [idealMangoldtSmooth_dyadic_eq_sum χ hJ hX,idealMangoldtDyadic_eq_sum χ hXB]
  apply (primeDyadicWeight_boundary_error S idealExponentNorm c hJ hX).trans
  have hs : (∑ ν ∈ S with
      (Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν < X) ∨
      (2*X < idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*Real.exp (1/J)*X), ‖c ν‖) ≤
      (∑ ν ∈ S with Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ X, ‖c ν‖)+
      (∑ ν ∈ S with 2*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*Real.exp (1/J)*X, ‖c ν‖) := by
    rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ν hν
    by_cases hL : Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν < X
    · have hLc : Real.exp (-1/J)*X ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ X :=
        ⟨hL.1,hL.2.le⟩
      rw [ite_eq_left (Or.inl hL),ite_eq_left hLc]
      split_ifs <;> simp only [add_zero,le_add_iff_nonneg_right,_root_.norm_nonneg,le_refl]
    · by_cases hR : 2*X < idealExponentNorm ν ∧
          idealExponentNorm ν ≤ 2*Real.exp (1/J)*X
      · have hRc : 2*X ≤ idealExponentNorm ν ∧
            idealExponentNorm ν ≤ 2*Real.exp (1/J)*X := ⟨hR.1.le,hR.2⟩
        rw [ite_eq_left (Or.inr hR),ite_eq_left hRc]
        split_ifs <;> simp only [zero_add,le_add_iff_nonneg_left,_root_.norm_nonneg,le_refl]
      · rw [ite_eq_right (not_or.mpr ⟨hL,hR⟩)]
        split_ifs <;> positivity
  apply hs.trans
  apply add_le_add
  · apply idealMangoldt_annulus_mass _ χ hχ hlo hAX
    intro ν hν
    exact (Finset.mem_filter.mp hν).2
  · apply idealMangoldt_annulus_mass _ χ hχ (by linarith) hXB
    intro ν hν
    exact (Finset.mem_filter.mp hν).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtPrefix
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete ideal von Mangoldt prefixes, exact half-open dyadic
increments, and the cost of their closed lower endpoints. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma fullIdealBall_sum_on {A B : ℝ} (hAB : A ≤ B)
    (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ fullIdealBall A, f ν) =
      ∑ ν ∈ fullIdealBall B, if idealExponentNorm ν ≤ A then f ν else 0 := by
  have hs : fullIdealBall A = (fullIdealBall B).filter (fun ν => idealExponentNorm ν ≤ A) := by
    ext ν
    simp only [Finset.mem_filter,mem_fullIdealBall]
    exact ⟨fun h => ⟨h.trans hAB,h⟩,And.right⟩
  rw [hs,Finset.sum_filter]

lemma idealMangoldtSum_dyadic (χ : EisensteinIdealExponent → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    idealMangoldtSum χ (2*X)-idealMangoldtSum χ X = idealMangoldtDyadic χ X-
      ∑ ν ∈ fullIdealBall (2*X) with idealExponentNorm ν = X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtSum idealMangoldtDyadic
  rw [fullIdealBall_sum_on (show X ≤ 2*X by linarith),
    ←Finset.sum_sub_distrib,Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  by_cases he : idealExponentNorm ν = X
  · simp [he]
  · by_cases hlo : idealExponentNorm ν ≤ X
    · have hn : ¬X ≤ idealExponentNorm ν := fun h => he (le_antisymm hlo h)
      simp [he,hlo,hn]
    · have hl : X ≤ idealExponentNorm ν := (lt_of_not_ge hlo).le
      simp [he,hlo,hl]

lemma idealMangoldt_boundary_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X B : ℝ} (hX : 1 ≤ X) :
    ‖∑ ν ∈ fullIdealBall B with idealExponentNorm ν = X,
      ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ ≤
      8*Real.sqrt X*Real.log X := by
  apply (norm_sum_le _ _).trans
  have hh := idealMangoldt_annulus_mass
    ((fullIdealBall B).filter (fun ν => idealExponentNorm ν = X)) χ hχ hX le_rfl (by
      intro ν hν
      have he := (Finset.mem_filter.mp hν).2
      exact ⟨he.ge,he.le⟩)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma idealMangoldtSum_norm_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖idealMangoldtSum χ X‖ ≤ 8*X*Real.log X := by
  have hh := idealMangoldt_annulus_mass (fullIdealBall X) χ hχ (by norm_num : (1:ℝ) ≤ 1) hX
    (fun ν hν => ⟨idealExponentNorm_ge_one ν,mem_fullIdealBall.mp hν⟩)
  have hs : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith,by nlinarith⟩
  calc
    _ ≤ ∑ ν ∈ fullIdealBall X, ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ := norm_sum_le _ _
    _ ≤ 4*(X-1+Real.sqrt X+Real.sqrt 1)*Real.log X := hh
    _ ≤ _ := by
      norm_num only [Real.sqrt_one]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimePowerCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct count of higher prime-ideal powers in the complete norm ball.
The map from a prime base and its exponent is used only for an upper bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma fullIdealBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((fullIdealBall X).card:ℝ) ≤ 18*X := by
  apply (Nat.cast_le.mpr (Finset.card_image_le)).trans
  exact nonzeroNormBall_card_le hX

lemma idealPrimePower_exponent_bound {ν : EisensteinIdealExponent} {X : ℝ}
    (hν : ν ∈ fullIdealBall X) (p : EisensteinIdealPrime) :
    ν p ≤ Nat.log 2 ⌊X⌋₊ := by
  have hh := idealExponentOf_le_log_norm (idealExponentGenerator_ne_zero ν) p
  rw [idealExponentOf_generator] at hh
  apply hh.trans
  apply Nat.log_mono_right
  exact Nat.le_floor (mem_fullIdealBall.mp hν)

lemma higherIdealPrimePowers_subset {X : ℝ} (hX : 0 ≤ X) :
    higherIdealPrimePowers X ⊆
      ((fullIdealBall (Real.sqrt X)).product (Finset.range (Nat.log 2 ⌊X⌋₊+1))).image
        (fun v : EisensteinIdealExponent × ℕ => v.2 • v.1) := by
  intro ν hν
  obtain ⟨hball,p,j,hj,rfl⟩ := Finset.mem_filter.mp hν
  have hnorm : (normNat (idealPrimeRepresentative p):ℝ)^j ≤ X := by
    simpa only [mem_fullIdealBall,idealExponentNorm_single] using hball
  have hbase : 1 ≤ (normNat (idealPrimeRepresentative p):ℝ) := by
    exact_mod_cast (show 1 ≤ normNat (idealPrimeRepresentative p) from
      (by have := idealPrimeRepresentative_normNat_ge_two p; omega))
  have hsq : (normNat (idealPrimeRepresentative p):ℝ)^2 ≤ X :=
    (pow_le_pow_right₀ hbase hj).trans hnorm
  have hsmall : Finsupp.single p 1 ∈ fullIdealBall (Real.sqrt X) := by
    rw [mem_fullIdealBall,idealExponentNorm_single,pow_one]
    exact (Real.le_sqrt (by positivity) hX).mpr hsq
  have hlarge := idealPrimePower_exponent_bound hball p
  simp only [Finsupp.single_eq_same] at hlarge
  refine Finset.mem_image.mpr ⟨(Finsupp.single p 1,j),
    Finset.mem_product.mpr ⟨hsmall,Finset.mem_range.mpr (by omega)⟩,?_⟩
  ext q
  by_cases hq : q=p
  · subst q
    simp
  · simp [hq]

theorem higherIdealPrimePowers_card {X : ℝ} (hX : 0 ≤ X) :
    ((higherIdealPrimePowers X).card:ℝ) ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1) := by
  have hh := Finset.card_le_card (higherIdealPrimePowers_subset hX)
  have hi : ((higherIdealPrimePowers X).card:ℝ) ≤
      (((fullIdealBall (Real.sqrt X)).product
        (Finset.range (Nat.log 2 ⌊X⌋₊+1))).card:ℝ) := by
    exact_mod_cast hh.trans (Finset.card_image_le)
  have hcard : ((fullIdealBall (Real.sqrt X)).product
      (Finset.range (Nat.log 2 ⌊X⌋₊+1))).card =
      (fullIdealBall (Real.sqrt X)).card*(Nat.log 2 ⌊X⌋₊+1) := by
    exact (Finset.card_product _ _).trans (by rw [Finset.card_range])
  rw [hcard,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right (fullIdealBall_card_le (Real.sqrt_nonneg X)) (by positivity))

theorem higherIdealPrimePowers_mass (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    (∑ ν ∈ higherIdealPrimePowers X,
      ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖) ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1)*Real.log X := by
  calc
    _ ≤ ∑ _ν ∈ higherIdealPrimePowers X, Real.log X := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      calc
        _ ≤ |(MvPowerSeries.coeff ν idealVonMangoldt:ℝ)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hχ ν)
        _ ≤ Real.log (idealExponentNorm ν) := idealVonMangoldt_coeff_abs_le_logNorm ν
        _ ≤ Real.log X := Real.log_le_log (idealExponentNorm_pos ν)
          (mem_fullIdealBall.mp (Finset.mem_filter.mp hν).1)
    _ = ((higherIdealPrimePowers X).card:ℝ)*Real.log X := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (higherIdealPrimePowers_card (by linarith)) (Real.log_nonneg hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimeReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of prime ideals from higher prime powers in the
actual von Mangoldt prefix. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealVonMangoldt_single_prime (p : EisensteinIdealPrime) :
    MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt =
      Real.log (idealExponentNorm (Finsupp.single p 1)) := by
  simpa only [zero_add,idealExponentNorm_single,pow_one] using idealVonMangoldt_prime_power p 0

lemma idealVonMangoldt_support (ν : EisensteinIdealExponent)
    (hν : MvPowerSeries.coeff ν idealVonMangoldt ≠ 0) :
    ∃ p : EisensteinIdealPrime, ∃ j : ℕ, 0 < j ∧ ν=Finsupp.single p j := by
  have hc : ν.support.card=1 := by
    by_contra hn
    exact hν (idealVonMangoldt_not_prime_power ν hn)
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
  exact ⟨p,ν p,Nat.pos_of_ne_zero hp,he⟩

lemma single_prime_ne_higher {p q : EisensteinIdealPrime} {j : ℕ} (hj : 2 ≤ j) :
    (Finsupp.single p 1 : EisensteinIdealExponent) ≠ Finsupp.single q j := by
  intro he
  have hh := congrArg (fun ν : EisensteinIdealExponent => ν q) he
  by_cases hpq : p=q
  · subst p
    simp only [Finsupp.single_eq_same] at hh
    omega
  · simp [Ne.symm hpq] at hh
    omega

theorem idealMangoldtSum_sub_prime (χ : EisensteinIdealExponent → ℂ) (X : ℝ) :
    idealMangoldtSum χ X-idealPrimeChebyshev χ X =
      ∑ ν ∈ higherIdealPrimePowers X,
        ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
  unfold idealMangoldtSum idealPrimeChebyshev higherIdealPrimePowers
  rw [Finset.sum_filter,←Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ν hν
  by_cases hp : ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1
  · obtain ⟨p,rfl⟩ := hp
    have hn : ¬∃ q : EisensteinIdealPrime, ∃ j : ℕ, 2 ≤ j ∧
        (Finsupp.single p 1 : EisensteinIdealExponent)=Finsupp.single q j := by
      rintro ⟨q,j,hj,he⟩
      exact single_prime_ne_higher hj he
    rw [ite_eq_left ⟨p,rfl⟩,ite_eq_right hn,idealVonMangoldt_single_prime,sub_self]
  · rw [ite_eq_right hp,sub_zero]
    by_cases hh : ∃ p : EisensteinIdealPrime, ∃ j : ℕ, 2 ≤ j ∧ ν=Finsupp.single p j
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      have hz : MvPowerSeries.coeff ν idealVonMangoldt=0 := by
        by_contra hn
        obtain ⟨p,j,hj,he⟩ := idealVonMangoldt_support ν hn
        have hj1 : j ≠ 1 := by
          intro hj1
          exact hp ⟨p,by simpa only [hj1] using he⟩
        exact hh ⟨p,j,by omega,he⟩
      rw [hz,Complex.ofReal_zero,zero_mul]

theorem idealMangoldt_prime_replacement_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1)*Real.log X := by
  rw [idealMangoldtSum_sub_prime]
  exact (norm_sum_le _ _).trans (higherIdealPrimePowers_mass χ hχ hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealBall
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite norm ball of prime ideals and the exact reindexing of its
logarithmically weighted sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primeIdealBall {X : ℝ} {p : EisensteinIdealPrime} :
    p ∈ primeIdealBall X ↔ idealExponentNorm (Finsupp.single p 1) ≤ X := by
  constructor
  · intro hp
    obtain ⟨ν,hν,hpν⟩ := Finset.mem_biUnion.mp hp
    have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hpν))
    exact (idealExponentNorm_mono hle).trans (mem_fullIdealBall.mp hν)
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨Finsupp.single p 1,mem_fullIdealBall.mpr hp,by simp⟩

lemma primeIdealBall_image (X : ℝ) :
    (primeIdealBall X).image (fun p => Finsupp.single p 1) =
      (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1) := by
  ext ν
  simp only [Finset.mem_image,mem_primeIdealBall,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨hp,p,rfl⟩
  · rintro ⟨hν,p,rfl⟩
    exact ⟨p,hν,rfl⟩

lemma idealPrimeChebyshev_eq_sum_primes (χ : EisensteinIdealExponent → ℂ) (X : ℝ) :
    idealPrimeChebyshev χ X = ∑ p ∈ primeIdealBall X,
      (Real.log (idealExponentNorm (Finsupp.single p 1)):ℂ)*χ (Finsupp.single p 1) := by
  unfold idealPrimeChebyshev
  rw [←primeIdealBall_image,Finset.sum_image]
  exact fun _ _ _ _ h => Finsupp.single_left_injective (by norm_num : (1:ℕ) ≠ 0) h

lemma primeIdealLog_nonneg (p : EisensteinIdealPrime) :
    0 ≤ Real.log (idealExponentNorm (Finsupp.single p 1)) :=
  Real.log_nonneg (idealExponentNorm_ge_one _)

lemma idealExponentNorm_primeSet (S : Finset EisensteinIdealPrime) :
    idealExponentNorm (primeSetExponent S) =
      ∏ p ∈ S, idealExponentNorm (Finsupp.single p 1) := by
  induction S using Finset.induction_on with
  | empty => simp [primeSetExponent,idealExponentNorm,idealExponentGenerator]
  | @insert p S hp ih =>
    simp only [primeSetExponent,Finset.sum_insert hp,idealExponentNorm_add,Finset.prod_insert hp] at *
    rw [ih]

lemma primeIdealLog_sum_le (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent)
    (hS : S ⊆ ν.support) :
    (∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1))) ≤ Real.log (idealExponentNorm ν) := by
  have hle : primeSetExponent S ≤ ν := (primeSetExponent_le_iff S ν).mpr
    (fun p hp => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hS hp)))
  have hh := Real.log_le_log (idealExponentNorm_pos (primeSetExponent S)) (idealExponentNorm_mono hle)
  rwa [idealExponentNorm_primeSet,Real.log_prod (fun _ _ => (idealExponentNorm_pos _).ne')] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact deletion of finitely many Euler factors in prime-ideal sums.
Its logarithmic cost is bounded by the norm of the original modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeIdealRestriction_single (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (p : EisensteinIdealPrime) :
    primeIdealRestriction S χ (Finsupp.single p 1) =
      if p ∈ S then 0 else χ (Finsupp.single p 1) := by
  have he : (∀ q ∈ S, (Finsupp.single p 1 : EisensteinIdealExponent) q=0) ↔ p ∉ S := by
    constructor
    · intro h hp
      have hh := h p hp
      simp at hh
    · intro hp q hq
      have hqp : q ≠ p := fun he => hp (he ▸ hq)
      simp [hqp]
  unfold primeIdealRestriction
  by_cases hp : p ∈ S
  · rw [ite_eq_right (fun h => (he.mp h) hp),ite_eq_left hp]
  · rw [ite_eq_left (he.mpr hp),ite_eq_right hp]

theorem primeIdeal_restriction_error (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction S χ) X‖ ≤
      ∑ p ∈ S, Real.log (idealExponentNorm (Finsupp.single p 1)) := by
  rw [idealPrimeChebyshev_eq_sum_primes,idealPrimeChebyshev_eq_sum_primes,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primeIdealBall X, if p ∈ S then
        Real.log (idealExponentNorm (Finsupp.single p 1)) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      rw [primeIdealRestriction_single]
      by_cases hmem : p ∈ S
      · simp only [hmem,ite_true, if_true]
        rw [mul_zero,sub_zero,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (primeIdealLog_nonneg p)]
        exact mul_le_of_le_one_right (primeIdealLog_nonneg p) (hχ _)
      · simp only [hmem,ite_false, if_false,sub_self,norm_zero,le_refl]
    _ = ∑ p ∈ (primeIdealBall X).filter (fun p => p ∈ S),
        Real.log (idealExponentNorm (Finsupp.single p 1)) := by rw [Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp => (Finset.mem_filter.mp hp).2) (fun p _ _ => primeIdealLog_nonneg p)

theorem primeIdeal_restriction_norm_cost (ν : EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ κ, ‖χ κ‖ ≤ 1) (X : ℝ) :
    ‖idealPrimeChebyshev χ X-idealPrimeChebyshev (primeIdealRestriction ν.support χ) X‖ ≤
      Real.log (idealExponentNorm ν) :=
  (primeIdeal_restriction_error ν.support χ hχ X).trans
    (primeIdealLog_sum_le ν.support ν (Finset.Subset.refl _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealPrimaryTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from complete prime ideals to the manuscript's unique
primary prime representatives when the ramified coefficient vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_idealExponent_single {a : Eisenstein} (ha : Prime a) :
    ∃ p : EisensteinIdealPrime, idealExponentOf a=Finsupp.single p 1 := by
  have hcard : (idealExponentOf a).support.card=1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p=1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  exact ⟨p,by rw [he,hone]⟩

lemma prime_idealPrimaryGenerator (p : EisensteinIdealPrime) :
    Prime (idealPrimaryGenerator (Finsupp.single p 1)) := by
  have hp : Prime (idealExponentGenerator (Finsupp.single p 1)) := by
    simpa [idealExponentGenerator,Finsupp.prod_single_index] using
      (idealPrimeRepresentative_irreducible p).prime
  exact (primaryNormalize_associated (idealExponentGenerator (Finsupp.single p 1))).prime_iff.mp hp

lemma primeCutoff_image_idealExponent (X : ℝ) :
    (primeCutoff X).image idealExponentOf =
      ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)) := by
  ext ν
  simp only [Finset.mem_image,Finset.mem_filter,mem_fullIdealBall]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hap,haX⟩ := mem_primeCutoff.mp ha
    refine ⟨⟨?_,prime_idealExponent_single hap.2⟩,?_⟩
    · rwa [idealExponentOf_norm hap.2.ne_zero]
    · rw [idealPrimaryGenerator_at_element hap.1]
      exact hap.1
  · rintro ⟨⟨hN,p,rfl⟩,hp⟩
    refine ⟨idealPrimaryGenerator (Finsupp.single p 1),mem_primeCutoff.mpr ⟨⟨hp,
      prime_idealPrimaryGenerator p⟩,?_⟩,idealExponentOf_primaryGenerator _⟩
    rwa [idealPrimaryGenerator_norm]

theorem idealPrimeChebyshev_primary_sum (χ : EisensteinIdealExponent → ℂ)
    (ψ : Eisenstein → ℂ)
    (hzero : ∀ ν, ¬primary (idealPrimaryGenerator ν) → χ ν=0)
    (hval : ∀ a : Eisenstein, primary a → χ (idealExponentOf a)=ψ a) (X : ℝ) :
    idealPrimeChebyshev χ X=primeChebyshev ψ X := by
  unfold idealPrimeChebyshev
  have he : (∑ ν ∈ (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1),
      (Real.log (idealExponentNorm ν):ℂ)*χ ν) =
      ∑ ν ∈ ((fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1)).filter
        (fun ν => primary (idealPrimaryGenerator ν)), (Real.log (idealExponentNorm ν):ℂ)*χ ν := by
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν hν
    by_cases hp : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp,hzero ν hp,mul_zero]
  rw [he,←primeCutoff_image_idealExponent,Finset.sum_image]
  · unfold primeChebyshev
    rw [primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hap := (mem_primeCutoff.mp ha).1
    rw [hval a hap.1,idealExponentOf_norm hap.2.ne_zero]
    ring
  · intro a ha b hb hab
    exact idealExponentOf_inj_primary (mem_primeCutoff.mp ha).1.1
      (mem_primeCutoff.mp hb).1.1 hab

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-ideal Euler-factor restoration and exact primary-prime transfer
for fixed angular characters, retaining the original modulus at three. -/
noncomputable section
namespace CubicFirstMoment

theorem induced_angular_prime_error {q d : Eisenstein} (hq : q ≠ 0) (hd : d ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (X : ℝ) :
    ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
      idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ Real.log (norm q) := by
  have he : angularResidueIdealChar q χ ℓ =
      primeIdealRestriction (idealExponentOf q).support (angularResidueIdealChar d ψ ℓ) :=
    funext (induced_angularResidueIdealChar hq h ℓ)
  rw [he,norm_sub_rev]
  have hh := primeIdeal_restriction_norm_cost (idealExponentOf q)
    (angularResidueIdealChar d ψ ℓ) (angularResidueIdealChar_norm_le_one hd ψ ℓ) X
  rwa [idealExponentOf_norm hq] at hh

lemma residueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : residueIdealChar q χ ν=0 := by
  have hnc : ¬IsCoprime q (idealExponentGenerator ν) := by
    intro hc
    have hcop := (hc.of_isCoprime_of_dvd_left h3).symm
    apply hn
    exact (idealPrimaryGenerator_primary_iff ν).mpr ((idealGenerator_coprime_three_iff ν).mp hcop)
  exact MulChar.map_nonunit χ (fun hu => hnc (isCoprime_of_residue_isUnit hu))

lemma angularResidueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : angularResidueIdealChar q χ ℓ ν=0 := by
  rw [angularResidueIdealChar,residueIdealChar_zero_nonprimary h3 χ ν hn,zero_mul]

theorem angular_primeChebyshev_eq_ideal {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ) (X : ℝ) :
    primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X =
      idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X := by
  symm
  apply idealPrimeChebyshev_primary_sum
  · exact angularResidueIdealChar_zero_nonprimary h3 χ ℓ
  · intro a ha
    exact angularResidueIdealChar_at_element χ hu (primary_ne_zero ha)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorOrder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic numerator characters have odd order. In particular a
nonprincipal one is not self-conjugate, as required when excluding the
real-character exceptional term in the prime estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorLift_unit_cube {v x : Eisenstein}
    (hx : IsUnit (Ideal.Quotient.mk (modulus (9*v)) x)) :
    cubicNumeratorLift v x ^ 3 = 1 := by
  have hcop := isCoprime_of_residue_isUnit hx
  have h3 : IsCoprime (3:Eisenstein) x := hcop.of_isCoprime_of_dvd_left ⟨3*v,by ring⟩
  have hv : IsCoprime x v := hcop.of_mul_left_right.symm
  have hx3 := residue_isUnit_of_isCoprime h3
  rw [cubicNumeratorLift,ite_eq_left hx3]
  apply cubicSymbol_cube_of_isCoprime (primaryNormalize_primary hx3)
  obtain ⟨u,hu⟩ := primaryNormalize_associated x
  rw [←hu]
  exact (isCoprime_mul_unit_right_left u.isUnit x v).mpr hv

lemma cubicNumeratorChar_cube (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) : cubicNumeratorChar hpub v hv ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num),MulChar.one_apply u.isUnit]
  change cubicNumeratorLift v (residueRepresentative (9*v) u)^3 = 1
  apply cubicNumeratorLift_unit_cube
  rw [residueRepresentative_spec]
  exact u.isUnit

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive reduction of the actual cubic numerator character preserves
its cubic order, its global unit invariance, and its values on primary
arguments prime to the original modulus. -/
noncomputable section
namespace CubicFirstMoment

lemma ResidueCharacterInduces.cube_eq_one {q d : Eisenstein}
    (hq : q ≠ 0) {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (hind : ResidueCharacterInduces q d χ ψ) (hχ : χ^3=1) : ψ^3=1 := by
  apply MulChar.ext
  intro u
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Residues d)
  have hdx : IsCoprime d x := isCoprime_of_residue_isUnit (by rw [hx]; exact u.isUnit)
  obtain ⟨y,hy,hdy⟩ := exists_coprime_residue_lift hq hdx
  have hqy : IsCoprime q y := hdy.of_mul_left_right
  have he : ψ u = χ (Ideal.Quotient.mk (modulus q) y) := by
    rw [←hx,←residue_eq_of_dvd_sub hy]
    exact hind.2 y hqy
  rw [MulChar.pow_apply' _ (by norm_num),he,MulChar.one_apply u.isUnit]
  have h := congrArg (fun ξ : MulChar (Residues q) ℂ => ξ (Ideal.Quotient.mk (modulus q) y)) hχ
  simpa only [MulChar.pow_apply' _ (by norm_num : (3:ℕ) ≠ 0),
    MulChar.one_apply (residue_isUnit_of_isCoprime hqy)] using h

/-- Exact primitive character associated with any nonzero numerator. -/
theorem cubicNumerator_primitive_conductor (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧
      d ∣ 9*v ∧ normNat d ≤ normNat (9*v) ∧ ψ^3=1 ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u)=1) ∧
      ResidueCharacterInduces (9*v) d (cubicNumeratorChar hpub v hv) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime v x →
        ψ (Ideal.Quotient.mk (modulus d) x)=cubicSymbol x v) := by
  have hq : 9*v ≠ (0:Eisenstein) := mul_ne_zero (by norm_num) hv
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq
    (cubicNumeratorChar hpub v hv)
  refine ⟨d,ψ,hd,hp,hi.1,hN,hi.cube_eq_one hq (cubicNumeratorChar_cube hpub v hv),
    hi.global_units (cubicNumeratorChar_units hpub v hv),hi,?_⟩
  intro x hx hcop
  have h9x : IsCoprime (9:Eisenstein) x := by
    convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  exact (hi.2 x (h9x.mul_left hcop)).trans (cubicNumeratorChar_primary hpub v hv hx)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicPrimeConductorScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary conductor scales for the arbitrary nonzero cubic numerator. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHeckeScale_le_norm {q : Eisenstein} (hq : q ≠ 0) :
    residueHeckeScale q ≤ norm q := by
  have hN := one_le_norm hq
  have hs : Real.sqrt (3*norm q) ≤ 2*norm q := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  unfold residueHeckeScale
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

lemma cubicNumerator_modulus_norm (v : Eisenstein) : norm (9*v)=81*norm v := by
  rw [norm_mul_eq]
  have h9 : norm (9:Eisenstein)=81 := by change Complex.normSq (9:ℂ)=81; norm_num
  rw [h9]

lemma cubicNumerator_primitive_scale {v d : Eisenstein} (hv : v ≠ 0) (hd : d ≠ 0)
    (hN : normNat d ≤ normNat (9*v)) :
    1 ≤ 810*norm v ∧ residueHeckeScale d ≤ 810*norm v ∧ 7 ≤ 810*norm v ∧
      norm (9*v) ≤ 810*norm v := by
  have hv1 := one_le_norm hv
  have hdN : norm d ≤ 81*norm v := by
    have hh : (normNat d:ℝ) ≤ (normNat (9*v):ℝ) := Nat.cast_le.mpr hN
    simpa only [normNat_cast,cubicNumerator_modulus_norm] using hh
  have hs := (residueHeckeScale_le_norm hd).trans hdN
  rw [cubicNumerator_modulus_norm]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteMellinContour
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite contour displacement with an explicit horizontal-edge error.
Only holomorphy on the finite rectangle is required. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem finite_mellin_rectangle_identity {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (finiteMellinBox a b T)) :
    (∫ x in a..b, f (x-(T:ℂ)*Complex.I))-
      (∫ x in a..b, f (x+(T:ℂ)*Complex.I))+
      Complex.I*(∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      Complex.I*(∫ y in -T..T, f (a+(y:ℂ)*Complex.I))=0 := by
  have hd : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc (-T) T) := by
    simpa only [uIcc_of_le hab,uIcc_of_le (show -T ≤ T by linarith),finiteMellinBox] using hf
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a:ℂ)-(T:ℂ)*Complex.I) ((b:ℂ)+(T:ℂ)*Complex.I)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.sub_im,Complex.add_im,mul_zero,
    sub_zero,add_zero,zero_sub,mul_one,zero_add] at h
  simpa only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.sub_im,Complex.add_im,mul_zero,zero_mul,
    sub_zero,add_zero,zero_sub,mul_one,zero_add,Complex.ofReal_neg,
    neg_mul,add_neg_cancel,sub_self,smul_eq_mul,sub_eq_add_neg] using h hd

theorem finite_mellin_shift_bound {a b T H : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (finiteMellinBox a b T))
    (hTop : ∀ x ∈ Icc a b, ‖f (x+(T:ℂ)*Complex.I)‖ ≤ H)
    (hBot : ∀ x ∈ Icc a b, ‖f (x-(T:ℂ)*Complex.I)‖ ≤ H) :
    ‖(∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, f (a+(y:ℂ)*Complex.I))‖ ≤ 2*H*(b-a) := by
  have he := finite_mellin_rectangle_identity hab hT f hf
  have h1 : ‖∫ x in a..b, f (x+(T:ℂ)*Complex.I)‖ ≤ H*(b-a) := by
    calc
      _ ≤ H*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx =>
        hTop x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have h2 : ‖∫ x in a..b, f (x-(T:ℂ)*Complex.I)‖ ≤ H*(b-a) := by
    calc
      _ ≤ H*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx =>
        hBot x (by rw [uIoc_of_le hab] at hx; exact ⟨hx.1.le,hx.2⟩))
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have hid : Complex.I*((∫ y in -T..T, f (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, f (a+(y:ℂ)*Complex.I)))=
      (∫ x in a..b, f (x+(T:ℂ)*Complex.I))-
        (∫ x in a..b, f (x-(T:ℂ)*Complex.I)) := by linear_combination he
  have hn := norm_sub_le (∫ x in a..b, f (x+(T:ℂ)*Complex.I))
    (∫ x in a..b, f (x-(T:ℂ)*Complex.I))
  rw [←hid,norm_mul,Complex.norm_I,one_mul] at hn
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeros
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zeros of the actual entire Hecke continuations: none occur right of
one, bounded sets contain finitely many, and local multiplicities are
positive finite integers. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

theorem heckeSeries_ne_zero {χ : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {s : ℂ} (hs1 : 1 < s.re) : L s ≠ 0 := by
  rw [hs s hs1]
  exact idealDirichlet_ne_zero χ hχ hχ0 hχadd hs1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeroFreePair
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-free step for a nonreal character and its square. The inputs
are the actual entire continuations and proved disk bounds; no prime-sum
or zero-free assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma principalPoleConstant_pos : 0 < principalPoleConstant :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.1

lemma principalPoleRadius_pos : 0 < principalPoleRadius :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.2.1

lemma diskLogDerivativeConstant_pos : 0 < diskLogDerivativeConstant := by
  have hl : 0 < Real.log ((7/8:ℝ)/(3/4)) := Real.log_pos (by norm_num)
  unfold diskLogDerivativeConstant
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDiskGrowth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial and logarithmic conductor-height bounds for the actual
normalized Hecke disks. The constants depend only on the fixed ideal lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma heckeDiskPolynomialConstant_gt_one : 1 < heckeDiskPolynomialConstant := by
  have h : 0 ≤ 32*(9/2:ℝ)^4*idealZetaTwo^2 := by positivity
  unfold heckeDiskPolynomialConstant
  linarith

lemma heckePairLogConstant_pos : 0 < heckePairLogConstant := by
  have hP := principalPoleConstant_pos
  have hR := principalPoleRadius_pos
  have hD := diskLogDerivativeConstant_pos
  have hC := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold heckePairLogConstant
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeUniformLogDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single logarithmic width and a log-squared bound for an entire finite
Hecke contour. All zero-free information is derived from the analytic pair. -/
noncomputable section
namespace CubicFirstMoment

lemma heckeZeroFreeWidth_pos {u : ℝ} (hu : 10 ≤ u) : 0 < heckeZeroFreeWidth u := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  positivity

lemma heckeZeroFreeWidth_le_one {u : ℝ} (hu : 10 ≤ u) : heckeZeroFreeWidth u ≤ 1 := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma heckeZeroFreeWidth_le_log {u : ℝ} (hu : 10 ≤ u) :
    heckeZeroFreeWidth u ≤ 1/(32*heckePairLogConstant*Real.log u) := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma heckeLogSquaredConstant_pos : 0 < heckeLogSquaredConstant := by
  have hD := diskLogDerivativeConstant_pos
  have hC := heckePairLogConstant_pos
  have hP := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have hr : 0 < Real.log ((7/8:ℝ)/(3/4:ℝ)) := Real.log_pos (by norm_num)
  unfold heckeLogSquaredConstant
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivativeMajorant
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform absolute bound on the right Mellin line. Positivity of the
actual von Mangoldt coefficients reduces every twist to the principal pole. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem idealLogDeriv_norm_le_principal
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {σ t : ℝ} (hσ : 1 < σ) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (-logDeriv principalIdealZeta (σ:ℂ)).re := by
  have hst : 1 < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by simpa using hσ
  have hsum := idealVonMangoldtDirichlet_norm_summable χ hχ hst
  have hp := idealMangoldt_real_hasSum (fun _ => 1) (by simp) hσ
  simp only [mul_one,Complex.one_re] at hp
  have hprincipal : (-logDeriv principalIdealZeta (σ:ℂ)).re=
      ∑' ν, (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*idealExponentNorm ν^(-σ) := by
    rw [idealSeries_logDeriv_eq (fun s hs => principalIdealZeta_right hs)
      (by simpa using hσ),idealDirichlet_neg_logDeriv (fun _ => 1)
        (by simp) (by simp) (by simp) (by simpa using hσ)]
    simpa only [mul_one] using hp.tsum_eq.symm
  rw [hprincipal,←norm_neg,idealSeries_logDeriv_eq hs hst,
    idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd hst]
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum hp.summable
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν),
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re]
  simp only [Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (idealVonMangoldt_coeff_nonneg ν) (hχ ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

theorem idealLogDeriv_uniform_right_line :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
      ∀ (L : ℂ → ℂ),
      (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
      ∀ σ t : ℝ, 1 < σ → σ < 1+δ →
      ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 1/(σ-1)+C := by
  obtain ⟨C,δ,hC,hδ,hb⟩ := principalIdealZeta_real_logDeriv_bound
  refine ⟨C,δ,hC,hδ,?_⟩
  intro χ hχ hχ0 hχadd L hs σ t hσ hσδ
  exact (idealLogDeriv_norm_le_principal χ hχ hχ0 hχadd hs hσ).trans (hb σ hσ hσδ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtContour
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite contour identity for the actual ideal von Mangoldt
Mellin integrand. Nonvanishing on the box is supplied by the proved
Hecke zero-free region, before estimating its edges. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma idealMangoldtMellinIntegrand_differentiableOn
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X a b T : ℝ} (hX : 0 < X)
    (hn : ∀ s ∈ finiteMellinBox a b T, L s ≠ 0) :
    DifferentiableOn ℂ (idealMangoldtMellinIntegrand L W X) (finiteMellinBox a b T) := by
  let _ : NeZero (X:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hm := smooth_mellin_entire W hW hpos hsm.continuous
  intro s hs
  have hl : AnalyticAt ℂ (logDeriv L) s :=
    (hL.analyticAt s).deriv.div (hL.analyticAt s) (hn s hs)
  exact (((hm s).mul ((differentiable_const_cpow_of_neZero (X:ℂ)) s)).mul
    hl.differentiableAt.neg).differentiableWithinAt

theorem idealMangoldt_finite_contour_bound
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X a b T H : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hn : ∀ s ∈ finiteMellinBox a b T, L s ≠ 0)
    (hTop : ∀ x ∈ Icc a b, ‖idealMangoldtMellinIntegrand L W X (x+(T:ℂ)*Complex.I)‖ ≤ H)
    (hBot : ∀ x ∈ Icc a b, ‖idealMangoldtMellinIntegrand L W X (x-(T:ℂ)*Complex.I)‖ ≤ H) :
    ‖(∫ y in -T..T, idealMangoldtMellinIntegrand L W X (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, idealMangoldtMellinIntegrand L W X (a+(y:ℂ)*Complex.I))‖ ≤
        2*H*(b-a) :=
  finite_mellin_shift_bound hab hT _
    (idealMangoldtMellinIntegrand_differentiableOn hL W hW hpos hsm hX hn) hTop hBot

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative tails of the actual prime Mellin integral. Constants are
uniform over a bounded real strip; the principal pole controls all twists. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma mellinScaledWeight_norm (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖mellinScaledWeight W X σ t‖=X^σ*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [mellinScaledWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

lemma mellinScaledWeight_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) : Integrable (mellinScaledWeight W X σ) := by
  let _ : NeZero (X:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hc : Continuous (mellinScaledWeight W X σ) := by
    unfold mellinScaledWeight
    exact ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp
      (by fun_prop)).mul ((differentiable_const_cpow_of_neZero (X:ℂ)).continuous.comp
        (by fun_prop))
  exact (((smooth_mellin_vertical_integrable W hW hpos hsm σ).norm).const_mul (X^σ)).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => (mellinScaledWeight_norm W hX σ t).le))

lemma mellinScaledWeight_moment_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) (A : ℕ) :
    Integrable (fun t => |t|^A*‖mellinScaledWeight W X σ t‖) := by
  have hi := ((mellinVerticalSchwartz W hW hpos hsm σ).integrable_pow_mul volume A).const_mul (X^σ)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [mellinScaledWeight_norm W hX,mellinVerticalSchwartz_apply,Real.norm_eq_abs]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtBoxEdges
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the left and horizontal edges of the actual prime contour. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma mem_finiteMellinBox {a b T σ t : ℝ}
    (hσ : σ ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
    (σ:ℂ)+(t:ℂ)*Complex.I ∈ finiteMellinBox a b T := by
  simpa only [finiteMellinBox,Complex.mem_reProdIm,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,mul_zero,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,Complex.I_im,mul_one,zero_add] using And.intro hσ ht

lemma idealMangoldtMellinIntegrand_norm (L : ℂ → ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖=
      X^σ*‖mellin W (σ+(t:ℂ)*Complex.I)‖*‖logDeriv L (σ+(t:ℂ)*Complex.I)‖ := by
  change ‖mellinScaledWeight W X σ t*(-logDeriv L _)‖=_
  rw [norm_mul,norm_neg,mellinScaledWeight_norm W hX]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtBoxEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite zero-free contour gives a quantitative bound on the actual
smoothed von Mangoldt sum, including both horizontal edges and the full tail. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma idealMangoldtMellinIntegrand_integrable_right
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X σ B : ℝ} (hX : 0 < X)
    (hn : ∀ t : ℝ, L ((σ:ℂ)+(t:ℂ)*Complex.I) ≠ 0)
    (hb : ∀ t : ℝ, ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B) :
    Integrable (fun t : ℝ => idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)) := by
  have hc : Continuous (fun t : ℝ => -logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hl := ((hL.analyticAt _).deriv.div (hL.analyticAt _) (hn t)).continuousAt
    have hg : ContinuousAt (fun y : ℝ => (σ:ℂ)+(y:ℂ)*Complex.I) t := by fun_prop
    exact (hl.comp (f := fun y : ℝ => (σ:ℂ)+(y:ℂ)*Complex.I) hg).neg
  have hw := mellinScaledWeight_integrable W hW hpos hsm hX σ
  apply (hw.norm.mul_const B).mono' (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards with t
  change ‖mellinScaledWeight W X σ t*(-logDeriv L _)‖ ≤ _
  rw [norm_mul,norm_neg]
  exact mul_le_mul_of_nonneg_left (hb t) (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMellinControlEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit linear dependence of each prime-contour edge estimate on
its finite Mellin control. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma PrimeMellinControl.scaled_moment_bound {W : ℝ → ℂ} {D : ℝ}
    (hD : PrimeMellinControl W D) {X σ : ℝ} (hX : 0 < X) (hσ : |σ| ≤ 2)
    {A : ℕ} (hA : A=0 ∨ A=2) :
    (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖) ≤ D*X^σ := by
  have he : (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖)=
      X^σ*(∫ t : ℝ, |t|^A*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [mellinScaledWeight_norm W hX]
    ring
  rw [he,mul_comm D]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX.le _)
  rcases hA with rfl | rfl
  · simpa only [pow_zero,one_mul] using hD.mass σ hσ
  · exact hD.moment σ hσ

theorem PrimeMellinControl.left_edge_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {D : ℝ} (hD : PrimeMellinControl W D) :
    ∀ (L : ℂ → ℂ) (X a T B : ℝ),
      0 < X → |a| ≤ 2 → 0 ≤ T → 0 ≤ B →
      (∀ t ∈ Icc (-T) T, ‖logDeriv L (a+(t:ℂ)*Complex.I)‖ ≤ B) →
      ‖∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)‖ ≤
        D*X^a*B := by
  intro L X a T B hX ha hT hB hlog
  have hi := (mellinScaledWeight_integrable W hW hpos hsm hX a).norm.const_mul B
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),←integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Icc (-T) T, B*‖mellinScaledWeight W X a t‖ := by
      apply norm_integral_le_of_norm_le hi.restrict
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change ‖mellinScaledWeight W X a t*(-logDeriv L _)‖ ≤ _
      rw [norm_mul,norm_neg]
      nlinarith [hlog t ht,_root_.norm_nonneg (mellinScaledWeight W X a t)]
    _ ≤ ∫ t : ℝ, B*‖mellinScaledWeight W X a t‖ :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => by positivity))
    _ = B*(∫ t : ℝ, |t|^0*‖mellinScaledWeight W X a t‖) := by
      simp only [pow_zero,one_mul,integral_const_mul]
    _ ≤ B*(D*X^a) := mul_le_mul_of_nonneg_left (hD.scaled_moment_bound hX ha (by decide : 0=0 ∨ 0=2)) hB
    _ = _ := by ring


theorem PrimeMellinControl.horizontal_edges_bound
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {D : ℝ} (hD : PrimeMellinControl W D) :
    ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      ∀ (X a b T B : ℝ), 1 ≤ X → 0 ≤ a → a ≤ b → b ≤ 2 → 0 < T → 0 ≤ B →
      (∀ s ∈ finiteMellinBox a b T, L s ≠ 0) →
      (∀ s ∈ finiteMellinBox a b T, ‖logDeriv L s‖ ≤ B) →
      ‖(∫ t in -T..T, idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I))-
        (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))‖ ≤
          4*D*X^b*B/T^2 := by
  have hC := hD.nonneg
  have hdecay := hD.decay
  intro L hL X a b T B hX ha hab hb hT hB hn hlog
  have hXp : 0 < X := by linarith
  have hpoint (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t|=T) :
      ‖idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖ ≤ D*X^b*B/T^2 := by
    have hσabs : |σ| ≤ 2 := by rw [abs_of_nonneg (ha.trans hσ.1)]; exact hσ.2.trans hb
    have hm := hdecay σ hσabs t
    rw [ht] at hm
    have hm' : ‖mellin W (σ+(t:ℂ)*Complex.I)‖ ≤ D/T^2 := by
      apply (le_div_iff₀ (pow_pos hT 2)).mpr
      have hpow : T^2 ≤ (1+T)^2 := by nlinarith
      simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hpow (_root_.norm_nonneg _)).trans hm
    have htmem : t ∈ Icc (-T) T := by
      have hh := abs_le.mp ht.le
      exact hh
    have hl := hlog _ (mem_finiteMellinBox hσ htmem)
    rw [idealMangoldtMellinIntegrand_norm L W hXp]
    calc
      _ ≤ X^b*(D/T^2)*B := by
        gcongr
        exact hσ.2
      _ = _ := by ring
  have hh := idealMangoldt_finite_contour_bound hL W hW hpos hsm hXp hab hT.le hn
    (fun σ hσ => hpoint σ T hσ (abs_of_pos hT)) (fun σ hσ => by
      have he : (σ:ℂ)-(T:ℂ)*Complex.I=(σ:ℂ)+((-T:ℝ):ℂ)*Complex.I := by push_cast; ring
      rw [he]
      exact hpoint σ (-T) hσ (by rw [abs_neg,abs_of_pos hT]))
  apply hh.trans
  have hlen : b-a ≤ 2 := by linarith
  have hc : 0 ≤ D*X^b*B/T^2 := by positivity
  calc
    _ ≤ 2*(D*X^b*B/T^2)*2 := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtControlled
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smoothed prime estimate with its finite cutoff cost exposed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem idealMangoldt_smooth_bound_controlled :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (W : ℝ → ℂ) (_hW : HasCompactSupport W),
      tsupport W ⊆ Ioi 0 → ContDiff ℝ ∞ W →
      ∀ D : ℝ, PrimeMellinControl W D →
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
      ∀ X a b T B : ℝ, 1 ≤ X → 0 ≤ a → a ≤ b → 1 < b → b < 1+δ → b ≤ 2 →
      0 < T → 0 ≤ B →
      (∀ s ∈ finiteMellinBox a b T, L s ≠ 0) →
      (∀ s ∈ finiteMellinBox a b T, ‖logDeriv L s‖ ≤ B) →
      ‖idealMangoldtSmooth χ W X‖ ≤
        6*D*(X^a*B+X^b*(B+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hline⟩ := idealLogDeriv_uniform_right_line
  refine ⟨C,δ,hC,hδ,?_⟩
  intro W hW hpos hsm D hD
  let Kl := D
  let Ke := 4*D
  let Kt := D
  let K := 6*D
  have hKl : 0 ≤ Kl := hD.nonneg
  have hKe : 0 ≤ Ke := mul_nonneg (by norm_num) hD.nonneg
  have hKt : 0 ≤ Kt := hD.nonneg
  have hleft := hD.left_edge_bound W hW hpos hsm
  have hedges := hD.horizontal_edges_bound W hW hpos hsm
  intro χ hχ hχ0 hχadd L hL hs X a b T B hX ha hab hb hbδ hb2 hT hB hn hlog
  have hXp : 0 < X := by linarith
  have hBa : 0 ≤ 1/(b-1)+C := by positivity
  have hright (t : ℝ) : ‖logDeriv L ((b:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 1/(b-1)+C :=
    hline χ hχ hχ0 hχadd L hs b t hb hbδ
  have hi := idealMangoldtMellinIntegrand_integrable_right hL W hW hpos hsm hXp
    (fun t => heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa using hb)) hright
  have hl := hleft L X a T B hXp (by rw [abs_of_nonneg ha]; linarith) hT.le hB
    (fun t ht => hlog _ (mem_finiteMellinBox ⟨le_rfl,hab⟩ ht))
  have he := hedges L hL X a b T B hX ha hab hb2 hT hB hn hlog
  have ht := bounded_product_height_tail (mellinScaledWeight W X b)
    (fun t => -logDeriv L ((b:ℂ)+(t:ℂ)*Complex.I))
    (mellinScaledWeight_integrable W hW hpos hsm hXp b) 2
    (mellinScaledWeight_moment_integrable W hW hpos hsm hXp b 2) hT hBa
    (fun t => by simpa only [norm_neg] using hright t)
  have ht' : ‖∫ t in (Icc (-T) T)ᶜ,
      idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I)‖ ≤ Kt*(1/(b-1)+C)*X^b/T^2 := by
    calc
      _ ≤ ((1/(b-1)+C)/T^2)*(∫ t : ℝ, |t|^2*‖mellinScaledWeight W X b t‖) := ht
      _ ≤ ((1/(b-1)+C)/T^2)*(Kt*X^b) := by
        apply mul_le_mul_of_nonneg_left (hD.scaled_moment_bound hXp (by rw [abs_of_pos (by linarith)]; exact hb2) (Or.inr rfl))
        positivity
      _ = _ := by ring
  let F := fun t : ℝ => idealMangoldtMellinIntegrand L W X (b+(t:ℂ)*Complex.I)
  have hcentral : ‖∫ t in Icc (-T) T, F t‖ ≤ Kl*X^a*B+Ke*X^b*B/T^2 := by
    have hiEq : (∫ t in Icc (-T) T, F t)=∫ t in -T..T, F t := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith)]
    rw [hiEq]
    calc
      _ ≤ ‖∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)‖+
        ‖(∫ t in -T..T, F t)-
          (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))‖ := by
        simpa only [add_sub_cancel] using norm_add_le
          (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I))
          ((∫ t in -T..T, F t)-
            (∫ t in -T..T, idealMangoldtMellinIntegrand L W X (a+(t:ℂ)*Complex.I)))
      _ ≤ _ := add_le_add hl he
  have hfull : ‖∫ t : ℝ, F t‖ ≤ Kl*X^a*B+Ke*X^b*B/T^2+Kt*(1/(b-1)+C)*X^b/T^2 := by
    rw [←integral_add_compl measurableSet_Icc hi]
    exact (norm_add_le _ _).trans (add_le_add hcentral ht')
  have hpre : ‖idealMangoldtSmooth χ W X‖ ≤ ‖∫ t : ℝ, F t‖ := by
    rw [idealMangoldt_smooth_mellin χ hχ hχ0 hχadd hs W hW hpos hsm hXp hb]
    change ‖((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ, F t)‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply mul_le_of_le_one_left (_root_.norm_nonneg _)
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  apply hpre.trans (hfull.trans _)
  calc
    _ ≤ K*X^a*B+K*X^b*B/T^2+K*(1/(b-1)+C)*X^b/T^2 := by
      gcongr <;> dsimp [K,Kl,Ke,Kt] at * <;> linarith
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeControlled
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative smooth prime estimate with its explicit finite weight cost deduced from the actual Hecke
functional equations for a character and its square. No prime bound or
zero-free assertion is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem hecke_smooth_prime_bound_controlled :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (W : ℝ → ℂ) (_hW : HasCompactSupport W),
    tsupport W ⊆ Ioi 0 → ContDiff ℝ ∞ W →
    ∀ D : ℝ, PrimeMellinControl W D →
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 u T : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    10 ≤ u → A ≤ u → A2 ≤ u → k+7 ≤ u → k2+7 ≤ u → 4+2*(T+3) ≤ u →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X b : ℝ, 1 ≤ X → 1 < b → b < 1+δ → b ≤ 2 → 0 < T →
      ‖idealMangoldtSmooth χ W X‖ ≤ 6*D*
        (X^(1-heckeZeroFreeWidth u/2)*(heckeLogSquaredConstant*(1+Real.log u)^2)+
          X^b*(heckeLogSquaredConstant*(1+Real.log u)^2+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := idealMangoldt_smooth_bound_controlled
  refine ⟨C,δ,hC,hδ,?_⟩
  intro W hW hpos hsm D hD χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 u T ε ε2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT
    hFE hFE2 hcomp hcomp2 X b hX hb hbδ hb2 hT
  have hw := heckeZeroFreeWidth_pos hu
  have hw1 := heckeZeroFreeWidth_le_one hu
  have ha : 0 ≤ 1-heckeZeroFreeWidth u/2 := by linarith
  have hab : 1-heckeZeroFreeWidth u/2 ≤ b := by linarith
  apply hbound W hW hpos hsm D hD χ hχ hχ0 hχadd L hL hs X (1-heckeZeroFreeWidth u/2) b T
    (heckeLogSquaredConstant*(1+Real.log u)^2) hX ha hab hb hbδ hb2 hT
    (mul_nonneg heckeLogSquaredConstant_pos.le (sq_nonneg _))
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    have him : |s.im| ≤ T := abs_le.mpr hparts.2
    have hheight : 4+|s.im| ≤ u := by linarith
    have hheight2 : 4+|2*s.im| ≤ u := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    rw [←Complex.re_add_im s]
    apply hecke_zero_free_log_from_analytic_pair hχ hχ0 hχadd hχdual hχ2dual hL hL2
      hs hs2 hds hds2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hFE2 hcomp hcomp2
    have hwidth := heckeZeroFreeWidth_le_log hu
    linarith [hparts.1.1]
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    rw [←Complex.re_add_im s]
    exact hecke_logDeriv_norm_uniform_from_analytic_pair hχ hχ0 hχadd hχdual hχ2dual hL hL2
      hs hs2 hds hds2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT hFE hFE2 hcomp hcomp2
      hparts.1.1 (hparts.1.2.trans hb2) (abs_le.mpr hparts.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeScales
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete height and conductor scales for the prime contour. -/
noncomputable section
namespace CubicFirstMoment

lemma primeContourHeight_ge_one (X : ℝ) : 1 ≤ primeContourHeight X := by
  exact Real.one_le_exp (Real.sqrt_nonneg _)

lemma primeContourDecay_pos : 0 < primeContourDecay := by
  have hC := heckePairLogConstant_pos
  have hl : 0 < Real.log 32 := Real.log_pos (by norm_num)
  unfold primeContourDecay
  positivity

lemma primeContourSize_log {Q X : ℝ} (hQ : 0 < Q) :
    Real.log (primeContourSize Q X)=Real.log 32+Real.log Q+Real.sqrt (Real.log X) := by
  unfold primeContourSize primeContourHeight
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by norm_num) hQ.ne',Real.log_exp]

lemma primeContourSize_bounds {Q X : ℝ} (hQ : 1 ≤ Q) :
    10 ≤ primeContourSize Q X ∧ Q ≤ primeContourSize Q X ∧
      4+2*(primeContourHeight X+3) ≤ primeContourSize Q X := by
  have ht := primeContourHeight_ge_one X
  have hprod : 32*primeContourHeight X ≤ primeContourSize Q X := by
    dsimp [primeContourSize]
    nlinarith
  constructor
  · linarith
  constructor
  · dsimp [primeContourSize]
    nlinarith
  · linarith

lemma primeContourDenominator_ge_one {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    1 ≤ primeContourDenominator Q X := by
  have hroot : 1 ≤ Real.sqrt (Real.log X) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hX)
  unfold primeContourDenominator
  linarith [Real.log_nonneg hQ]

lemma primeContourSize_log_bound {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    1+Real.log (primeContourSize Q X) ≤
      (2+Real.log 32)*primeContourDenominator Q X := by
  rw [primeContourSize_log (by linarith)]
  have hd := primeContourDenominator_ge_one hQ hX
  have hl : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  unfold primeContourDenominator at *
  nlinarith

lemma primeContourWidth_lower {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeContourDecay/primeContourDenominator Q X ≤ heckeZeroFreeWidth (primeContourSize Q X)/2 := by
  have hd := primeContourDenominator_ge_one hQ hX
  have hu := (primeContourSize_bounds hQ (X := X)).1
  have hlu : 0 < Real.log (primeContourSize Q X) := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  have hl : 0 < Real.log 32 := Real.log_pos (by norm_num)
  have hb := primeContourSize_log_bound hQ hX
  have hrec : 1/(64*(1+heckePairLogConstant)*((2+Real.log 32)*primeContourDenominator Q X)) ≤
      1/(64*(1+heckePairLogConstant)*(1+Real.log (primeContourSize Q X))) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  convert hrec using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [primeContourDecay,heckeZeroFreeWidth,div_div] <;> congr 1 <;> ring)

lemma primeContour_shifted_power {Q X : ℝ} (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2) ≤
      X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X) := by
  have hw := primeContourWidth_lower hQ hX
  have he : X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)=
      Real.exp (Real.log X-primeContourDecay*Real.log X/primeContourDenominator Q X) := by
    rw [Real.exp_sub,Real.exp_log hXp]
    rw [show -primeContourDecay*Real.log X/primeContourDenominator Q X =
      -(primeContourDecay*Real.log X/primeContourDenominator Q X) by ring,Real.exp_neg]
    ring
  rw [he,Real.rpow_def_of_pos hXp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤ Real.log X by linarith)
  have hh' : primeContourDecay*Real.log X/primeContourDenominator Q X ≤
      heckeZeroFreeWidth (primeContourSize Q X)/2*Real.log X := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  nlinarith

lemma primeContour_right_power {X : ℝ} (hX : 0 < X) (hlog : Real.log X ≠ 0) :
    X^(1+1/Real.log X)=Real.exp 1*X := by
  rw [Real.rpow_def_of_pos hX]
  have he : Real.log X*(1+1/Real.log X)=1+Real.log X := by field_simp; ring
  rw [he,Real.exp_add,Real.exp_log hX]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSmoothingScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing a cutoff width after its finite derivative order is known.
The same exponential saving absorbs the cutoff cost and the contour tail. -/
noncomputable section
namespace CubicFirstMoment

lemma primeSmoothingRate_pos (d : ℕ) : 0 < primeSmoothingRate d := by
  unfold primeSmoothingRate
  positivity [primeContourDecay_pos]

lemma primeSmoothingRate_bounds (d : ℕ) :
    ((d:ℝ)+1)*primeSmoothingRate d ≤ primeContourDecay ∧
    ((d:ℝ)+1)*primeSmoothingRate d ≤ 1/2 ∧ primeSmoothingRate d ≤ 1/2 := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  have he : ((d:ℝ)+1)*primeSmoothingRate d = min primeContourDecay 1/2 := by
    unfold primeSmoothingRate
    field_simp
  have hmin : 0 < min primeContourDecay 1 := lt_min primeContourDecay_pos zero_lt_one
  have hleft : min primeContourDecay 1/2 ≤ primeContourDecay := by
    have hh := min_le_left primeContourDecay 1
    linarith
  have hright : min primeContourDecay 1/2 ≤ 1/2 := by
    have hh := min_le_right primeContourDecay 1
    linarith
  refine ⟨he.trans_le hleft,he.trans_le hright,?_⟩
  have hc := primeSmoothingRate_pos d
  nlinarith [show (0:ℝ) ≤ d by positivity]

lemma primeContour_ratio_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    0 ≤ Real.log X/primeContourDenominator Q X ∧
    Real.log X/primeContourDenominator Q X ≤ Real.sqrt (Real.log X) ∧
    Real.log X/primeContourDenominator Q X ≤ Real.log X := by
  have hd := primeContourDenominator_ge_one hQ hX
  have hl : 0 ≤ Real.log X := by linarith
  refine ⟨div_nonneg hl (by linarith),?_,div_le_self hl hd⟩
  apply (div_le_iff₀ (by linarith : 0 < primeContourDenominator Q X)).mpr
  have hs := Real.sq_sqrt hl
  have hq := Real.log_nonneg hQ
  unfold primeContourDenominator
  nlinarith [Real.sqrt_nonneg (Real.log X)]

lemma primeSmoothingParameter_ge_one (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) : 1 ≤ primeSmoothingParameter d Q X := by
  apply Real.one_le_exp
  exact mul_nonneg (primeSmoothingRate_pos d).le (primeContour_ratio_bounds hQ hX).1

lemma primeSmoothing_absorbs_shift (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*
      Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X) ≤
    Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).1
    (primeContour_ratio_bounds hQ hX).1
  simp only [div_eq_mul_inv] at *
  nlinarith only [hh]

lemma primeSmoothing_absorbs_tail (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d/primeContourHeight X^2 ≤
      Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,primeContourHeight,←Real.exp_nat_mul,←Real.exp_nat_mul,
    ←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).2.1
    (primeContour_ratio_bounds hQ hX).1
  have hb := (primeContour_ratio_bounds hQ hX).2.1
  norm_num only [Nat.cast_ofNat] at *
  simp only [div_eq_mul_inv] at *
  nlinarith [Real.sqrt_nonneg (Real.log X)]

lemma primeSmoothing_absorbs_sqrt (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    Real.sqrt X ≤ X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).2.2
    (primeContour_ratio_bounds hQ hX).1
  have hb := (primeContour_ratio_bounds hQ hX).2.2
  have he : Real.sqrt X=Real.exp (Real.log X/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hXp]
    congr 1
    ring
  calc
    _ = Real.exp (Real.log X/2) := he
    _ ≤ Real.exp (Real.log X+-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv] at *
      nlinarith
    _ = _ := by rw [Real.exp_add,Real.exp_log hXp]

lemma primeSmoothing_inverse (d : ℕ) (Q X : ℝ) :
    X/primeSmoothingParameter d Q X =
      X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,div_eq_mul_inv,←Real.exp_neg]
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeContourOptimization
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary optimization of the actual smoothed prime contour bound.
The cutoff order is fixed before the conductor and the summation length. -/
noncomputable section
namespace CubicFirstMoment

lemma primeLogSize_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 1 ≤ Real.log X) :
    1 ≤ Real.log (X*Q) ∧ Real.log X ≤ Real.log (X*Q) ∧
    primeContourDenominator Q X ≤ Real.log (X*Q) := by
  have hq := Real.log_nonneg hQ
  have hs : Real.sqrt (Real.log X) ≤ Real.log X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith,?_⟩
    nlinarith
  rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
  unfold primeContourDenominator
  exact ⟨by linarith,by linarith,by linarith⟩

lemma primeLogDerivative_polynomial {Q X : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 1 ≤ Real.log X) :
    heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2 ≤
      (heckeLogSquaredConstant*(2+Real.log 32)^2)*(Real.log (X*Q))^2 := by
  have hu := (primeContourSize_bounds hQ (X := X)).1
  have hp := (primeLogSize_bounds hQ hXp hX).2.2
  have hlog32 : 0 ≤ 2+Real.log 32 := by positivity
  have hh := (primeContourSize_log_bound hQ hX).trans
    (mul_le_mul_of_nonneg_left hp hlog32)
  have hleft : 0 ≤ 1+Real.log (primeContourSize Q X) := by
    have := Real.log_nonneg (show 1 ≤ primeContourSize Q X by linarith)
    linarith
  have hsq := pow_le_pow_left₀ hleft hh 2
  have hm := mul_le_mul_of_nonneg_left hsq heckeLogSquaredConstant_pos.le
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma primeSmoothing_left_power (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2) ≤
      X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  calc
    _ ≤ primeSmoothingParameter d Q X^d*
        (X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)) :=
      mul_le_mul_of_nonneg_left (primeContour_shifted_power hQ hXp hX)
        (pow_nonneg (le_trans zero_le_one (primeSmoothingParameter_ge_one d hQ hX)) d)
    _ = X*(primeSmoothingParameter d Q X^d*
        Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeSmoothing_absorbs_shift d hQ hX) hXp.le

lemma primeSmoothing_right_power (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*X^(1+1/Real.log X)/primeContourHeight X^2 ≤
      Real.exp 1*(X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  calc
    _ = (Real.exp 1*X)*(primeSmoothingParameter d Q X^d/primeContourHeight X^2) := by
      rw [primeContour_right_power hXp (by linarith)]
      ring
    _ ≤ (Real.exp 1*X)*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) :=
      mul_le_mul_of_nonneg_left (primeSmoothing_absorbs_tail d hQ hX) (by positivity)
    _ = _ := by ring

lemma primeContour_optimized_bound (d : ℕ) {K C Q X : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    6*(K*primeSmoothingParameter d Q X^d)*
      (X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2)*
          (heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2)+
        X^(1+1/Real.log X)*(heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2+
          (1/((1+1/Real.log X)-1)+C))/primeContourHeight X^2) ≤
    (6*K*((1+Real.exp 1)*(heckeLogSquaredConstant*(2+Real.log 32)^2)+Real.exp 1*(1+C)))*
      (X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  let B := heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2
  let P := (Real.log (X*Q))^2
  let E := heckeLogSquaredConstant*(2+Real.log 32)^2
  let V := X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)
  have hB : 0 ≤ B := by dsimp [B]; positivity [heckeLogSquaredConstant_pos]
  have hBP : B ≤ E*P := primeLogDerivative_polynomial hQ hXp hX
  have hP : 1 ≤ P := by
    have hp := (primeLogSize_bounds hQ hXp hX).1
    dsimp [P]
    nlinarith
  have hLP : Real.log X ≤ P := by
    have hp := (primeLogSize_bounds hQ hXp hX).2.1
    have hp1 := (primeLogSize_bounds hQ hXp hX).1
    dsimp [P]
    nlinarith
  have hBCP : B+(Real.log X+C) ≤ (E+1+C)*P := by
    nlinarith [mul_le_mul_of_nonneg_left hP hC]
  have hden : 1/((1+1/Real.log X)-1)=Real.log X := by field_simp; ring
  rw [hden]
  change 6*(K*primeSmoothingParameter d Q X^d)*
    (X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2)*B+
      X^(1+1/Real.log X)*(B+(Real.log X+C))/primeContourHeight X^2) ≤ _
  calc
    _ = 6*K*((primeSmoothingParameter d Q X^d*
          X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2))*B+
        (primeSmoothingParameter d Q X^d*X^(1+1/Real.log X)/primeContourHeight X^2)*
          (B+(Real.log X+C))) := by ring
    _ ≤ 6*K*(V*B+(Real.exp 1*V)*(B+(Real.log X+C))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_right (primeSmoothing_left_power d hQ hXp hX) hB)
        (mul_le_mul_of_nonneg_right (primeSmoothing_right_power d hQ hXp hX) (by positivity))
    _ ≤ 6*K*(V*(E*P)+(Real.exp 1*V)*((E+1+C)*P)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hBP (by dsimp [V]; positivity))
        (mul_le_mul_of_nonneg_left hBCP (by dsimp [V]; positivity))
    _ = _ := by dsimp [V,E,P]; ring

lemma primeSmoothing_cutoff_error (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    32*(X/primeSmoothingParameter d Q X+Real.sqrt X)*Real.log (6*X) ≤
      64*(1+Real.log 6)*(X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  have hp1 := (primeLogSize_bounds hQ hXp hX).1
  have hLP := (primeLogSize_bounds hQ hXp hX).2.1
  have hp2 : 1 ≤ (Real.log (X*Q))^2 := by nlinarith
  have hL2 : Real.log X ≤ (Real.log (X*Q))^2 := by nlinarith
  have hlog6 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 6)
  have hlog : Real.log (6*X) ≤ (1+Real.log 6)*(Real.log (X*Q))^2 := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    nlinarith
  have hlog0 : 0 ≤ Real.log (6*X) := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    linarith
  let V := X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)
  calc
    _ ≤ 32*(V+V)*Real.log (6*X) := by
      apply mul_le_mul_of_nonneg_right _ hlog0
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (le_of_eq (primeSmoothing_inverse d Q X))
        (primeSmoothing_absorbs_sqrt d hQ hXp hX)
    _ = 64*V*Real.log (6*X) := by ring
    _ ≤ 64*V*((1+Real.log 6)*(Real.log (X*Q))^2) :=
      mul_le_mul_of_nonneg_left hlog (by dsimp [V]; positivity)
    _ = _ := by dsimp [V]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicError
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative removal of the narrowing logarithmic cutoff. The error
is bounded by the actual ideal lattice in its two endpoint annuli. -/
noncomputable section
namespace CubicFirstMoment

lemma primeReciprocal_exp_bounds {J : ℝ} (hJ : 1 ≤ J) :
    Real.exp (-1/J) ≤ 1 ∧ 1 ≤ Real.exp (1/J) ∧ Real.exp (1/J) ≤ 3 ∧
    1-Real.exp (-1/J) ≤ 2/J ∧ Real.exp (1/J)-1 ≤ 2/J := by
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have ht : 0 ≤ 1/J := by positivity
  have ht1 : 1/J ≤ 1 := (div_le_one hJ0).mpr hJ
  have hu := Real.abs_exp_sub_one_le (x := 1/J) (by rwa [abs_of_nonneg ht])
  have hl := Real.abs_exp_sub_one_le (x := -1/J) (by
    rw [neg_div,abs_neg,abs_of_nonneg ht]; exact ht1)
  rw [abs_of_nonneg ht] at hu
  rw [neg_div,abs_neg,abs_of_nonneg ht] at hl
  have he := Real.one_le_exp ht
  have he' : Real.exp (-1/J) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rw [neg_div]
    linarith
  refine ⟨he',he,?_,?_,?_⟩
  · linarith [(le_abs_self (Real.exp (1/J)-1)).trans hu]
  · have hh := (neg_le_abs (Real.exp (-(1/J))-1)).trans hl
    rw [←neg_div] at hh
    rw [show (2:ℝ)/J = 2*(1/J) by ring]
    linarith
  · rw [show (2:ℝ)/J = 2*(1/J) by ring]
    linarith [(le_abs_self (Real.exp (1/J)-1)).trans hu]

theorem idealMangoldt_dyadic_smoothing_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J X : ℝ} (hJ : 1 ≤ J) (hX : Real.exp 1 ≤ X) :
    ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ ≤
      32*(X/J+Real.sqrt X)*Real.log (6*X) := by
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  obtain ⟨heL,heU,he3,hdL,hdU⟩ := primeReciprocal_exp_bounds hJ
  have hrec : 1/J ≤ 1 := (div_le_one hJp).mpr hJ
  have hA1 : 1 ≤ Real.exp (-1/J)*X := by
    calc
      1 ≤ Real.exp (-1/J)*Real.exp 1 := by
        rw [←Real.exp_add]
        apply Real.one_le_exp
        rw [neg_div]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
  have hAX : Real.exp (-1/J)*X ≤ X := mul_le_of_le_one_left hXp.le heL
  have hBX : 2*Real.exp (1/J)*X ≤ 6*X := by nlinarith
  have hdLX : X-Real.exp (-1/J)*X ≤ 2*(X/J) := by
    have hh := mul_le_mul_of_nonneg_right hdL hXp.le
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hdUX : 2*Real.exp (1/J)*X-2*X ≤ 4*(X/J) := by
    have hh := mul_le_mul_of_nonneg_right hdU (show 0 ≤ 2*X by positivity)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hsA : Real.sqrt (Real.exp (-1/J)*X) ≤ Real.sqrt X := Real.sqrt_le_sqrt hAX
  have hsB : Real.sqrt (2*Real.exp (1/J)*X) ≤ 3*Real.sqrt X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hXp.le]
  have hs2 : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hXp.le]
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hl6 : 0 ≤ Real.log (6*X) := Real.log_nonneg (by linarith)
  have hlogs : Real.log X ≤ Real.log (6*X) := Real.log_le_log hXp (by linarith)
  have hlogsB : Real.log (2*Real.exp (1/J)*X) ≤ Real.log (6*X) :=
    Real.log_le_log (by positivity) hBX
  have hlow : 4*(X-Real.exp (-1/J)*X+Real.sqrt X+Real.sqrt (Real.exp (-1/J)*X))*Real.log X ≤
      4*(2*(X/J)+2*Real.sqrt X)*Real.log (6*X) := by
    apply mul_le_mul _ hlogs hlX (by positivity)
    linarith
  have hupp : 4*(2*Real.exp (1/J)*X-2*X+Real.sqrt (2*Real.exp (1/J)*X)+Real.sqrt (2*X))*
      Real.log (2*Real.exp (1/J)*X) ≤
      4*(4*(X/J)+5*Real.sqrt X)*Real.log (6*X) := by
    apply mul_le_mul _ hlogsB (Real.log_nonneg (by nlinarith)) (by positivity)
    linarith
  calc
    _ ≤ _ := idealMangoldt_dyadic_smoothing_error χ hχ hJ hXp hA1
    _ ≤ 4*(2*(X/J)+2*Real.sqrt X)*Real.log (6*X)+
        4*(4*(X/J)+5*Real.sqrt X)*Real.log (6*X) := add_le_add hlow hupp
    _ ≤ _ := by nlinarith [mul_nonneg (div_nonneg hXp.le hJp.le) hl6,
      mul_nonneg (Real.sqrt_nonneg X) hl6]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDyadicPrimeEstimate
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyadic prime-ideal cancellation from the actual Hecke functional
equations for a character and its square. No prime estimate is assumed. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_dyadic_prime_bound_of_analytic_pair :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/2 ∧ 1 < X0 ∧
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtDyadic χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := hecke_smooth_prime_bound_controlled
  obtain ⟨d,K,hK,hcontrol⟩ := primeDyadicWeight_mellin_control
  let M := 6*K*((1+Real.exp 1)*(heckeLogSquaredConstant*(2+Real.log 32)^2)+Real.exp 1*(1+C))
  let X0 := Real.exp (max 2 (2/δ))
  have hM : 0 < M := by
    have hlog32 : 0 < 2+Real.log 32 := by positivity
    dsimp [M]
    positivity [heckeLogSquaredConstant_pos]
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hX0 : 1 < X0 := by
    apply Real.one_lt_exp_iff.mpr
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M+64*(1+Real.log 6),primeSmoothingRate d,X0,by positivity,
    primeSmoothingRate_pos d,(primeSmoothingRate_bounds d).2.2,hX0,?_⟩
  intro χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hFE2 hcomp hcomp2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : max 2 (2/δ) ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos (max 2 (2/δ))) hX
    rwa [Real.log_exp] at hh
  have hLX1 : 1 ≤ Real.log X := by linarith [le_max_left (2:ℝ) (2/δ)]
  have hLXpos : 0 < Real.log X := by linarith
  have hrec : 1/Real.log X < δ := by
    have hh : 2 ≤ Real.log X*δ := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hLX)
    exact (div_lt_iff₀ hLXpos).mpr (by linarith)
  have hXe : Real.exp 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr hLX1
    rwa [Real.exp_log hXp] at hh
  let J := primeSmoothingParameter d Q X
  have hJ : 1 ≤ J := primeSmoothingParameter_ge_one d hQ hLX1
  have hu := primeContourSize_bounds hQ (X := X)
  have hpre := hbound (primeDyadicWeight J hJ) (primeDyadicWeight_compact hJ)
    (primeDyadicWeight_positive_support hJ) (primeDyadicWeight_smooth hJ)
    (K*J^d) (hcontrol J hJ) hχ hχ0 hχadd hχdual hχ2dual hL hL2 hs hs2 hds hds2
    hA hA2 hk hk2 hε hε2 hu.1 (hQA.trans hu.2.1) (hQA2.trans hu.2.1)
    (hQk.trans hu.2.1) (hQk2.trans hu.2.1) hu.2.2 hFE hFE2 hcomp hcomp2
    X (1+1/Real.log X) (by linarith)
    (by have hh := one_div_pos.mpr hLXpos; linarith) (by linarith)
    (by have hh := (div_le_one hLXpos).mpr hLX1; linarith) (Real.exp_pos _)
  have hmain : ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X‖ ≤
      M*(X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) :=
    hpre.trans (primeContour_optimized_bound d hK.le hC.le hQ hXp hLX1)
  have herr := (idealMangoldt_dyadic_smoothing_bound χ hχ hJ hXe).trans
    (primeSmoothing_cutoff_error d hQ hXp hLX1)
  calc
    _ = ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-
        (idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X‖+
        ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the prime contour majorant over the upper half of a
contracting dyadic partition. -/
noncomputable section
namespace CubicFirstMoment

lemma primeDyadic_log_bounds {X t : ℝ} (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    0 < t ∧ 1 ≤ Real.log t ∧ Real.log X/2 ≤ Real.log t ∧ Real.log t ≤ Real.log X := by
  have htp : 0 < t := (Real.sqrt_pos.mpr hXp).trans_le ht
  have hlo := Real.log_le_log (Real.sqrt_pos.mpr hXp) ht
  rw [Real.log_sqrt hXp.le] at hlo
  exact ⟨htp,by linarith,hlo,Real.log_le_log htp htX⟩

lemma primeDyadic_ratio_compare {Q X t : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 2 ≤ Real.log X) (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    (Real.log X/primeContourDenominator Q X)/2 ≤
      Real.log t/primeContourDenominator Q t := by
  obtain ⟨htp,hlt,hlo,hhi⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hdX := primeContourDenominator_ge_one hQ (by linarith : 1 ≤ Real.log X)
  have hdt := primeContourDenominator_ge_one hQ hlt
  have hden : primeContourDenominator Q t ≤ primeContourDenominator Q X := by
    unfold primeContourDenominator
    linarith [Real.sqrt_le_sqrt hhi]
  calc
    _ = (Real.log X/2)/primeContourDenominator Q X := by ring
    _ ≤ Real.log t/primeContourDenominator Q X :=
      div_le_div_of_nonneg_right hlo (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by linarith) hden

lemma primeDyadic_majorant_compare {c Q X t : ℝ} (hc : 0 ≤ c) (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hX : 2 ≤ Real.log X) (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    primeCancellationWeight c Q t ≤
      t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
  obtain ⟨htp,hlt,_,_⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hl : Real.log (t*Q) ≤ Real.log (X*Q) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right htX (by linarith))
  have hl0 : 0 ≤ Real.log (t*Q) := by
    have hh := (primeLogSize_bounds hQ htp hlt).1
    linarith
  have hsq := pow_le_pow_left₀ hl0 hl 2
  have he : Real.exp (-c*Real.log t/primeContourDenominator Q t) ≤
      Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (primeDyadic_ratio_compare hQ hXp hX ht htX) hc
    simp only [div_eq_mul_inv] at *
    nlinarith only [hh]
  unfold primeCancellationWeight
  exact mul_le_mul (mul_le_mul_of_nonneg_left hsq htp.le) he
    (Real.exp_pos _).le (by positivity)

lemma primeDyadic_sqrt_absorption {c Q X t : ℝ} (_hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    Real.sqrt t ≤ t*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
  obtain ⟨htp,hlt,hlo,_⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hy := primeContour_ratio_bounds hQ (by linarith : 1 ≤ Real.log X)
  have hh := mul_le_mul_of_nonneg_right hc1 hy.1
  have hs : Real.sqrt t = Real.exp (Real.log t/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos htp]
    congr 1
    ring
  calc
    _ = Real.exp (Real.log t/2) := hs
    _ ≤ Real.exp (Real.log t+-(c/2)*Real.log X/primeContourDenominator Q X) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv] at *
      nlinarith [hy.2.2]
    _ = _ := by rw [Real.exp_add,Real.exp_log htp]

lemma primeDyadic_boundary_compare {c Q X t : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    8*Real.sqrt t*Real.log t ≤
      8*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨htp,hlt,_,hhi⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hlog : Real.log t ≤ (Real.log (X*Q))^2 := by nlinarith
  have hh := mul_le_mul (primeDyadic_sqrt_absorption hc hc1 hQ hXp hX ht htX)
    hlog (by linarith : 0 ≤ Real.log t) (by positivity)
  nlinarith only [hh]

lemma primeDyadic_small_compare {c Q X r : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hr : 1 ≤ r) (hrX : r ≤ X) (hrs : r ≤ 2*Real.sqrt X) :
    8*r*Real.log r ≤ 16*primeCancellationWeight (c/2) Q X := by
  have hroot : Real.sqrt X ≤ X := by
    have hx1 : 1 ≤ X := by
      have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
      simpa [Real.exp_log hXp] using hh
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hsq := primeDyadic_sqrt_absorption hc hc1 hQ hXp hX hroot le_rfl
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hlog : Real.log r ≤ (Real.log (X*Q))^2 := by
    have hh := Real.log_le_log (by linarith : 0 < r) hrX
    nlinarith
  have hh := mul_le_mul hrs hlog (Real.log_nonneg hr) (by positivity : 0 ≤ 2*Real.sqrt X)
  have hhh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log (X*Q)))
  unfold primeCancellationWeight
  nlinarith only [hh,hhh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicScales
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite contracting-dyad partition stopping at the square-root scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primeDyadic_scale_sum (X : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1)) = X-X/(2:ℝ)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    rw [pow_succ]
    field_simp
    ring

lemma primeDyadic_scale_sum_le {X : ℝ} (hX : 0 ≤ X) (N : ℕ) :
    (∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1)) ≤ X := by
  rw [primeDyadic_scale_sum]
  linarith [div_nonneg hX (show (0:ℝ) ≤ 2^N by positivity)]

lemma exists_primeDyadic_sqrt_split {X : ℝ} (hX : 1 ≤ X) :
    ∃ N : ℕ, Real.sqrt X ≤ X/(2:ℝ)^N ∧ X/(2:ℝ)^N ≤ 2*Real.sqrt X ∧
      X/(2:ℝ)^N ≤ X ∧
      ∀ j < N, Real.sqrt X ≤ X/(2:ℝ)^(j+1) ∧ X/(2:ℝ)^(j+1) ≤ X := by
  have hX0 : 0 ≤ X := by linarith
  have hs1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0).mpr (by simpa using hX)
  obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hs1 (by norm_num : (1:ℝ) < 2)
  have hlow : Real.sqrt X ≤ X/(2:ℝ)^N := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2^N)).mpr
    have hh := mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg X)
    nlinarith [Real.sq_sqrt hX0]
  have hhigh : X/(2:ℝ)^N ≤ 2*Real.sqrt X := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^N)).mpr
    rw [pow_succ] at hN'
    have hh := mul_le_mul_of_nonneg_left hN'.le (Real.sqrt_nonneg X)
    nlinarith [Real.sq_sqrt hX0]
  refine ⟨N,hlow,hhigh,div_le_self hX0 (one_le_pow₀ (by norm_num)),?_⟩
  intro j hj
  constructor
  · apply hlow.trans
    exact div_le_div_of_nonneg_left hX0 (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))
  · exact div_le_self hX0 (one_le_pow₀ (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtFullFromDyadic
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative reconstruction of the full ideal von Mangoldt prefix.
The lower endpoint corrections and the square-root prefix are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem idealMangoldt_full_from_dyadic (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {B c Q X0 X : ℝ}
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hQ : 1 ≤ Q) (hX0 : 1 ≤ X0)
    (hdyad : ∀ t : ℝ, X0 ≤ t → ‖idealMangoldtDyadic χ t‖ ≤ B*primeCancellationWeight c Q t)
    (hXp : 0 < X) (hX : 2 ≤ Real.log X) (hXX0 : X0^2 ≤ X) :
    ‖idealMangoldtSum χ X‖ ≤ (B+24)*primeCancellationWeight (c/2) Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  obtain ⟨N,hrlo,hrhi,hrX,hscales⟩ := exists_primeDyadic_sqrt_split hX1
  have hs0 : X0 ≤ Real.sqrt X := (Real.le_sqrt (by linarith) hXp.le).mpr hXX0
  let E := (Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinc (j : ℕ) (hj : j ∈ Finset.range N) :
      ‖dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j)‖ ≤
        (B+8)*(X/(2:ℝ)^(j+1)*E) := by
    let t := X/(2:ℝ)^(j+1)
    obtain ⟨htlo,htX⟩ := hscales j (Finset.mem_range.mp hj)
    have htp : 0 < t := by dsimp [t]; positivity
    have ht0 : X0 ≤ t := hs0.trans htlo
    have ht1 : 1 ≤ t := hX0.trans ht0
    have hxj : X/(2:ℝ)^j = 2*t := by
      dsimp [t]
      rw [pow_succ]
      field_simp
    have he : dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j) =
        idealMangoldtDyadic χ t-
          ∑ ν ∈ fullIdealBall (2*t) with idealExponentNorm ν = t,
            ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν := by
      unfold dyadicDifference
      rw [hxj,show 2*t/2=t by ring,idealMangoldtSum_dyadic χ htp.le]
    have hd := (hdyad t ht0).trans (mul_le_mul_of_nonneg_left
      (primeDyadic_majorant_compare hc hQ hXp hX htlo htX) hB)
    have hb := (idealMangoldt_boundary_bound χ hχ (B := 2*t) ht1).trans
      (primeDyadic_boundary_compare hc hc1 hQ hXp hX htlo htX)
    rw [he]
    calc
      _ ≤ ‖idealMangoldtDyadic χ t‖+
          ‖∑ ν ∈ fullIdealBall (2*t) with idealExponentNorm ν = t,
            ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖ := norm_sub_le _ _
      _ ≤ B*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X))+
          8*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)) :=
        add_le_add hd hb
      _ = _ := by dsimp [t,E]; ring
  have hr1 : 1 ≤ X/(2:ℝ)^N := hX0.trans (hs0.trans hrlo)
  have hsmall := (idealMangoldtSum_norm_bound χ hχ hr1).trans
    (primeDyadic_small_compare hc hc1 hQ hXp hX hr1 hrX hrhi)
  have htel : idealMangoldtSum χ X =
      (∑ j ∈ Finset.range N, dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j))+
        idealMangoldtSum χ (X/(2:ℝ)^N) := by
    rw [dyadicDifference_sum]
    abel
  have hsum : (∑ j ∈ Finset.range N, (B+8)*(X/(2:ℝ)^(j+1)*E)) =
      (B+8)*((∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1))*E) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ‖(∑ j ∈ Finset.range N, dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j))+
        idealMangoldtSum χ (X/(2:ℝ)^N)‖ := congrArg _ htel
    _ ≤ (∑ j ∈ Finset.range N, ‖dyadicDifference (idealMangoldtSum χ) (X/(2:ℝ)^j)‖)+
        ‖idealMangoldtSum χ (X/(2:ℝ)^N)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ j ∈ Finset.range N, (B+8)*(X/(2:ℝ)^(j+1)*E))+
        16*primeCancellationWeight (c/2) Q X := add_le_add (Finset.sum_le_sum hinc) hsmall
    _ = (B+8)*((∑ j ∈ Finset.range N, X/(2:ℝ)^(j+1))*E)+16*primeCancellationWeight (c/2) Q X := by rw [hsum]
    _ ≤ (B+8)*(X*E)+16*primeCancellationWeight (c/2) Q X := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (primeDyadic_scale_sum_le hXp.le N) hE) (by linarith)) le_rfl
    _ = _ := by dsimp [E,primeCancellationWeight]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFullPrimeEstimate
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full sharp ideal von Mangoldt bound, from the actual Hecke
functional equations and the proved finite dyadic reconstruction. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_full_prime_bound_of_analytic_pair :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtSum χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_dyadic_prime_bound_of_analytic_pair
  let X0 := max (Real.exp 2) (Y0^2)
  have hX0 : 1 < X0 := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num)) (le_max_left _ _)
  refine ⟨B+24,c/2,X0,by linarith,by positivity,by linarith,hX0,?_⟩
  intro χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hFE2 hcomp hcomp2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_left _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hwindow (t : ℝ) (ht : Y0 ≤ t) :
      ‖idealMangoldtDyadic χ t‖ ≤ B*primeCancellationWeight c Q t :=
    hbound hχ hχ0 hχadd hχdual hχ2dual hL hL2 hs hs2 hds hds2 hA hA2 hk hk2 hε hε2
      hQ hQA hQA2 hQk hQk2 hFE hFE2 hcomp hcomp2 t ht
  exact idealMangoldt_full_from_dyadic χ hχ hB.le hc.le hc1 hQ hY0.le hwindow hXp hLX
    ((le_max_right _ _).trans hX)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimePowerError
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact prime-power deletion error has the classical square-root
size with two logarithms. -/
noncomputable section
namespace CubicFirstMoment

lemma idealPrimePowerErrorConstant_pos : 0 < idealPrimePowerErrorConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold idealPrimePowerErrorConstant
  positivity

lemma idealPrimePower_log_count {X : ℝ} (hX : Real.exp 1 ≤ X) :
    (Nat.log 2 ⌊X⌋₊+1:ℝ) ≤ (1+1/Real.log 2)*Real.log X := by
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hh
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX1)
  have hfloorpos : (0:ℝ) < (⌊X⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊X⌋₊)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le hXp.le)
  have hn := Real.natLog_le_logb ⌊X⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : (Nat.log 2 ⌊X⌋₊:ℝ) ≤ Real.log X/Real.log 2 :=
    hn.trans (div_le_div_of_nonneg_right hlog h2.le)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem idealMangoldt_prime_replacement_log_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : Real.exp 1 ≤ X) :
    ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      idealPrimePowerErrorConstant*Real.sqrt X*(Real.log X)^2 := by
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  apply (idealMangoldt_prime_replacement_bound χ hχ hX1).trans
  have hh := mul_le_mul_of_nonneg_left (idealPrimePower_log_count hX)
    (show 0 ≤ 18*Real.sqrt X by positivity)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.log_nonneg hX1)
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [idealPrimePowerErrorConstant]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerAbsorption
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The classical higher-prime-power error is absorbed by the same
conductor-uniform exponential majorant at the proved small rate. -/
noncomputable section
namespace CubicFirstMoment

lemma primeCancellation_sqrt_log {c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X) :
    Real.sqrt X*(Real.log X)^2 ≤ primeCancellationWeight c Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hs := primeDyadic_sqrt_absorption (c := 2*c) (by linarith : 0 ≤ 2*c)
    (by linarith : 2*c ≤ 1/2) hQ hXp hX hroot le_rfl
  rw [show 2*c/2=c by ring] at hs
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log X) hLP 2
  calc
    _ ≤ (X*Real.exp (-c*Real.log X/primeContourDenominator Q X))*(Real.log (X*Q))^2 :=
      mul_le_mul hs hsq (sq_nonneg _) (by positivity)
    _ = _ := by unfold primeCancellationWeight; ring

theorem idealPrimeChebyshev_bound_of_mangoldt (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {B c Q X : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hmain : ‖idealMangoldtSum χ X‖ ≤ B*primeCancellationWeight c Q X) :
    ‖idealPrimeChebyshev χ X‖ ≤ (B+idealPrimePowerErrorConstant)*primeCancellationWeight c Q X := by
  have hXe : Real.exp 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show 1 ≤ Real.log X by linarith)
    rwa [Real.exp_log hXp] at hh
  have herr : ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      idealPrimePowerErrorConstant*primeCancellationWeight c Q X := by
    calc
      _ ≤ idealPrimePowerErrorConstant*Real.sqrt X*(Real.log X)^2 :=
        idealMangoldt_prime_replacement_log_bound χ hχ hXe
      _ = idealPrimePowerErrorConstant*(Real.sqrt X*(Real.log X)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (primeCancellation_sqrt_log hc hc1 hQ hXp hX)
        idealPrimePowerErrorConstant_pos.le
  calc
    _ = ‖idealMangoldtSum χ X-(idealMangoldtSum χ X-idealPrimeChebyshev χ X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealMangoldtSum χ X‖+‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ := norm_sub_le _ _
    _ ≤ B*primeCancellationWeight c Q X+idealPrimePowerErrorConstant*primeCancellationWeight c Q X :=
      add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeIdealEstimate
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sharp prime-ideal cancellation from the actual Hecke pair
functional equations. Higher prime powers have been removed by a proved count. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_prime_ideal_bound_of_analytic_pair :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealPrimeChebyshev χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_full_prime_bound_of_analytic_pair
  let X0 := max Y0 (Real.exp 2)
  have hX0 : 1 < X0 := hY0.trans_le (le_max_left _ _)
  refine ⟨B+idealPrimePowerErrorConstant,c,X0,add_pos hB idealPrimePowerErrorConstant_pos,
    hc,hc1,hX0,?_⟩
  intro χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hFE2 hcomp hcomp2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hmain := hbound hχ hχ0 hχadd hχdual hχ2dual hL hL2 hs hs2 hds hds2 hA hA2 hk hk2 hε hε2
    hQ hQA hQA2 hQk hQk2 hFE hFE2 hcomp hcomp2 X ((le_max_left _ _).trans hX)
  exact idealPrimeChebyshev_bound_of_mangoldt χ hχ hc.le hc1 hQ hXp hLX hmain

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_InverseLogWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse logarithm weight used to remove von Mangoldt's prime
logarithm. Its endpoint and total-variation cost is explicit. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma inverseLog_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => (Real.log x)⁻¹) (inverseLogDerivative t) t :=
  (Real.hasDerivAt_log (by linarith : t ≠ 0)).inv (Real.log_pos ht).ne'

lemma inverseLogWeight_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt inverseLogWeight (inverseLogDerivative t:ℂ) t :=
  (inverseLog_hasDerivAt ht).ofReal_comp

lemma inverseLogDerivative_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn inverseLogDerivative (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith
  exact ((continuousAt_inv₀ ht0).neg.div ((Real.continuousAt_log ht0).pow 2)
    (pow_ne_zero 2 (Real.log_pos ht1).ne')).continuousWithinAt

lemma inverseLogWeight_deriv_norm {t : ℝ} (ht : 1 < t) :
    ‖deriv inverseLogWeight t‖ = -inverseLogDerivative t := by
  rw [(inverseLogWeight_hasDerivAt ht).deriv,Complex.norm_real,Real.norm_eq_abs]
  apply abs_of_nonpos
  unfold inverseLogDerivative
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_nonneg.mpr (by linarith))) (sq_nonneg _)

lemma inverseLogWeight_integrableOn_deriv {a b : ℝ} (ha : 1 < a) :
    IntegrableOn (deriv inverseLogWeight) (Icc a b) := by
  have hh : IntegrableOn (fun t : ℝ => (inverseLogDerivative t : ℂ)) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
    (inverseLogDerivative_continuousOn (b := b) ha)).integrableOn_Icc
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (inverseLogWeight_hasDerivAt (ha.trans_le ht.1)).deriv.symm

lemma inverseLogWeight_variation {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    ‖inverseLogWeight a‖+‖inverseLogWeight b‖+
      (∫ t in Ioc a b, ‖deriv inverseLogWeight t‖) ≤ 2 := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have hcont := inverseLogDerivative_continuousOn (b := b) ha1
  have hint : IntervalIntegrable inverseLogDerivative volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hft : (∫ t in a..b, inverseLogDerivative t) = (Real.log b)⁻¹-(Real.log a)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact inverseLog_hasDerivAt (ha1.trans_le ht.1)
  have hn : (∫ t in Ioc a b, ‖deriv inverseLogWeight t‖) =
      (Real.log a)⁻¹-(Real.log b)⁻¹ := by
    calc
      _ = ∫ t in Ioc a b, -inverseLogDerivative t := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact inverseLogWeight_deriv_norm (ha1.trans ht.1)
      _ = -(∫ t in a..b, inverseLogDerivative t) := by
        rw [integral_neg,intervalIntegral.integral_of_le hab]
      _ = _ := by rw [hft]; ring
  have hla : 1 ≤ Real.log a := by
    have hh := Real.log_le_log (Real.exp_pos 1) ha
    simpa only [Real.log_exp] using hh
  have hia : (Real.log a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hla
  rw [hn]
  simp only [inverseLogWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.log_pos ha1).le),
    abs_of_nonneg (inv_nonneg.mpr (Real.log_pos hb1).le)]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeEstimateTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite loss in restoring the original modulus is absorbed in
the same explicit prime majorant. No new analytic estimate is needed. -/
noncomputable section
namespace CubicFirstMoment

lemma angularResidueIdealChar_zero (q : Eisenstein) (χ : MulChar (Residues q) ℂ) :
    angularResidueIdealChar q χ 0=residueIdealChar q χ := by
  funext ν
  simp only [angularResidueIdealChar,theta_zero,mul_one]

lemma primeCancellation_log_cost {c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X) :
    Real.log Q ≤ primeCancellationWeight c Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hs := primeDyadic_sqrt_absorption (c := 2*c) (by linarith : 0 ≤ 2*c)
    (by linarith : 2*c ≤ 1/2) hQ hXp hX hroot le_rfl
  rw [show 2*c/2=c by ring] at hs
  have hroot1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by simpa using hX1)
  have hv : 1 ≤ X*Real.exp (-c*Real.log X/primeContourDenominator Q X) := hroot1.trans hs
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hq : Real.log Q ≤ Real.log (X*Q) := by
    rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
    linarith
  calc
    _ ≤ (Real.log (X*Q))^2 := by nlinarith
    _ ≤ (X*Real.exp (-c*Real.log X/primeContourDenominator Q X))*(Real.log (X*Q))^2 :=
      le_mul_of_one_le_left (sq_nonneg _) hv
    _ = _ := by unfold primeCancellationWeight; ring

theorem primary_angular_prime_bound_of_primitive {q d : Eisenstein}
    (hq : q ≠ 0) (hd : d ≠ 0) (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ψ : MulChar (Residues d) ℂ)
    (hi : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    {B c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hQ : 1 ≤ Q)
    (hqQ : norm q ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hmain : ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ B*primeCancellationWeight c Q X) :
    ‖primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X‖ ≤
      (B+1)*primeCancellationWeight c Q X := by
  have herr := (induced_angular_prime_error hq hd hi ℓ X).trans
    ((Real.log_le_log (norm_pos_of_ne_zero hq) hqQ).trans (primeCancellation_log_cost hc hc1 hQ hXp hX))
  rw [angular_primeChebyshev_eq_ideal h3 χ ℓ hu]
  calc
    _ = ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X+
        (idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖+
        ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
          idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ := norm_add_le _ _
    _ ≤ B*primeCancellationWeight c Q X+primeCancellationWeight c Q X := add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveCharacterStar
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the actual finite conductor. For a cubic
character, its square is precisely its conjugate, including the zero extension. -/
noncomputable section
namespace CubicFirstMoment

lemma ResidueCharacterInduces.star {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) :
    ResidueCharacterInduces q d (star χ) (star ψ) := by
  refine ⟨h.1,?_⟩
  intro x hx
  exact congrArg (Star.star : ℂ → ℂ) (h.2 x hx)

lemma PrimitiveResidueCharacter.star {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : PrimitiveResidueCharacter q χ) : PrimitiveResidueCharacter q (star χ) := by
  intro d ψ hi
  apply h d (Star.star ψ)
  simpa only [star_star] using hi.star

lemma cubic_residue_character_sq_eq_star {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (h3 : χ^3=1) : χ^2=star χ := by
  let : Finite (Residues q) := finite_residues hq
  rw [MulChar.star_eq_inv]
  have he : χ^2*χ=1 := by simpa only [←pow_succ] using h3
  calc
    χ^2 = (χ^2*χ)*χ⁻¹ := by group
    _ = χ⁻¹ := by rw [he,one_mul]

lemma star_residue_character_ne_one {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : χ ≠ 1) : star χ ≠ 1 := by
  intro he
  have hh := congrArg star he
  simp only [star_star,star_one] at hh
  exact h hh

lemma star_residue_character_units {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1) :
    ∀ u : Eisensteinˣ, (star χ) (Ideal.Quotient.mk (modulus q) u)=1 := by
  intro u
  rw [MulChar.star_apply,h u,star_one]

lemma residueIdealChar_cubic_square {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (h3 : χ^3=1) (ν : EisensteinIdealExponent) :
    (residueIdealChar q χ ν)^2=residueIdealChar q (star χ) ν := by
  rw [←cubic_residue_character_sq_eq_star hq χ h3]
  exact (MulChar.pow_apply' χ (by norm_num : (2:ℕ) ≠ 0) _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveCubicPrimeEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The character and square analytic data in the sharp prime theorem
are supplied by primitive Hecke completion for a cubic finite character.
Conjugation preserves its conductor and supplies precisely its square. -/
noncomputable section
namespace CubicFirstMoment

theorem primitive_cubic_prime_ideal_estimate (hpub : PrimitiveResidueHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → χ ≠ 1 → χ^3=1 →
    (∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1) →
    ∀ Q : ℝ, 1 ≤ Q → residueHeckeScale q ≤ Q → 7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (residueIdealChar q χ) X‖ ≤
      B*primeCancellationWeight c Q X := by
  obtain ⟨B,c,X0,hB,hc,hc1,hX0,hbound⟩ := hecke_prime_ideal_bound_of_analytic_pair
  refine ⟨B,c,X0,hB,hc,hc1,hX0,?_⟩
  intro q hq χ hp hn h3 hu Q hQ hA h7 X hX
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub q hq χ hp hn hu
  obtain ⟨root2,L2,L2dual,hr2,hL2,hs2,hds2,hFE2,hcomp2⟩ :=
    hpub q hq (star χ) hp.star (star_residue_character_ne_one hn) (star_residue_character_units hu)
  have hs2' : ∀ s : ℂ, 1 < s.re → L2 s=
      normDirichletSeries (fun ν => (residueIdealChar q χ ν)^2) idealExponentNorm s := by
    intro s hss
    rw [hs2 s hss]
    congr 1
    ext ν
    exact (residueIdealChar_cubic_square hq χ h3 ν).symm
  have hds2' : ∀ s : ℂ, 1 < s.re → L2dual s=
      normDirichletSeries (residueIdealChar q χ) idealExponentNorm s := by
    simpa only [star_star] using hds2
  have hcomp' : ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) 0 L := by
    simpa only [ShiftedCompletedHeckeFiniteOrder,CompletedHeckeFiniteOrder,Complex.ofReal_zero,add_zero] using hcomp
  have hcomp2' : ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) 0 L2 := by
    simpa only [ShiftedCompletedHeckeFiniteOrder,CompletedHeckeFiniteOrder,Complex.ofReal_zero,add_zero] using hcomp2
  apply hbound (residueIdealChar_norm_le_one hq χ) _ (residueIdealChar_add q χ)
    (residueIdealChar_norm_le_one hq (star χ)) (residueIdealChar_norm_le_one hq χ)
    hL hL2 hs hs2' hds hds2' (residueHeckeScale_pos hq) (residueHeckeScale_pos hq)
    (by norm_num) (by norm_num) hr.le hr2.le hQ hA hA (by simpa using h7) (by simpa using h7)
    hFE hFE2 hcomp' hcomp2' X hX
  simp [residueIdealChar,idealExponentGenerator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KummerChebyshevFromPrimitive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubic-symbol prime sum for every nonzero noncube numerator,
from the primitive Hecke completion input and proved elementary reciprocity. -/
noncomputable section
namespace CubicFirstMoment

theorem kummer_chebyshev_from_primitive (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3=v) →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeChebyshev (fun p => cubicSymbol p v) X‖ ≤
        B*primeCancellationWeight c (810*norm v) X := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := primitive_cubic_prime_ideal_estimate hpub
  let X0 := max Y0 (Real.exp 2)
  refine ⟨B+1,c,X0,by linarith,hc,hc1,hY0.trans_le (le_max_left _ _),?_⟩
  intro v hv hnc X hX
  obtain ⟨d,ψ,hd,hp,_hdiv,hN,h3,hu,hi,_hval⟩ := cubicNumerator_primitive_conductor hperiod hv
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hperiod v hv).mp
    (cubicNumeratorChar_noncube hperiod hv hnc)
  have hψ : ψ ≠ 1 := hi.nonprincipal ⟨x,hcop,by
    rwa [cubicNumeratorChar_primary hperiod v hv hx]⟩
  obtain ⟨hQ,hscale,h7,hqQ⟩ := cubicNumerator_primitive_scale hv hd hN
  have hmain := hbound d hd ψ hp hψ h3 hu (810*norm v) hQ hscale h7 X
    ((le_max_left _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos 2).trans_le ((le_max_right _ _).trans hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hu0 : AngularUnitCompatible (9*v) (cubicNumeratorChar hperiod v hv) 0 := by
    intro u
    simpa only [theta_zero,mul_one] using cubicNumeratorChar_units hperiod v hv u
  have hh := primary_angular_prime_bound_of_primitive
    (mul_ne_zero (by norm_num : (9:Eisenstein) ≠ 0) hv) hd
    (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩)
    (cubicNumeratorChar hperiod v hv) ψ hi 0 hu0 hc.le hc1 hQ hqQ hXp hLX
    (by simpa only [angularResidueIdealChar_zero] using hmain)
  have he : primeChebyshev (fun p => (cubicNumeratorChar hperiod v hv)
      (Ideal.Quotient.mk (modulus (9*v)) p)*theta 0 p) X =
      primeChebyshev (fun p => cubicSymbol p v) X := by
    unfold primeChebyshev
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [cubicNumeratorChar_primary hperiod v hv (mem_primeCutoff.mp hp).1.1,theta_zero,mul_one]
  rwa [he] at hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicReconstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime sums satisfy the small-argument and local-growth
conditions of dyadic reconstruction; closed interval endpoints cost O(1). -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_on (c : Eisenstein → ℂ) {X Y : ℝ} (hXY : X ≤ Y) :
    primeCutoffSum c X = ∑ p ∈ primeCutoff Y, if norm p ≤ X then c p else 0 := by
  have hs : primeCutoff X = (primeCutoff Y).filter (fun p => norm p ≤ X) := by
    ext p
    simp only [mem_primeCutoff,Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨⟨hp.1,hp.2.trans hXY⟩,hp.2⟩
    · intro hp
      exact ⟨hp.1.1,hp.2⟩
  rw [primeCutoffSum_eq_sum,hs,Finset.sum_filter]

lemma primeCutoffSum_norm_le (c : Eisenstein → ℂ) {M X : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M) (hX : 0 ≤ X) :
    ‖primeCutoffSum c X‖ ≤ 18*M*X := by
  have hsub : primeCutoff X ⊆ nonzeroNormBall X := by
    intro p hp
    have hh := mem_primeCutoff.mp hp
    exact mem_nonzeroNormBall.mpr ⟨hh.2,hh.1.2.ne_zero⟩
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hX)
  rw [primeCutoffSum_eq_sum]
  calc
    _ ≤ ∑ _p ∈ primeCutoff X, M := (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun p hp => hc p (mem_primeCutoff.mp hp).1))
    _ = ((primeCutoff X).card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (18*X)*M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeChebyshevDeweight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the logarithmic prime weight by Abel summation above sqrt X.
The small primes are bounded by the actual Eisenstein lattice count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma primeCutoffSum_split (ψ : Eisenstein → ℂ) {a b : ℝ} (hab : a ≤ b) :
    primeCutoffSum ψ b = primeCutoffSum ψ a +
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), ψ p := by
  classical
  rw [primeCutoffSum_on ψ hab, primeCutoffSum_eq_sum, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : norm p ≤ a
  · simp [hp,not_lt_of_ge hp]
  · simp [hp,lt_of_not_ge hp]

lemma inverseLogWeight_prime_cancel (ψ : Eisenstein → ℂ) {p : Eisenstein}
    (hp : 1 < norm p) :
    inverseLogWeight (norm p) * (ψ p * (Real.log (norm p) : ℂ)) = ψ p := by
  have hn : (Real.log (norm p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hp).ne'
  unfold inverseLogWeight
  push_cast
  field_simp

lemma primeChebyshev_deweight (ψ : Eisenstein → ℂ) {B c Q X X0 : ℝ}
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hL : 2 ≤ Real.log X) (hX0 : X0 ≤ Real.sqrt X)
    (hmain : ∀ t, X0 ≤ t →
      ‖primeChebyshev ψ t‖ ≤ B*primeCancellationWeight c Q t) :
    ‖primeCutoffSum ψ X‖ ≤ (2*B+18)*primeCancellationWeight (c/2) Q X := by
  have hx1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa only [Real.exp_zero,Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := (Real.sqrt_le_iff).mpr ⟨hXp.le,by nlinarith⟩
  have hrootp : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hrootexp : Real.exp 1 ≤ Real.sqrt X := by
    apply (Real.le_log_iff_exp_le hrootp).mp
    rw [Real.log_sqrt hXp.le]
    linarith
  have hroot1 : 1 < Real.sqrt X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hrootexp
  let H := B*primeCancellationWeight (c/2) Q X
  have hH : 0 ≤ H := by unfold H primeCancellationWeight; positivity
  have hprefix (t : ℝ) (ht : t ∈ Icc (Real.sqrt X) X) :
      ‖primeChebyshev ψ t‖ ≤ H := by
    apply (hmain t (hX0.trans ht.1)).trans
    apply (mul_le_mul_of_nonneg_left
      (primeDyadic_majorant_compare hc hQ hXp hL ht.1 ht.2) hB).trans
    unfold H primeCancellationWeight
    gcongr
    exact ht.2
  have hw := weighted_prime_bound
    (fun p => ψ p*(Real.log (norm p):ℂ)) inverseLogWeight hrootp.le hroot
    (fun t ht => (inverseLogWeight_hasDerivAt (hroot1.trans_le ht.1)).differentiableAt)
    (inverseLogWeight_integrableOn_deriv hroot1) hprefix
  have hsum : (∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
      inverseLogWeight (norm p)*(ψ p*(Real.log (norm p):ℂ))) =
      ∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p), ψ p := by
    classical
    apply Finset.sum_congr rfl
    intro p hp
    exact inverseLogWeight_prime_cancel ψ
      (hroot1.trans (Finset.mem_filter.mp hp).2)
  rw [hsum] at hw
  have hlarge : ‖∑ p ∈ (primeCutoff X).filter
      (fun p => Real.sqrt X < norm p), ψ p‖ ≤ 2*H :=
    hw.trans ((mul_le_mul_of_nonneg_left
      (inverseLogWeight_variation hrootexp hroot) hH).trans_eq (by ring))
  have hsmall := primeCutoffSum_norm_le ψ (by norm_num : (0:ℝ)≤1) hψ hrootp.le
  have hsqrt : Real.sqrt X ≤ primeCancellationWeight (c/2) Q X := by
    have hh := primeDyadic_sqrt_absorption hc hc1 hQ hXp hL hroot le_rfl
    have hP := (primeLogSize_bounds hQ hXp (by linarith : 1 ≤ Real.log X)).1
    unfold primeCancellationWeight
    calc
      _ ≤ X*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := hh
      _ = X*1*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by nlinarith : (1:ℝ)≤(Real.log (X*Q))^2) hXp.le)
        (Real.exp_pos _).le
  rw [primeCutoffSum_split ψ hroot]
  apply (norm_add_le _ _).trans
  have hs : ‖primeCutoffSum ψ (Real.sqrt X)‖ ≤
      18*primeCancellationWeight (c/2) Q X := hsmall.trans (by nlinarith [hsqrt])
  calc
    _ ≤ 18*primeCancellationWeight (c/2) Q X+2*H := add_le_add hs hlarge
    _ = _ := by unfold H; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KummerPrimeFromPrimitive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw Kummer prime input follows from primitive finite-character
Hecke completion, with all prime-sum estimates and deweighting derived. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primeCancellationWeight_le_heckeError {c Q X : ℝ} (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hL : 1 ≤ Real.log X) :
    primeCancellationWeight c Q X ≤ heckeExponentialError c X Q := by
  have hP := (primeLogSize_bounds hQ hXp hL).1
  have hpow : (Real.log (X*Q))^2 ≤ (Real.log (X*Q))^4 := by nlinarith [sq_nonneg ((Real.log (X*Q))^2-1)]
  unfold primeCancellationWeight heckeExponentialError primeContourDenominator
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hXp.le) (Real.exp_pos _).le

theorem kummer_unweighted_from_primitive (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ 1 < X0 ∧
    ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3=v) →
    ∀ X : ℝ, X0 ≤ X →
      ‖primeCutoffSum (fun p => cubicSymbol p v) X‖ ≤
        B*primeCancellationWeight c (810*norm v) X := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := kummer_chebyshev_from_primitive hpub hperiod
  refine ⟨2*B+18,c/2,max (Y0^2) (Real.exp 2),by positivity,by positivity,?_,?_⟩
  · exact (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<2)).trans_le (le_max_right _ _)
  intro v hv hnc X hX
  have hXp : 0 < X := (Real.exp_pos 2).trans_le ((le_max_right _ _).trans hX)
  have hL : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hroot : Y0 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le ((le_max_left _ _).trans hX)
  have hQ : 1 ≤ 810*norm v := by nlinarith [one_le_norm hv]
  exact primeChebyshev_deweight (fun p => cubicSymbol p v)
    (fun p hp => norm_cubicSymbol_le_one hp.1 v) hB.le hc.le (by linarith) hQ hXp hL hroot
    (fun t ht => hbound v hv hnc t ht)

theorem kummerPrimeSiegelWalfisz_of_primitive_oai (hpub : PrimitiveResidueHeckeInput) :
    KummerPrimeSiegelWalfisz := by
  obtain ⟨B,c,Y0,hB,hc,hY0,hbound⟩ :=
    kummer_unweighted_from_primitive hpub cubicSupplementaryPeriodicity_proved
  intro A D _hA _hD
  have herr := heckeExponentialError_logSaving (K := 810) (A := A) (D := D) hc (by norm_num)
  obtain ⟨X1,hX1⟩ := eventually_atTop.mp herr
  refine ⟨16*B,max Y0 (max X1 (Real.exp 2)),by positivity,hY0.trans_le (le_max_left _ _),?_⟩
  intro X hX v hv hnc hcon
  have hXY : Y0 ≤ X := (le_max_left _ _).trans hX
  have hXX : X1 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hXe
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) hXe
    rw [Real.log_exp] at hh
    linarith
  have hQ : 1 ≤ 810*norm v := by nlinarith [one_le_norm hv]
  calc
    _ ≤ B*primeCancellationWeight c (810*norm v) X := hbound v hv hnc X hXY
    _ ≤ B*heckeExponentialError c X (810*norm v) :=
      mul_le_mul_of_nonneg_left (primeCancellationWeight_le_heckeError hQ hXp hL) hB.le
    _ ≤ B*(16*X/(Real.log X)^D) := mul_le_mul_of_nonneg_left
      (hX1 X hXX _ hQ (mul_le_mul_of_nonneg_left hcon (by norm_num))) hB.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive_oai := @OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive_oai
