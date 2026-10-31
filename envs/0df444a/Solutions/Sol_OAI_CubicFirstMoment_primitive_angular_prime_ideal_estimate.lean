-- Prove2me | solution 1 for OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:24:59.397239+00:00
-- url     : https://prove2.me/submissions/df7dc34c-656d-4aa7-a998-0498b0fd099b

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026
import Theorems.Thm_OAI_CubicFirstMoment_hecke_logDeriv_norm_uniform_from_square_disk
import Theorems.Thm_OAI_CubicFirstMoment_hecke_zero_free_log_from_square_disk

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFunctionalEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

theorem hecke_uncompleted {A k : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A k ε L Ldual) (s : ℂ)
    (hG : Complex.Gamma (s+(k:ℂ)) ≠ 0)
    (hGdual : Complex.Gamma (1-s+(k:ℂ)) ≠ 0) :
    L s = ε*(A:ℂ)^(1-2*s) *
      (Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))) * Ldual (1-s) := by
  have ha : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hap : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ha)
  have hp : (A:ℂ)^s*(A:ℂ)^(1-2*s) = (A:ℂ)^(1-s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero hap hG)
  calc
    _ = ε*((A:ℂ)^(1-s)*Complex.Gamma (1-s+(k:ℂ))*Ldual (1-s)) := hFE s hG hGdual
    _ = _ := by
      field_simp [hG]
      rw [← hp]
      rw [show (1-s*2:ℂ) = 1-2*s by ring]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularGamma
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far-left Gamma quotient for a fixed angular parameter. Its two
arguments differ, after conjugation, by the integer `2m` independently
of the angular order. Possible Gamma poles are retained explicitly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma angular_norm_ascPochhammer_le (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval,norm_mul]
      have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by
        simpa using norm_add_le z (n:ℂ)
      calc
        _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
          mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
        _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
        _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          linarith

theorem norm_angular_gamma_left_ratio_le {k : ℝ} (hk : 0 ≤ k) (m : ℕ) (u : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I)‖ ≤
        (k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I
  by_cases hG : Complex.Gamma z = 0
  · change ‖_ / Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    positivity
  have hreg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n hn
    apply hG
    rw [hn,Complex.Gamma_neg_nat_eq_zero]
  have he : ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z hreg
  have hn : ‖z‖ ≤ k+(m:ℝ)+1+|u| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)+(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := by simp [abs_of_nonneg hk]; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := angular_norm_ascPochhammer_le _ _
    _ ≤ ((k+3*(m:ℝ)+1)*(1+|u|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg u, show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

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

lemma ResidueCharacterInduces.restriction {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (x : Eisenstein) :
    χ (Ideal.Quotient.mk (modulus q) x) =
      if IsCoprime q x then ψ (Ideal.Quotient.mk (modulus d) x) else 0 := by
  by_cases hx : IsCoprime q x
  · rw [ite_eq_left hx,h.2 x hx]
  · rw [ite_eq_right hx]
    exact MulChar.map_nonunit χ (fun hu => hx (isCoprime_of_residue_isUnit hu))

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

lemma ResidueCharacterInduces.angular_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) {ℓ : ℤ}
    (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible d ψ ℓ := by
  intro u
  rw [h.2 u (show IsCoprime q (u:Eisenstein) from ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩)]
  exact hu u

lemma angularResidueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν κ : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ (ν+κ) =
      angularResidueIdealChar q χ ℓ ν*angularResidueIdealChar q χ ℓ κ := by
  simp only [angularResidueIdealChar, residueIdealChar_add, idealExponentGenerator_add, theta_mul]
  ring

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialStrip
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth from finite order and polynomial boundary
bounds. The finite-order hypothesis is much weaker than the conclusion;
the proof uses the Phragmén–Lindelöf theorem in mathlib. -/

noncomputable section
open Set Filter Asymptotics
namespace CubicFirstMoment

lemma finiteVerticalOrder_double_exp {f : ℂ → ℂ} {a b c : ℝ}
    (hf : FiniteVerticalOrder f a b) (hc : 0 < c) :
    f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      (fun z : ℂ => Real.exp (Real.exp (c*|z.im|))) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  have he := ((isLittleO_pow_exp_pos_mul_atTop k hc).const_mul_left (C*2^k)).bound
    (by norm_num : (0:ℝ) < 1)
  have hlarge : ∀ᶠ u : ℝ in atTop,
      C*(1+u)^k ≤ Real.exp (c*u) := by
    filter_upwards [he,eventually_ge_atTop (1:ℝ)] with u hu hu1
    have hu0 : 0 ≤ u := le_trans zero_le_one hu1
    have hpow : (1+u)^k ≤ (2*u)^k := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      C*(1+u)^k ≤ C*(2*u)^k := mul_le_mul_of_nonneg_left hpow hC
      _ = (C*2^k)*u^k := by rw [mul_pow]; ring
      _ ≤ Real.exp (c*u) := by
        exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul] using hu)
  apply IsBigO.of_bound' 
  have hlarge' := ((tendsto_comap : Tendsto (abs ∘ Complex.im) (comap (abs ∘ Complex.im) atTop) atTop).eventually hlarge).filter_mono (inf_le_left :
    comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b) ≤
      comap (abs ∘ Complex.im) atTop)
  have hs : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo a b), z.re ∈ Ioo a b :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [hlarge',hs] with z hz hzstrip
  exact (hf z ⟨hzstrip.1.le,hzstrip.2.le⟩).trans <| by
    simpa using Real.exp_le_exp.mpr hz

private lemma strip_shift_norm_lower {a : ℝ} {z : ℂ} (hz : a ≤ z.re) :
    1 ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
  have hr := Complex.re_le_norm (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re] at hr
  linarith

private lemma strip_shift_norm_upper {a b : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc a b) :
    ‖z+((1-a:ℝ):ℂ)‖ ≤ (b-a+1)*(1+|z.im|) := by
  have hn := Complex.norm_le_abs_re_add_abs_im (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero] at hn
  rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z.re+(1-a))] at hn
  nlinarith [abs_nonneg z.im,hz.1,hz.2]

/-- A finite-order holomorphic function with polynomial bounds on both
vertical edges has polynomial growth throughout the strip. -/
theorem polynomial_strip_of_finite_order {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a < b) (hfd : Differentiable ℂ f) (hf : FiniteVerticalOrder f a b)
    (hC : 0 ≤ C) (n : ℕ)
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C*(1+|z.im|)^n)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C*(1+|z.im|)^n) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ (C*2^n*(b-a+1)^n)*(1+|z.im|)^n := by
  let g (z : ℂ) := f z/(z+((1-a:ℝ):ℂ))^n
  have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le,hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hne {z : ℂ} (hz : a ≤ z.re) : z+((1-a:ℝ):ℂ) ≠ 0 := by
    have hn := strip_shift_norm_lower hz
    intro he
    rw [he,norm_zero] at hn
    norm_num at hn
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact (hfd z).differentiableWithinAt.div
      (((differentiable_id.add_const ((1-a:ℝ):ℂ)).pow n) z).differentiableWithinAt
      (pow_ne_zero _ (hne (hcl hz).1))
  have hgnorm {z : ℂ} (hz : a ≤ z.re) : ‖g z‖ ≤ ‖f z‖ := by
    dsimp [g]
    rw [norm_div,norm_pow]
    exact div_le_self (_root_.norm_nonneg _) (one_le_pow₀ (strip_shift_norm_lower hz))
  have hgf : FiniteVerticalOrder g a b := by
    obtain ⟨D,k,hD,hf⟩ := hf
    exact ⟨D,k,hD,fun z hz => (hgnorm hz.1).trans (hf z hz)⟩
  have hboundary {z : ℂ} (hz : z.re ∈ Icc a b)
      (hfz : ‖f z‖ ≤ C*(1+|z.im|)^n) : ‖g z‖ ≤ C*2^n := by
    have hn := strip_shift_norm_lower hz.1
    have hi : |z.im| ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (z+((1-a:ℝ):ℂ))
    have hpow : (1+|z.im|)^n ≤ (2*‖z+((1-a:ℝ):ℂ)‖)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    dsimp [g]
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hn) _)).mpr
    calc
      ‖f z‖ ≤ C*(1+|z.im|)^n := hfz
      _ ≤ C*(2*‖z+((1-a:ℝ):ℂ)‖)^n := mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by rw [mul_pow]; ring
  have hc : 0 < Real.pi/(2*(b-a)) := div_pos Real.pi_pos (by linarith)
  have hcb : Real.pi/(2*(b-a)) < Real.pi/(b-a) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)
  intro z hz
  have hg : ‖g z‖ ≤ C*2^n := PhragmenLindelof.vertical_strip hgd
    ⟨Real.pi/(2*(b-a)),hcb,1,by
      simpa only [one_mul] using finiteVerticalOrder_double_exp hgf hc⟩
    (fun w hw => hboundary ⟨hw.ge,hw ▸ hab.le⟩ (ha w hw))
    (fun w hw => hboundary ⟨hw ▸ hab.le,hw.le⟩ (hb w hw)) hz.1 hz.2
  have hfeq : ‖f z‖ = ‖g z‖*‖z+((1-a:ℝ):ℂ)‖^n := by
    dsimp [g]
    rw [norm_div,norm_pow,div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne hz.1)))]
  rw [hfeq]
  calc
    _ ≤ (C*2^n)*((b-a+1)*(1+|z.im|))^n :=
      mul_le_mul hg (pow_le_pow_left₀ (_root_.norm_nonneg _) (strip_shift_norm_upper hz) n)
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeStripGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial strip-growth field used by the Mellin proof follows
from finite order, absolute convergence, and the functional equation.
No polynomial strip bound is assumed in the input structure here. -/

noncomputable section
open Set
namespace CubicFirstMoment

lemma norm_idealDirichlet_le_zeta_two (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤
      ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) := by
  have hb := summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)
  have hf (ν : EisensteinIdealExponent) :
      ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-(2:ℝ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
      (Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (neg_le_neg hs))
  have hfn : Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖) :=
    hb.of_norm_bounded (fun ν => by simpa only [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)] using hf ν)
  exact (norm_tsum_le_tsum_norm hfn).trans (Summable.tsum_le_tsum hf hfn hb)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeGrowth
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth for the shifted completion Gamma(s+k).
The input is the ordinary entire order-one completion, expressed by a
coarse quadratic exponential bound. All strip bounds are derived. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma shifted_completed_hecke_decompletion {A k : ℝ} (hA : 0 < A)
    {L Λ : ℂ → ℂ} (hL : Continuous L) (hΛ : Continuous Λ)
    (heq : ∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 → Λ s = heckeCompleted A k L s) :
    L = fun s : ℂ => (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  apply Continuous.ext_on
    ((Set.countable_range (fun n : ℕ => -(n:ℂ)-(k:ℂ))).dense_compl ℂ)
    hL (((differentiable_const_cpow_of_neZero (A:ℂ)).continuous.comp continuous_neg).mul
      (Complex.differentiable_one_div_Gamma.continuous.comp
        (continuous_id.add continuous_const)) |>.mul hΛ)
  intro s hs
  have hG : Complex.Gamma (s+(k:ℂ)) ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    apply hs
    refine ⟨n,?_⟩
    linear_combination -hn)
  change L s = (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s
  rw [heq s hG,heckeCompleted,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  field_simp

theorem shifted_completed_finiteVerticalOrder {A k : ℝ} (hA : 0 < A)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) {a b : ℝ}
    (hGamma : GammaInverseFiniteOrder (a+k) (b+k)) : FiniteVerticalOrder L a b := by
  obtain ⟨Λ,hΛ,heq,C,hC,hbound⟩ := hcomp
  obtain ⟨B,hB,hGamma⟩ := hGamma
  have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
  let R : ℝ := 1+|a|+|b|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a,abs_nonneg b]
  refine ⟨R*|Real.log A|+C*R^2+B,2,by positivity,?_⟩
  intro s hs
  have hreal : |s.re| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hs.1]
    · linarith [le_abs_self b,abs_nonneg a,hs.2]
  have hn : 1+‖s‖ ≤ R*(1+|s.im|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    dsimp [R]
    nlinarith [abs_nonneg a,abs_nonneg b,abs_nonneg s.im]
  have hnsq : (1+‖s‖)^2 ≤ R^2*(1+|s.im|)^2 := by
    calc
      _ ≤ (R*(1+|s.im|))^2 := pow_le_pow_left₀ (by positivity) hn _
      _ = _ := mul_pow _ _ _
  have haexp : ‖(A:ℂ)^(-s)‖ ≤ Real.exp (R*|Real.log A|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA,Complex.neg_re,Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A*(-s.re) ≤ |Real.log A*(-s.re)| := le_abs_self _
      _ = |Real.log A| *|s.re| := by rw [abs_mul,abs_neg]
      _ ≤ |Real.log A| *R := mul_le_mul_of_nonneg_left
        (hreal.trans (by dsimp [R]; linarith)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hg : ‖(Complex.Gamma (s+(k:ℂ)))⁻¹‖ ≤ Real.exp (B*(1+|s.im|)^2) := by
    simpa using hGamma (s+(k:ℂ)) (by simpa using
      (show a+k ≤ s.re+k ∧ s.re+k ≤ b+k from
        ⟨by linarith [hs.1],by linarith [hs.2]⟩))
  have hp : 1 ≤ (1+|s.im|)^2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rw [congrFun hdec s,norm_mul,norm_mul]
  calc
    _ ≤ Real.exp (R*|Real.log A|)*Real.exp (B*(1+|s.im|)^2)*
        Real.exp (C*(1+‖s‖)^2) :=
      mul_le_mul (mul_le_mul haexp hg (_root_.norm_nonneg _) (Real.exp_pos _).le)
        (hbound s) (_root_.norm_nonneg _) (by positivity)
    _ = Real.exp (R*|Real.log A|+B*(1+|s.im|)^2+C*(1+‖s‖)^2) := by
      rw [←Real.exp_add,←Real.exp_add]
    _ ≤ Real.exp ((R*|Real.log A|+C*R^2+B)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ R*|Real.log A| by positivity)
      have h2 := mul_le_mul_of_nonneg_left hnsq hC
      nlinarith

lemma angular_hecke_left_boundary (χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hd : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    ‖L ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (‖ε‖*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))))*(1+|u|)^(2*m) := by
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 2 ≤ (1-s).re := by dsimp [s]; simp; linarith
  have hS : 0 ≤ ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) :=
    tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  by_cases hG : Complex.Gamma (s+(k:ℂ)) = 0
  · obtain ⟨Λ,hΛ,heq,-⟩ := hcomp
    have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
    change ‖L s‖ ≤ _
    rw [congrFun hdec s,hG,inv_zero,mul_zero,zero_mul,norm_zero]
    positivity
  have hGd : Complex.Gamma (1-s+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  have he := hecke_uncompleted hA hFE s hG hGd
  rw [hd _ (by linarith)] at he
  have hp : ‖(A:ℂ)^(1-2*s)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*s).re = ((2*m:ℕ):ℝ) := by dsimp [s]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hg : ‖Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))‖ ≤
      (k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
    have heq : 1-s+(k:ℂ) = (1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    have heq2 : s+(k:ℂ) = (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    rw [heq,heq2]
    exact norm_angular_gamma_left_ratio_le hk m u
  change ‖L s‖ ≤ _
  rw [he,norm_mul,norm_mul,norm_mul,hp]
  calc
    _ ≤ (‖ε‖*A^(2*m))*((k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (norm_idealDirichlet_le_zeta_two χdual hχdual (1-s) hr)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

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

lemma idealExponentNorm_primeSet (S : Finset EisensteinIdealPrime) :
    idealExponentNorm (primeSetExponent S) =
      ∏ p ∈ S, idealExponentNorm (Finsupp.single p 1) := by
  induction S using Finset.induction_on with
  | empty => simp [primeSetExponent,idealExponentNorm,idealExponentGenerator]
  | @insert p S hp ih =>
    simp only [primeSetExponent,Finset.sum_insert hp,idealExponentNorm_add,Finset.prod_insert hp] at *
    rw [ih]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Euler factors for the complete ideal Dirichlet series.
These retain the ramified factors lost in primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeIdealRestriction_norm_le (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (ν : EisensteinIdealExponent) :
    ‖primeIdealRestriction S χ ν‖ ≤ 1 := by
  unfold primeIdealRestriction
  split_ifs
  · exact hχ ν
  · simp

lemma primeIdealRestriction_add (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (ν κ : EisensteinIdealExponent) :
    primeIdealRestriction S χ (ν+κ)=primeIdealRestriction S χ ν*primeIdealRestriction S χ κ := by
  have hz : (∀ p ∈ S, (ν+κ) p=0) ↔ (∀ p ∈ S, ν p=0) ∧ (∀ p ∈ S, κ p=0) := by
    simp only [Finsupp.add_apply,Nat.add_eq_zero_iff,forall_and]
  unfold primeIdealRestriction
  simp only [hz,hχ]
  split_ifs <;> simp_all

lemma primeIdealRestriction_insert (S : Finset EisensteinIdealPrime) (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) :
    primeIdealRestriction (insert p S) χ = primeIdealRestriction {p} (primeIdealRestriction S χ) := by
  funext ν
  simp only [primeIdealRestriction,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,
    forall_eq]
  split_ifs <;> simp_all

lemma idealDirichlet_single_exclusion (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction {p} χ) idealExponentNorm s =
      (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))*
        normDirichletSeries χ idealExponentNorm s := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := if δ ≤ ν then f ν else 0
  have hf : Summable f := (idealDirichlet_norm_summable χ hχ hs).of_norm
  have hg : Summable g := by
    convert hf.indicator {ν | δ ≤ ν} using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    by_cases hν : δ ≤ ν <;> simp [g,Set.indicator,hν]
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hshift : (∑' ν, g ν)=f δ*(∑' ν, f ν) := by
    have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
      intro ν hν
      have hd : δ ≤ ν := by
        by_contra hn
        exact hν (by simp [g,hn])
      exact ⟨ν-δ,add_tsub_cancel_of_le hd⟩
    rw [←hi.tsum_eq hsup]
    simp only [g,le_add_of_nonneg_right zero_le,ite_true, if_true]
    simp_rw [show ∀ ν, f (δ+ν)=f δ*f ν from fun ν => idealDirichlet_weight_add χ hadd s δ ν]
    exact tsum_mul_left
  have he (ν : EisensteinIdealExponent) :
      primeIdealRestriction {p} χ ν*(idealExponentNorm ν:ℂ)^(-s)=f ν-g ν := by
    have hd : δ ≤ ν ↔ 0 < ν p := by
      simp only [δ,Finsupp.single_le_iff,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
    simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
    by_cases hp : ν p=0
    · simp [f,g,hd,hp]
    · simp [f,g,hd,hp,Nat.pos_of_ne_zero hp]
  unfold normDirichletSeries
  simp_rw [he]
  rw [hf.tsum_sub hg,hshift]
  dsimp only [f,δ]
  ring

theorem idealDirichlet_euler_exclusion (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction S χ) idealExponentNorm s =
      idealEulerFactor S χ s*normDirichletSeries χ idealExponentNorm s := by
  induction S using Finset.induction_on with
  | empty => simp [primeIdealRestriction,idealEulerFactor,normDirichletSeries]
  | @insert p S hp ih =>
      rw [primeIdealRestriction_insert,idealDirichlet_single_exclusion p _
        (primeIdealRestriction_norm_le S χ hχ) (primeIdealRestriction_add S χ hadd) hs,ih,
        primeIdealRestriction_single,ite_eq_right hp]
      simp only [idealEulerFactor,Finset.prod_insert hp]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerFactorBounds
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler correction is entire and has an explicit norm bound
in the strip used by the angular prime zero-free argument. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealEulerFactor_differentiable (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) : Differentiable ℂ (idealEulerFactor S χ) := by
  unfold idealEulerFactor
  apply Differentiable.fun_finsetProd
  intro p _
  have hN : NeZero (idealExponentNorm (Finsupp.single p 1) : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos _).ne'⟩
  apply Differentiable.sub (differentiable_const (1:ℂ))
  apply Differentiable.mul (differentiable_const (χ (Finsupp.single p 1)))
  exact (differentiable_const_cpow_of_neZero _).comp differentiable_neg

lemma idealEulerFactor_norm_bound (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ}
    (hs : -(3/2:ℝ) ≤ s.re) :
    ‖idealEulerFactor S χ s‖ ≤ (idealExponentNorm (primeSetExponent S))^3 := by
  have hsingle (p : EisensteinIdealPrime) :
      ‖1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s)‖ ≤
        (idealExponentNorm (Finsupp.single p 1))^3 := by
    let N := idealExponentNorm (Finsupp.single p 1)
    have hN : 2 ≤ N := by
      dsimp only [N]
      rw [idealExponentNorm_single,pow_one]
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    have hp : 0 < N := by linarith
    have he : N^(-s.re) ≤ N^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_two] at he
    calc
      _ ≤ 1+‖χ (Finsupp.single p 1)‖*N^(-s.re) := by
        simpa only [norm_one,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.neg_re]
          using norm_sub_le (1:ℂ) (χ (Finsupp.single p 1)*(N:ℂ)^(-s))
      _ ≤ 1+N^2 := by
        have hh := mul_le_of_le_one_left (Real.rpow_nonneg hp.le (-s.re)) (hχ (Finsupp.single p 1))
        linarith
      _ ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
  rw [idealEulerFactor,norm_prod]
  calc
    _ ≤ ∏ p ∈ S, (idealExponentNorm (Finsupp.single p 1))^3 :=
      Finset.prod_le_prod (fun p _ => _root_.norm_nonneg _) (fun p _ => hsingle p)
    _ = _ := by rw [Finset.prod_pow,idealExponentNorm_primeSet]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquareCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of a fixed nonzero angular character is completed through
its own primitive conductor. The omitted Euler factors are retained. -/
noncomputable section
namespace CubicFirstMoment

lemma angularResidueIdealChar_square (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    angularResidueIdealChar q (χ^2) (2*ℓ) ν = (angularResidueIdealChar q χ ℓ ν)^2 := by
  unfold angularResidueIdealChar residueIdealChar
  rw [MulChar.pow_apply' χ (by norm_num : (2:ℕ)≠0)]
  rw [show 2*ℓ=ℓ+ℓ by ring,theta_add ℓ ℓ (idealExponentGenerator_ne_zero ν)]
  ring

lemma AngularUnitCompatible.square {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ) : AngularUnitCompatible q (χ^2) (2*ℓ) := by
  intro u
  rw [MulChar.pow_apply' χ (by norm_num : (2:ℕ)≠0)]
  rw [show 2*ℓ=ℓ+ℓ by ring,theta_add ℓ ℓ u.ne_zero]
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u)^2 := by ring
    _ = 1 := by rw [hu u]; norm_num

theorem angular_square_primitive_completion (hpub : PrimitiveAngularHeckeInput)
    {q : Eisenstein} (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (hu : AngularUnitCompatible q χ ℓ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ) (root : ℂ) (L Ldual : ℂ → ℂ),
      d ≠ 0 ∧ normNat d ≤ normNat q ∧ PrimitiveResidueCharacter d ψ ∧
      AngularUnitCompatible d ψ (2*ℓ) ∧ ‖root‖=1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar d ψ (2*ℓ)) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar d (star ψ) (-(2*ℓ))) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale d) (|((2*ℓ:ℤ):ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale d) (|((2*ℓ:ℤ):ℝ)|/2) L ∧
      Differentiable ℂ (fun s => idealEulerFactor (idealExponentOf q).support
        (angularResidueIdealChar d ψ (2*ℓ)) s*L s) ∧
      (∀ s : ℂ, 1 < s.re →
        idealEulerFactor (idealExponentOf q).support (angularResidueIdealChar d ψ (2*ℓ)) s*L s =
          normDirichletSeries (fun ν => (angularResidueIdealChar q χ ℓ ν)^2) idealExponentNorm s) := by
  obtain ⟨d,ψ,hd,hi,hN,hp⟩ := primitive_residue_conductor_exists hq (χ^2)
  have hu2 := hi.angular_units hu.square
  have h2ℓ : 2*ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓ
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub (2*ℓ) d hd ψ hp hu2 (Or.inl h2ℓ)
  refine ⟨d,ψ,root,L,Ldual,hd,hN,hp,hu2,hr,hL,hs,hds,hFE,hcomp,
    (idealEulerFactor_differentiable _ _).mul hL,?_⟩
  intro s hss
  rw [hs s hss,←idealDirichlet_euler_exclusion _ _
    (angularResidueIdealChar_norm_le_one hd ψ (2*ℓ))
    (angularResidueIdealChar_add d ψ (2*ℓ)) hss]
  congr 1
  funext ν
  rw [←angularResidueIdealChar_square q χ ℓ ν]
  exact (induced_angularResidueIdealChar hq hi (2*ℓ) ν).symm

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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaElementaryGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds used to discharge reciprocal Gamma growth. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma gamma_norm_le_add_nat {s : ℂ} (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have him : (s+(n:ℂ)).im = s.im := by simp
    have hn : 1 ≤ ‖s+(n:ℂ)‖ := hs.trans (by simpa using Complex.abs_im_le_norm (s+(n:ℂ)))
    have hne : s+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (s+n)‖ := ih
      _ ≤ ‖s+(n:ℂ)‖*‖Complex.Gamma (s+n)‖ :=
        le_mul_of_one_le_left (_root_.norm_nonneg _) hn
      _ = ‖Complex.Gamma (s+(n+1:ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

lemma complex_sin_norm_le_exp_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hp : ‖Complex.exp (-s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self s.im
  have hm : ‖Complex.exp (s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs s.im
  have hd := (norm_sub_le (Complex.exp (-s*Complex.I)) (Complex.exp (s*Complex.I))).trans
    (add_le_add hp hm)
  norm_num
  simp only [neg_mul] at hd
  linarith

lemma gamma_real_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc a b, Real.Gamma x ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma (x:ℂ) ?_).comp Complex.continuous_ofReal.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    linarith [hx.1]
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (Complex.re_le_norm (Complex.Gamma (x:ℂ))).trans ((hM x hx).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaInverseGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal Gamma has the coarse strip growth needed for the completed
Hecke functions. This uses Euler's integral, reflection and recurrence. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma gamma_inverse_reflection {s : ℂ} (hs : 1 ≤ |s.im|) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1-s)*Complex.sin (Real.pi*s)/Real.pi := by
  have hi : s.im ≠ 0 := by intro h; simp only [h,abs_zero] at hs; linarith
  have hreg : ∀ n : ℕ, s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    simpa using congrArg Complex.im hn
  have hreg' : ∀ n : ℕ, 1-s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh
  have hG := Complex.Gamma_ne_zero hreg
  have hG' := Complex.Gamma_ne_zero hreg'
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin (Real.pi*s) ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hr
    exact mul_ne_zero hG hG' hr
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := (eq_div_iff hsin).mp hr
  apply (eq_div_iff hp).mpr
  calc
    _ = (Complex.Gamma s)⁻¹*(Complex.Gamma s*Complex.Gamma (1-s)*
        Complex.sin (Real.pi*s)) := congrArg (fun z : ℂ => (Complex.Gamma s)⁻¹*z) hr'.symm
    _ = _ := by field_simp [hG]

private lemma gamma_inverse_large_height_bound (a b : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, s.re ∈ Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  have hlo : 0 < 1-b+(n:ℝ) := by linarith
  obtain ⟨M,hM,hbound⟩ := gamma_real_interval_bound (b := 1-a+(n:ℝ)) hlo
  refine ⟨M/Real.pi,div_pos hM Real.pi_pos,?_⟩
  intro s hs ht
  have hz : 0 < (1-s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
    linarith [hs.2]
  have hΓ : ‖Complex.Gamma (1-s)‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (1-s+(n:ℂ))‖ := gamma_norm_le_add_nat (by simpa using ht) n
      _ ≤ Real.Gamma (1-s+(n:ℂ)).re := gamma_norm_le_real hz
      _ ≤ M := hbound _ (by
        simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
        constructor <;> linarith [hs.1,hs.2])
  have hsin : ‖Complex.sin (Real.pi*s)‖ ≤ Real.exp (Real.pi*|s.im|) := by
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      abs_mul,abs_of_pos Real.pi_pos] using complex_sin_norm_le_exp_im (Real.pi*s)
  rw [gamma_inverse_reflection ht,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact (div_le_div_of_nonneg_right (mul_le_mul hΓ hsin (_root_.norm_nonneg _) hM.le)
    Real.pi_pos.le).trans_eq (by ring)

/-- The exact reciprocal-Gamma strip input is an elementary theorem. -/
theorem gammaInverseFiniteOrder (a b : ℝ) : GammaInverseFiniteOrder a b := by
  obtain ⟨D,hD,hlarge⟩ := gamma_inverse_large_height_bound a b
  let F : ℝ × ℝ → ℂ := fun p => (Complex.Gamma ((p.1:ℂ)+(p.2:ℂ)*Complex.I))⁻¹
  have hF : Continuous F := by
    simpa only [F,one_div,Function.comp_def] using Complex.differentiable_one_div_Gamma.continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*Complex.I) by fun_prop)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc a b) ×ˢ (Icc (-1:ℝ) 1)) hF.continuousOn
  let E := max (max C 1) D
  have hE1 : 1 ≤ E := (le_max_right C 1).trans (le_max_left _ _)
  have hE : 0 < E := zero_lt_one.trans_le hE1
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
  refine ⟨Real.log E+Real.pi,add_nonneg hlog Real.pi_pos.le,?_⟩
  intro s hs
  have hb : ‖(Complex.Gamma s)⁻¹‖ ≤ E*Real.exp (Real.pi*|s.im|) := by
    by_cases ht : |s.im| ≤ 1
    · have hc := hC (s.re,s.im) ⟨hs,abs_le.mp ht⟩
      have hc' : ‖(Complex.Gamma s)⁻¹‖ ≤ C := by
        simpa only [F,Complex.re_add_im] using hc
      exact (hc'.trans ((le_max_left C 1).trans (le_max_left _ _))).trans
        (le_mul_of_one_le_right hE.le (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))))
    · exact (hlarge s hs (le_of_not_ge ht)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hquad1 : 1 ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  have hquad2 : |s.im| ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ E*Real.exp (Real.pi*|s.im|) := hb
    _ = Real.exp (Real.log E+Real.pi*|s.im|) := by rw [Real.exp_add,Real.exp_log hE]
    _ ≤ Real.exp ((Real.log E+Real.pi)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log E*(1+|s.im|)^2+Real.pi*(1+|s.im|)^2 :=
          add_le_add (by simpa using mul_le_mul_of_nonneg_left hquad1 hlog)
            (mul_le_mul_of_nonneg_left hquad2 Real.pi_pos.le)
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normalization of the complete ideal series on Re(s) ≥ 2.
The lower bound follows from its actual Möbius inverse. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealZetaTwo_ge_one : 1 ≤ idealZetaTwo := by
  have h := (summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)).le_tsum
    0 (fun ν _ => Real.rpow_nonneg (idealExponentNorm_pos ν).le _)
  simpa [idealZetaTwo,idealExponentNorm,idealExponentGenerator] using h

lemma idealZetaTwo_pos : 0 < idealZetaTwo := zero_lt_one.trans_le idealZetaTwo_ge_one

lemma idealMoebius_character_norm (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (ν : EisensteinIdealExponent) :
    ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν‖ ≤ 1 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans
    (idealMoebiusSeries_abs_le_one ν)

theorem idealDirichlet_upper_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤ idealZetaTwo :=
  norm_idealDirichlet_le_zeta_two χ hχ s hs

theorem idealDirichlet_inverse_lower_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    1 ≤ idealZetaTwo*‖normDirichletSeries χ idealExponentNorm s‖ := by
  have he := congrArg (fun z : ℂ => ‖z‖) (idealDirichlet_moebius_mul χ hχ hχ0 hχadd
    (show 1 < s.re by linarith))
  rw [norm_mul,norm_one] at he
  rw [←he]
  exact mul_le_mul_of_nonneg_right
    (idealDirichlet_upper_bound _ (idealMoebius_character_norm χ hχ) hs)
    (_root_.norm_nonneg _)

theorem idealDirichlet_reciprocal_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(normDirichletSeries χ idealExponentNorm s)⁻¹‖ ≤ idealZetaTwo := by
  rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr
    (idealDirichlet_ne_zero χ hχ hχ0 hχadd (show 1 < s.re by linarith)))]
  simpa only [mul_comm] using idealDirichlet_inverse_lower_bound χ hχ hχ0 hχadd hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeUniformGrowth
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A conductor-explicit polynomial bound in the fixed strip needed by
the local zero-free argument. The finite-order constant disappears under
Phragmen--Lindelof; only the actual functional-equation factors remain. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma heckeZeroFreeMajorant_ge_zeta (A k : ℝ) (ε : ℂ) :
    idealZetaTwo ≤ heckeZeroFreeMajorant A k ε := by
  have h := idealZetaTwo_pos
  have hp : 0 ≤ ‖ε‖*A^4*(k+7)^4*idealZetaTwo := by positivity
  unfold heckeZeroFreeMajorant
  nlinarith

lemma heckeZeroFreeMajorant_pos (A k : ℝ) (ε : ℂ) :
    0 < heckeZeroFreeMajorant A k ε :=
  idealZetaTwo_pos.trans_le (heckeZeroFreeMajorant_ge_zeta A k ε)

theorem shifted_hecke_uniform_strip
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) :
    ∀ z : ℂ, -(3/2:ℝ) ≤ z.re →
      ‖L z‖ ≤ heckeZeroFreeMajorant A k ε*(1+|z.im|)^4 := by
  let C : ℝ := idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo
  have hS0 := idealZetaTwo_pos
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : idealZetaTwo ≤ C := le_add_of_nonneg_right (by positivity)
  have ha : ∀ z : ℂ, z.re=-(3/2:ℝ) → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    have he : z=(1/2:ℂ)-(2:ℕ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> norm_num
      linarith
    have hb := angular_hecke_left_boundary χdual hχdual hA hk hL hcomp hFE hds
      (m := 2) (by norm_num) z.im
    rw [←he] at hb
    have hb' : ‖L z‖ ≤ (‖ε‖*A^4*(k+7)^4*idealZetaTwo)*(1+|z.im|)^4 := by
      simpa only [idealZetaTwo,Nat.reduceMul,Nat.cast_ofNat,
        show k+3*(2:ℝ)+1=k+7 by ring] using! hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [idealZetaTwo_pos])
      (by positivity))
  have hb : ∀ z : ℂ, z.re=2 → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ hz.ge).trans
      (hS.trans (le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg z.im]))))
  have hfin : FiniteVerticalOrder L (-(3/2:ℝ)) 2 :=
    shifted_completed_finiteVerticalOrder hA hL hcomp
      (gammaInverseFiniteOrder (-(3/2:ℝ)+k) (2+k))
  have hbound := polynomial_strip_of_finite_order (a := -(3/2:ℝ)) (b := 2)
    (by norm_num) hL hfin hC 4 ha hb
  intro z hz
  by_cases hz2 : z.re ≤ 2
  · simpa only [heckeZeroFreeMajorant,C,show 2-(-(3/2:ℝ))+1=9/2 by norm_num,
      show (2:ℝ)^4=16 by norm_num]
      using hbound z ⟨hz,hz2⟩
  · rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ (by linarith)).trans
      ((heckeZeroFreeMajorant_ge_zeta A k ε).trans
        (le_mul_of_one_le_right (heckeZeroFreeMajorant_pos A k ε).le
          (one_le_pow₀ (by linarith [abs_nonneg z.im]))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_EulerHeckeDisk
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler deletion retains a polynomial bound on the normalized
Hecke disk. No functional equation for the imprimitive function is asserted. -/
noncomputable section
namespace CubicFirstMoment

lemma primeIdealRestriction_zero (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : χ 0=1) : primeIdealRestriction S χ 0=1 := by
  simp [primeIdealRestriction,hχ]

lemma euler_hecke_majorant {N A k : ℝ} {ε : ℂ}
    (hN : 1 ≤ N) (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) :
    N^3*heckeZeroFreeMajorant A k ε ≤ heckeZeroFreeMajorant (2*N*(1+A)) k 1 := by
  have hN0 : 0 ≤ N := by linarith
  have hH : 1 ≤ (k+7)^4 := one_le_pow₀ (by linarith)
  have hP : 1 ≤ (1+A)^4 := one_le_pow₀ (by linarith)
  have hNP : N^3 ≤ N^4 := pow_le_pow_right₀ hN (by norm_num : (3:ℕ)≤4)
  have hAP : A^4 ≤ (1+A)^4 := pow_le_pow_left₀ hA.le (by linarith) 4
  let Z := N^4*(1+A)^4*(k+7)^4
  have h1 : N^3 ≤ Z := by
    calc
      _ ≤ N^4 := hNP
      _ ≤ N^4*(1+A)^4 := le_mul_of_one_le_right (by positivity) hP
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hH
  have h2 : N^3*‖ε‖*A^4*(k+7)^4 ≤ Z := by
    calc
      _ ≤ N^4*1*(1+A)^4*(k+7)^4 := by gcongr
      _ = _ := by dsimp [Z]; ring
  have h3 : N^3*(1+‖ε‖*A^4*(k+7)^4) ≤ 1+(2*N*(1+A))^4*(k+7)^4 := by
    have hZ : 0 ≤ Z := by dsimp [Z]; positivity
    have he : (2*N*(1+A))^4*(k+7)^4=16*Z := by dsimp [Z]; ring
    rw [he]
    nlinarith only [h1,h2,hZ]
  unfold heckeZeroFreeMajorant
  rw [norm_one]
  have hh := mul_le_mul_of_nonneg_right h3 idealZetaTwo_pos.le
  nlinarith only [hh]

lemma euler_corrected_right_series (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {s : ℂ} (hss : 1 < s.re) :
    idealEulerFactor S χ s*L s=normDirichletSeries (primeIdealRestriction S χ) idealExponentNorm s := by
  rw [hs s hss,idealDirichlet_euler_exclusion S χ hχ hadd hss]

theorem euler_corrected_normalized_disk
    (S : Finset EisensteinIdealPrime) (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (hdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} (hε : ‖ε‖ ≤ 1)
    {L Ldual : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) (t : ℝ) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖normalizedHeckeDisk (fun s => idealEulerFactor S χ s*L s) t z‖ ≤
        normalizedHeckeDiskBound (2*idealExponentNorm (primeSetExponent S)*(1+A)) k 1 t := by
  intro z hz
  let N := idealExponentNorm (primeSetExponent S)
  have hN : 1 ≤ N := idealExponentNorm_ge_one _
  have hright (s : ℂ) (hss : 1 < s.re) := euler_corrected_right_series S χ hχ hadd hs hss
  have hc : (2+(t:ℂ)*Complex.I).re=2 := by simp
  have hinv : ‖(idealEulerFactor S χ (2+(t:ℂ)*Complex.I)*L (2+(t:ℂ)*Complex.I))⁻¹‖ ≤ idealZetaTwo := by
    rw [hright _ (by rw [hc]; norm_num)]
    exact idealDirichlet_reciprocal_bound _ (primeIdealRestriction_norm_le S χ hχ)
      (primeIdealRestriction_zero S χ hχ0) (primeIdealRestriction_add S χ hadd) hc.ge
  have hr : -(3/2:ℝ) ≤ (2+(t:ℂ)*Complex.I+3*z).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm z)).1
    have he : (2+(t:ℂ)*Complex.I+3*z).re=2+3*z.re := by simp
    rw [he]
    linarith
  have hi : |(2+(t:ℂ)*Complex.I+3*z).im| ≤ |t|+3 := by
    have hh := abs_add_le t (3*z.im)
    have him := Complex.abs_im_le_norm z
    have he : (2+(t:ℂ)*Complex.I+3*z).im=t+3*z.im := by simp
    rw [he]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hh
    linarith
  have hl := shifted_hecke_uniform_strip hχ hdual hA hk hL hs hds hFE hcomp _ hr
  have hp : (1+|(2+(t:ℂ)*Complex.I+3*z).im|)^4 ≤ (4+|t|)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hcorr := idealEulerFactor_norm_bound S χ hχ hr
  have hm := euler_hecke_majorant hN hA hk hε
  have hnum : ‖idealEulerFactor S χ (2+(t:ℂ)*Complex.I+3*z)*L (2+(t:ℂ)*Complex.I+3*z)‖ ≤
      heckeZeroFreeMajorant (2*N*(1+A)) k 1*(4+|t|)^4 := by
    rw [norm_mul]
    calc
      _ ≤ N^3*(heckeZeroFreeMajorant A k ε*(4+|t|)^4) :=
        mul_le_mul hcorr (hl.trans (mul_le_mul_of_nonneg_left hp (heckeZeroFreeMajorant_pos A k ε).le))
          (_root_.norm_nonneg _) (by positivity)
      _ = (N^3*heckeZeroFreeMajorant A k ε)*(4+|t|)^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)
  rw [normalizedHeckeDisk,div_eq_mul_inv,norm_mul]
  exact (mul_le_mul hnum hinv (_root_.norm_nonneg _)
    (mul_nonneg (heckeZeroFreeMajorant_pos _ _ _).le (by positivity))).trans (by
    unfold normalizedHeckeDiskBound
    nlinarith)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeSquareDisk
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp prime bounds from the actual square series and its proved disk
bound. This accommodates finite Euler corrections in angular characters. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem hecke_smooth_prime_bound_square_disk :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (W : ℝ → ℂ) (_hW : HasCompactSupport W),
    tsupport W ⊆ Ioi 0 → ContDiff ℝ ∞ W →
    ∀ D : ℝ, PrimeMellinControl W D →
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 u T : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    10 ≤ u → A ≤ u → A2 ≤ u → k+7 ≤ u → k2+7 ≤ u → 4+2*(T+3) ≤ u →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X b : ℝ, 1 ≤ X → 1 < b → b < 1+δ → b ≤ 2 → 0 < T →
      ‖idealMangoldtSmooth χ W X‖ ≤ 6*D*
        (X^(1-heckeZeroFreeWidth u/2)*(heckeLogSquaredConstant*(1+Real.log u)^2)+
          X^b*(heckeLogSquaredConstant*(1+Real.log u)^2+(1/(b-1)+C))/T^2) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := idealMangoldt_smooth_bound_controlled
  refine ⟨C,δ,hC,hδ,?_⟩
  intro W hW hpos hsm D hD χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 u T ε ε2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT
    hFE hcomp hdisk2 X b hX hb hbδ hb2 hT
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
    apply hecke_zero_free_log_from_square_disk hχ hχ0 hχadd hχdual hL hL2
      hs hs2 hds hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hcomp hdisk2
    have hwidth := heckeZeroFreeWidth_le_log hu
    linarith [hparts.1.1]
  · intro s hmem
    have hparts : s.re ∈ Icc (1-heckeZeroFreeWidth u/2) b ∧ s.im ∈ Icc (-T) T := hmem
    rw [←Complex.re_add_im s]
    exact hecke_logDeriv_norm_uniform_from_square_disk hχ hχ0 hχadd hχdual hL hL2
      hs hs2 hds hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 huT hFE hcomp hdisk2
      hparts.1.1 (hparts.1.2.trans hb2) (abs_le.mpr hparts.2)

theorem hecke_dyadic_prime_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/2 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtDyadic χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := hecke_smooth_prime_bound_square_disk
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
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
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
    (K*J^d) (hcontrol J hJ) hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds
    hA hA2 hk hk2 hε hε2 hu.1 (hQA.trans hu.2.1) (hQA2.trans hu.2.1)
    (hQk.trans hu.2.1) (hQk2.trans hu.2.1) hu.2.2 hFE hcomp hdisk2
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

theorem hecke_full_prime_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealMangoldtSum χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_dyadic_prime_bound_of_square_disk
  let X0 := max (Real.exp 2) (Y0^2)
  have hX0 : 1 < X0 := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num)) (le_max_left _ _)
  refine ⟨B+24,c/2,X0,by linarith,by positivity,by linarith,hX0,?_⟩
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_left _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hwindow (t : ℝ) (ht : Y0 ≤ t) :
      ‖idealMangoldtDyadic χ t‖ ≤ B*primeCancellationWeight c Q t :=
    hbound hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds hA hA2 hk hk2 hε hε2
      hQ hQA hQA2 hQk hQk2 hFE hcomp hdisk2 t ht
  exact idealMangoldt_full_from_dyadic χ hχ hB.le hc.le hc1 hQ hY0.le hwindow hXp hLX
    ((le_max_right _ _).trans hX)

theorem hecke_prime_ideal_bound_of_square_disk :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) →
    ∀ {L Ldual L2 : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    ShiftedCompletedHeckeFiniteOrder A k L →
    (∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t) →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealPrimeChebyshev χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_full_prime_bound_of_square_disk
  let X0 := max Y0 (Real.exp 2)
  have hX0 : 1 < X0 := hY0.trans_le (le_max_left _ _)
  refine ⟨B+idealPrimePowerErrorConstant,c,X0,add_pos hB idealPrimePowerErrorConstant_pos,
    hc,hc1,hX0,?_⟩
  intro χ χdual hχ hχ0 hχadd hχdual L Ldual L2 hL hL2
    hs hs2 hds A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hcomp hdisk2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hmain := hbound hχ hχ0 hχadd hχdual hL hL2 hs hs2 hds hA hA2 hk hk2 hε hε2
    hQ hQA hQA2 hQk hQk2 hFE hcomp hdisk2 X ((le_max_left _ _).trans hX)
  exact idealPrimeChebyshev_bound_of_mangoldt χ hχ hc.le hc1 hQ hXp hLX hmain

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveAngularPrimeEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp angular prime-ideal estimate is derived from the actual
primitive completions. The square uses its own conductor and finite Euler correction. -/
noncomputable section
namespace CubicFirstMoment

lemma primeSetExponent_support_norm_le {q : Eisenstein} (hq : q ≠ 0) :
    idealExponentNorm (primeSetExponent (idealExponentOf q).support) ≤ norm q := by
  rw [←idealExponentOf_norm hq]
  apply idealExponentNorm_mono
  apply (primeSetExponent_le_iff _ _).mpr
  intro p hp
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)

lemma angularResidueIdealChar_at_zero (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) : angularResidueIdealChar q χ ℓ 0=1 := by
  simp [angularResidueIdealChar,residueIdealChar,idealExponentGenerator]

theorem primitive_angular_prime_ideal_estimate_oai (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → ∀ ℓ : ℤ, ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → 2*norm q*(1+norm q) ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X‖ ≤
      B*primeCancellationWeight c Q X := by
  obtain ⟨B,c,X0,hB,hc,hc1,hX0,hbound⟩ := hecke_prime_ideal_bound_of_square_disk
  refine ⟨B,c,X0,hB,hc,hc1,hX0,?_⟩
  intro q hq χ hp ℓ hℓ hu Q hQ hQN hQk X hX
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub ℓ q hq χ hp hu (Or.inl hℓ)
  obtain ⟨d,ψ,root2,L2,L2dual,hd,hN,hp2,_hu2,hr2,hL2,hs2,hds2,hFE2,hcomp2,hcorr,hsq⟩ :=
    angular_square_primitive_completion hpub hq χ hℓ hu
  let S := (idealExponentOf q).support
  let A2 := 2*idealExponentNorm (primeSetExponent S)*(1+residueHeckeScale d)
  have hn : 1 ≤ norm q := one_le_norm hq
  have hnd : norm d ≤ norm q := by
    simpa only [normNat_cast] using (Nat.cast_le.mpr hN : (normNat d:ℝ) ≤ (normNat q:ℝ))
  have hscale : residueHeckeScale q ≤ Q :=
    (residueHeckeScale_le_norm hq).trans (by nlinarith)
  have hscale2 : A2 ≤ Q := by
    have hsN : idealExponentNorm (primeSetExponent S) ≤ norm q := primeSetExponent_support_norm_le hq
    have hsd := (residueHeckeScale_le_norm hd).trans hnd
    have hh : A2 ≤ 2*norm q*(1+norm q) := by
      dsimp [A2]
      gcongr; linarith [residueHeckeScale_pos hd]
    exact hh.trans hQN
  have hk2 : |((2*ℓ:ℤ):ℝ)|/2 = |(ℓ:ℝ)| := by
    push_cast
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  apply hbound (k2 := |((2*ℓ:ℤ):ℝ)|/2) (angularResidueIdealChar_norm_le_one hq χ ℓ)
    (angularResidueIdealChar_at_zero q χ ℓ) (angularResidueIdealChar_add q χ ℓ)
    (angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)) hL hcorr hs hsq hds
    (residueHeckeScale_pos hq) (show 0<A2 by
      dsimp [A2]
      exact mul_pos (mul_pos (by norm_num) (idealExponentNorm_pos _))
        (by linarith [residueHeckeScale_pos hd]))
    (by positivity) (by positivity) hr.le (show ‖(1:ℂ)‖≤1 by simp) hQ hscale hscale2
    (by have hh := abs_nonneg (ℓ:ℝ); linarith) (by rw [hk2]; exact hQk) hFE hcomp _ X hX
  intro t z hz
  exact euler_corrected_normalized_disk S (angularResidueIdealChar d ψ (2*ℓ))
    (angularResidueIdealChar d (star ψ) (-(2*ℓ)))
    (angularResidueIdealChar_norm_le_one hd ψ (2*ℓ))
    (angularResidueIdealChar_at_zero d ψ (2*ℓ)) (angularResidueIdealChar_add d ψ (2*ℓ))
    (angularResidueIdealChar_norm_le_one hd (star ψ) (-(2*ℓ)))
    (residueHeckeScale_pos hd) (by positivity) hr2.le hL2 hs2 hds2 hFE2 hcomp2 t z (hz.trans (by norm_num))

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate_oai := @OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate_oai
