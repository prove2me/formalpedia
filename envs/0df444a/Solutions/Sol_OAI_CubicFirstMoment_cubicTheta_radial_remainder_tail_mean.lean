-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:13:29.663176+00:00
-- url     : https://prove2.me/submissions/fe267aa6-e622-4784-8e6e-a211106d9060

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaResidue_radial_voronoi

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

end CubicFirstMoment

end
end

end OAI
end

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

lemma hecke_scale_phase {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I) =
      (Real.sqrt Z:ℂ)*mellinPhase τ Z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne'),
    ← Complex.ofReal_log hZ.le,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hZ,Complex.ofReal_exp]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

lemma mellin_rectangle_identity {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (T : ℝ) :
    (∫ x in a..b, f (x - (T : ℂ) * Complex.I)) -
      (∫ x in a..b, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y in -T..T, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in -T..T, f (a + (y : ℂ) * Complex.I)) = 0 := by
  have hd := hf.mono (show
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) ⊆ closedVerticalStrip a b from by
    intro z hz
    simpa only [Set.uIcc_of_le hab, Set.mem_preimage, Set.mem_Icc,
      closedVerticalStrip, Set.mem_ofPred_eq] using hz.1)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero,
    sub_zero, add_zero, zero_sub, mul_one, zero_add] at h
  simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, mul_one, zero_add, Complex.ofReal_neg,
    neg_mul, add_neg_cancel, sub_self, smul_eq_mul, sub_eq_add_neg] using h hd

/-- Vertical Mellin integrals agree after shifting through a holomorphic
strip, once both horizontal edges vanish. -/
theorem mellin_contour_shift {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (ha : Integrable (fun y : ℝ => f (a + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f (b + (y : ℂ) * Complex.I)))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + (T : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b, f (x - (T : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hia := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot tendsto_id
  have hib := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hBot.sub hTop).add (hib.const_mul Complex.I)).sub
    (hia.const_mul Complex.I)
  have hz : (0 : ℂ) + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
    have hz' : 0 - 0 + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall (fun T => (mellin_rectangle_identity hab f hf T).symm)
    simpa only [sub_self] using hz'
  have he : Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) := by
    linear_combination -hz
  exact mul_left_cancel₀ Complex.I_ne_zero he

/-- A common decaying majorant supplies both horizontal limits. This is
the form used for a rapidly decreasing Mellin transform times an
L-function of polynomial growth. -/
theorem mellin_contour_shift_of_majorant {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (H : ℝ → ℝ) (hH : Integrable H)
    (hHtop : Tendsto H atTop (𝓝 0)) (hHbot : Tendsto H atBot (𝓝 0))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (x + (t : ℂ) * Complex.I)‖ ≤ H t) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hline (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) := by
    have hc : Continuous (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) :=
      hf.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (by intro y; simpa [closedVerticalStrip] using hx)
    exact hH.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (hbound x hx))
  have hedge (t : ℝ) :
      ‖∫ x in a..b, f (x + (t : ℂ) * Complex.I)‖ ≤ H t * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hbound x
    rw [Set.uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  apply mellin_contour_shift hab f hf
    (hline a ⟨le_rfl,hab⟩) (hline b ⟨hab,le_rfl⟩)
  · exact squeeze_zero_norm hedge (by simpa using hHtop.mul_const |b-a|)
  · have he : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun T => hedge (-T))
        (by simpa using (hHbot.comp tendsto_neg_atTop_atBot).mul_const |b-a|)
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rapid Mellin decay on a fixed closed real strip. The bound
comes from the actual compact logarithmic support, not an additional
analytic input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

private lemma exp_linear_deriv_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| * |u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

private lemma mellinLogSchwartz_eq_smul (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ) =
      fun u => Real.exp (-σ*u) • mellinLogSchwartz W hW hpos hsm 0 u := by
  ext u
  simp [mellinLogSchwartz_apply]

theorem mellinLogSchwartz_seminorm_uniform (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤ C := by
  let G := mellinLogSchwartz W hW hpos hsm 0
  obtain ⟨R₀,hR₀⟩ := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := max R₀ 1
  let M' := max M 0
  let B := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (M'^i * Real.exp (M'*R)) * SchwartzMap.seminorm ℝ 0 (n-i) G
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hM : 0 ≤ M' := le_max_right _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by positivity)
  refine ⟨R^k*B, by positivity, ?_⟩
  intro σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hg (i : ℕ) : ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ B := by
      rw [mellinLogSchwartz_eq_smul W hW hpos hsm σ]
      apply hd.trans
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (exp_linear_deriv_bound hM (hσ.trans (le_max_left _ _)) hu i) (by positivity)
      · exact hg (n-i)
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |u|) hu k) hb
        (by positivity) (by positivity)
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      have hb : |u| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ u hs'
      exact hu (hb.trans (le_max_left _ _))
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_family_bounded (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun σ => mellinVerticalSchwartz W hW hpos hsm σ) '' {σ | |σ| ≤ M}) := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun σ => mellinLogSchwartz W hW hpos hsm σ
  have hb : Bornology.IsVonNBounded ℝ (f '' {σ | |σ| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,h⟩ := mellinLogSchwartz_seminorm_uniform W hW hpos hsm M i.1 i.2
    exact ⟨C+1,by linarith,fun σ hσ => (h σ hσ).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

theorem smooth_mellin_strip_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  have hb := mellinVertical_family_bounded W hW hpos hsm M
  obtain ⟨C,hC,h⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun σ => mellinVerticalSchwartz W hW hpos hsm σ) |>.mp hb (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (h σ hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

lemma mellinEdgeMajorant_tendsto (C : ℝ) :
    Tendsto (mellinEdgeMajorant C) atTop (𝓝 0) ∧
      Tendsto (mellinEdgeMajorant C) atBot (𝓝 0) := by
  have h (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
      Tendsto (mellinEdgeMajorant C) l (𝓝 0) := by
    change Tendsto (fun t : ℝ => C/(1+|t|)^2) l (𝓝 0)
    have hp : Tendsto (fun t : ℝ => (1+|t|)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t => by linarith) hl)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using (hp.pow 2).const_mul C
  exact ⟨h atTop tendsto_abs_atTop_atTop,h atBot tendsto_abs_atBot_atTop⟩

lemma norm_mellinHecke_integrand_le (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ + ((τ-t : ℝ) : ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
          L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K τ := by
  obtain ⟨Cw,hCw,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm (|a|+|b|) (N+2)
  let B := Z^b*C*(1+|t|)^N
  have hB : 0 ≤ B := by positivity
  refine ⟨B*Cw,by positivity,?_⟩
  intro σ hσ τ
  have hσabs : |σ| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hσ.1]
    · linarith [le_abs_self b,abs_nonneg a,hσ.2]
  have hscale : ‖(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)‖ ≤ Z^b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Z)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hZ hσ.2
  have hshift : (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hd := abs_sub_le τ 0 t
    simp only [sub_zero,zero_sub,abs_neg] at hd
    nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  have hL' : ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤
      C*((1+|t|)^N*(1+|τ|)^N) :=
    (hL σ hσ τ).trans (mul_le_mul_of_nonneg_left hshift hC)
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖ * Z^b *
        (C*((1+|t|)^N*(1+|τ|)^N)))*(1+|τ|)^2 := by
      rw [norm_mul,norm_mul]
      gcongr
    _ = B*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      dsimp [B]
      ring
    _ ≤ B*Cw := mul_le_mul_of_nonneg_left (hdecay σ hσabs τ) hB

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedIdealParts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the finitely many primes above three in the
complete ideal lattice. No ramified Euler term is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual common nonconstant coefficient is nonzero. Otherwise
global automorphy would force a pure height power to be invariant. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_ne_zero : cubicThetaArithmeticBaseScalar≠0 := by
  intro hB
  let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
  let g₀ : SL(2,Eisenstein) := ⟨!![1,0;3,1],by simp [Matrix.det_fin_two]⟩
  have hg : g₀∈cubicThetaPrincipalGroup :=
    (cubicThetaPrincipalGroup_mem_iff g₀).mpr
      ⟨primary_one,dvd_zero _,dvd_refl _,primary_one⟩
  let g : cubicThetaPrincipalGroup := ⟨g₀,hg⟩
  have hp : (g • p).val.2=(1/10:ℝ) := by
    change (cubicThetaMobius (cubicThetaPrincipalComplex g) (0,1)).2=(1/10:ℝ)
    norm_num [cubicThetaMobius,cubicThetaMobiusDenominator,
      cubicThetaPrincipalComplex_apply,g,g₀]
    change (1+Complex.normSq (3:ℂ))⁻¹=(1/10:ℝ)
    norm_num [Complex.normSq_apply]
  have hC : 0 < cubicThetaConstant := by unfold cubicThetaConstant; positivity
  have hnorm (q : CubicThetaPoint) :
      ‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar q.val‖=
        cubicThetaConstant*q.val.2^(2/3:ℝ) := by
    rw [cubicThetaArithmeticModel,hB,zero_mul,add_zero,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (mul_pos hC (Real.rpow_pos_of_pos q.property _))]
  have he := congrArg (fun z : ℂ => ‖z‖) (cubicThetaArithmeticModel_automorphy g p)
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul,hnorm,hnorm,hp] at he
  change cubicThetaConstant*(1/10:ℝ)^(2/3:ℝ)=cubicThetaConstant*1^(2/3:ℝ) at he
  have hlt : (1/10:ℝ)^(2/3:ℝ)<1 := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ)≤1/10)
      (by norm_num : (1/10:ℝ)<1) (by norm_num : (0:ℝ)<2/3)
  rw [Real.one_rpow] at he
  have he' := (mul_left_cancel₀ hC.ne' he)
  exact (ne_of_lt hlt) he'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariance of the cubic multiplier under the two integral modular
generators, as needed to extend it to the group of DR v3 Section 5.1. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaKubotaConjugate_S_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaKubotaConjugate cubicThetaModularS g).val 0 0 = g.val 1 1 ∧
      (cubicThetaKubotaConjugate cubicThetaModularS g).val 1 0 = -g.val 0 1 := by
  change ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 0 0 = g.val 1 1 ∧
    ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 1 0 = -g.val 0 1
  constructor <;> simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem cubicThetaKubotaValue_conjugate_S (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaKubotaConjugate cubicThetaModularS g) =
      cubicThetaKubotaValue g := by
  obtain ⟨ha,hc⟩ := cubicThetaKubotaConjugate_S_entries g
  rw [cubicThetaKubotaValue_eq_symbol,ha,hc,
    cubicSymbol_neg (cubicThetaPrincipalGroup_diagonal_primary g).2,
    ←cubicThetaKubota_column_switch,cubicThetaKubotaValue_eq_symbol]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspTypes
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three translated inversion types needed for primary bottom rows.
The actual constant is retained at the trivial type. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullTranslation_add (a b : Eisenstein) :
    cubicThetaFullTranslation (a+b)=cubicThetaFullTranslation a*cubicThetaFullTranslation b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,a;0,1]*!![1,b;0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma cubicThetaShiftedInversion_factor (b : Eisenstein) :
    cubicThetaShiftedInversion b=cubicThetaFullTranslation b*cubicThetaFullInversion := by
  apply Subtype.ext
  change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three cusp multipliers agree when the lower-right entry is
zero modulo three. This is the elementary supplementary-law step needed
before finite Ramanujan summation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimaryBottom_multiplier_symbol (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (1+g 0 1*(g 1 0-1)) (g 1 1*(g 1 0-1)) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol ((cubicThetaPrimaryBottomDefect g).val 0 0)
    ((cubicThetaPrimaryBottomDefect g).val 1 0)=_
  rw [cubicThetaPrimaryBottomDefect_matrix]
  rfl

lemma cubicThetaProjectedCuspMatrix_entries (g : SL(2,Eisenstein)) (j : Fin 3) :
    cubicThetaProjectedCuspMatrix g j 0 1=g 0 1+(j.val:Eisenstein)*omegaE*g 1 1 ∧
    cubicThetaProjectedCuspMatrix g j 1 0=g 1 0 ∧
    cubicThetaProjectedCuspMatrix g j 1 1=g 1 1 := by
  change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 1=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 0=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 1=_
  simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem cubicThetaProjectedCuspMultiplier_constant (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (hd : (3:Eisenstein)∣g 1 1) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier g hc j=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc) := by
  have hj := cubicThetaProjectedCuspMatrix_entries g j
  have hpj := (cubicThetaPrincipalGroup_diagonal_primary
    (cubicThetaPrimaryBottomPrincipal (cubicThetaProjectedCuspMatrix g j)
      (cubicThetaProjectedCuspMatrix_primary g hc j))).1
  have hp := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimaryBottomPrincipal g hc)).1
  change primary ((cubicThetaPrimaryBottomDefect (cubicThetaProjectedCuspMatrix g j)).val 0 0) at hpj
  change primary ((cubicThetaPrimaryBottomDefect g).val 0 0) at hp
  rw [cubicThetaPrimaryBottomDefect_matrix] at hpj hp
  change primary (1+cubicThetaProjectedCuspMatrix g j 0 1*
    (cubicThetaProjectedCuspMatrix g j 1 0-1)) at hpj
  change primary (1+g 0 1*(g 1 0-1)) at hp
  rw [hj.1,hj.2.1] at hpj
  unfold cubicThetaProjectedCuspMultiplier
  rw [cubicThetaPrimaryBottom_multiplier_symbol,cubicThetaPrimaryBottom_multiplier_symbol,
    hj.1,hj.2.1,hj.2.2]
  apply cubicSymbol_periodic_of_nine_and_numerator hpj hp
  · obtain ⟨d,hd⟩ := hd
    obtain ⟨c,hc⟩ := hc
    refine ⟨(j.val:Eisenstein)*omegaE*d*c,?_⟩
    rw [hd,hc]
    ring
  · refine ⟨(j.val:Eisenstein)*omegaE,?_⟩
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAdaptedMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principal-level decomposition evaluates the common multiplier for
cusp lifts with both diagonal entries zero modulo three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaFullTranslation_neg (a : Eisenstein) :
    cubicThetaFullTranslation (-a)=(cubicThetaFullTranslation a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [←cubicThetaFullTranslation_add,neg_add_cancel]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma cubicThetaRightInversion_value (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaRightInversionPrincipal g hc ha hd)=
      cubicSymbol (g 1 0) (g 0 0) := by
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubota_column_switch]
  change cubicSymbol ((g*cubicThetaFullInversion⁻¹).val 1 1)
    ((g*cubicThetaFullInversion⁻¹).val 0 1)=_
  rw [cubicThetaRightInversion_matrix]
  rfl

theorem cubicThetaPrimaryBottom_multiplier_adapted (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (g 1 0) (g 0 0) := by
  obtain ⟨a,ha'⟩ := ha
  obtain ⟨d,hd'⟩ := hd
  let h := cubicThetaRightInversionPrincipal g hc ⟨a,ha'⟩ ⟨d,hd'⟩
  let k := cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d))
  let l := cubicThetaPrincipalTranslation (-a)
  have he : cubicThetaPrimaryBottomPrincipal g hc=h*k*l := by
    apply Subtype.ext
    change g*(cubicThetaPrimaryBottomSeed g)⁻¹=
      (g*cubicThetaFullInversion⁻¹)*
        (cubicThetaModularS*(cubicThetaPrincipalTranslation (-d)).val*cubicThetaModularS⁻¹)*
          (cubicThetaPrincipalTranslation (-a)).val
    have hS : cubicThetaModularS=cubicThetaFullInversion := rfl
    have htd : (cubicThetaPrincipalTranslation (-d)).val=
        (cubicThetaFullTranslation (3*d))⁻¹ := by
      change cubicThetaFullTranslation (3*(-d))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    have hta : (cubicThetaPrincipalTranslation (-a)).val=
        (cubicThetaFullTranslation (3*a))⁻¹ := by
      change cubicThetaFullTranslation (3*(-a))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    rw [cubicThetaPrimaryBottomSeed,cubicThetaShiftedInversion_factor,ha',hd',hS,htd,hta]
    group
  rw [he,cubicThetaKubotaValue_mul,cubicThetaKubotaValue_mul]
  have hk : cubicThetaKubotaValue k=1 := by
    rw [show k=cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d)) from rfl,
      cubicThetaKubotaValue_conjugate_S,cubicThetaPrincipalTranslation_value]
  rw [hk,show cubicThetaKubotaValue l=1 from cubicThetaPrincipalTranslation_value _,mul_one,mul_one]
  exact cubicThetaRightInversion_value g hc _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCubeScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube multiplication in the literal Patterson coefficient formula,
including its unit and ramified cases. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.amplitude_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).amplitude=R.amplitude/norm e := by
  change 3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm (R.cubePart*e))=
    (3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm R.cubePart))/norm e
  rw [norm_mul_eq,div_div]
  congr 1
  ring

lemma CubicThetaCoordinates.coefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    (R.mulPrimaryCube e he).coefficient=(norm e:ℂ)⁻¹*R.coefficient := by
  unfold coefficient
  rw [R.amplitude_mulPrimaryCube]
  dsimp only [mulPrimaryCube]
  push_cast
  split_ifs <;> ring

theorem cubicThetaArithmeticCoefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    cubicThetaArithmeticCoefficient (n*e^3)=(norm e:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  rw [cubicThetaArithmeticCoefficient_formula (R.mulPrimaryCube e he),
    cubicThetaArithmeticCoefficient_formula R,R.coefficient_mulPrimaryCube]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual cusp coefficient families depend only on the integer
cusp index modulo three. This is inherited from their literal support. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspIndex_congr {x y : Eisenstein} (h : (3:Eisenstein)∣x-y) :
    (3:ℤ)∣cubicThetaCuspIndex x-cubicThetaCuspIndex y := by
  obtain ⟨t,ht⟩ := h
  refine ⟨cubicThetaCuspIndex t,?_⟩
  have he : x-y=(3:ℤ) • t := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using ht
  have hh := congrArg (fun z : Eisenstein => coordinatesEquiv.symm z 1) he
  simpa only [cubicThetaCuspIndex,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul] using hh

lemma cubicThetaCuspIndex_omega (j : ℤ) :
    cubicThetaCuspIndex ((j:Eisenstein)*omegaE)=j := by
  have he : coordinatesEquiv ![(0:ℤ),j]=(j:Eisenstein)*omegaE := by
    change ofCoords 0 j=_
    simp [ofCoords]
  unfold cubicThetaCuspIndex
  rw [←he,LinearEquiv.symm_apply_apply]
  rfl

lemma cubicThetaActualCuspCoefficient_periodic {m n : ℤ} (h : (3:ℤ)∣n-m) :
    cubicThetaActualCuspCoefficient n=cubicThetaActualCuspCoefficient m := by
  have he : (3:ℤ)∣n ↔ (3:ℤ)∣m := by
    constructor
    · intro hn
      have hm := dvd_sub hn h
      simpa only [sub_sub_cancel] using hm
    · intro hm
      have hn := dvd_add h hm
      simpa only [sub_add_cancel] using hn
  by_cases hn : (3:ℤ)∣n
  · simp only [cubicThetaActualCuspCoefficient,hn,he.mp hn,ite_true, if_true]
  · have hm := mt he.mpr hn
    simp only [cubicThetaActualCuspCoefficient,hn,hm,ite_false, if_false]
    funext k
    unfold cubicThetaShiftedLatticeCoefficient
    have hnm : lambdaE∣(n:Eisenstein)-(m:Eisenstein) := by
      obtain ⟨t,ht⟩ := h
      have hl : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
        rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
      apply dvd_trans hl
      exact ⟨(t:Eisenstein),by exact_mod_cast ht⟩
    have hiff : lambdaE∣k-(n:Eisenstein) ↔ lambdaE∣k-(m:Eisenstein) := by
      constructor
      · intro hk
        convert dvd_add hk hnm using 1
        all_goals try with_reducible_and_instances rfl
        ring
      · intro hk
        convert dvd_sub hk hnm using 1
        all_goals try with_reducible_and_instances rfl
        ring
    rw [hiff]

lemma cubicThetaProjectedCuspType_congr (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (j : Fin 3) :
    (3:ℤ)∣cubicThetaProjectedCuspType g j-(j.val:ℤ) := by
  have hj : cubicThetaProjectedCuspMatrix g j 0 0=
      g 0 0+(j.val:Eisenstein)*omegaE*g 1 0 := by
    change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 0=_
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  have h : (3:Eisenstein)∣cubicThetaProjectedCuspMatrix g j 0 0-(j.val:Eisenstein)*omegaE := by
    rw [hj]
    convert dvd_add ha (dvd_mul_of_dvd_right hc ((j.val:Eisenstein)*omegaE)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hh := cubicThetaCuspIndex_congr h
  have hjindex : cubicThetaCuspIndex ((j.val:Eisenstein)*omegaE)=(j.val:ℤ) := by
    simpa only [Int.cast_natCast] using cubicThetaCuspIndex_omega (j.val:ℤ)
  rw [hjindex] at hh
  exact hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the genuine primary-level theta transformation on a symmetric
height scale, before Mellin integration. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_pos {q : Eisenstein} (hq : primary q) :
    0 < cubicThetaLevelScale q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hq)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelAngularReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put every genuine signed angular transformation on the symmetric height scale. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_square (q : Eisenstein) :
    cubicThetaLevelScale q^2=(norm q)⁻¹ := by
  unfold cubicThetaLevelScale
  rw [inv_pow,Real.sq_sqrt (norm_nonneg q)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticFrequency_ne_zero (n : MetaplecticDualArgument) :
    metaplecticFrequency n ≠ 0 :=
  div_ne_zero (fun h => n.property (Subtype.ext h)) traceLambda_ne_zero

lemma metaplecticCompleted_eq_raw {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticCompleted r ℓ W X = gauss r*theta ℓ r*metaplecticRawCompleted r ℓ W X := by
  rw [metaplecticCompleted,metaplecticRawCompleted,← tsum_mul_left]
  apply tsum_congr
  intro du
  split_ifs
  · rw [gauss_mul hr du.2.property,theta_mul,cubic_reciprocity du.2.property hr]
    ring
  · ring

lemma gauss_mul_conj_unnormalized {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r) = (Real.sqrt (norm r):ℂ) := by
  rw [star_mul]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (norm r):ℂ)*(gauss r*(starRingEnd ℂ) (gauss r)) := by ring
    _ = _ := by
      rw [Complex.mul_conj',norm_gauss_of_squarefree hr hs]
      norm_num

lemma angular_conjugate_ratio {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ)) = theta (3*ℓ) r := by
  have hz : (r:ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  have hn : (‖(r:ℂ)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hratio : star (r:ℂ)/(r:ℂ) = ((r:ℂ)/(‖(r:ℂ)‖:ℂ))^(-2:ℤ) := by
    rw [zpow_neg,zpow_ofNat,← inv_pow,inv_div]
    field_simp
    simpa [pow_two,mul_comm] using (Complex.mul_conj' (r:ℂ))
  rw [hratio,← zpow_mul]
  simp only [theta]
  rw [← zpow_add₀ (div_ne_zero hz hn)]
  congr 1
  ring

lemma metaplecticPrefactor_normalization {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (ℓ : ℤ) :
    gauss r*theta ℓ r*metaplecticRawPrefactor r ℓ = metaplecticPrefactor r ℓ := by
  unfold metaplecticRawPrefactor metaplecticPrefactor
  calc
    _ = (gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r))/
        ((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ))) := by ring
    _ = _ := by
      rw [gauss_mul_conj_unnormalized hr hs,angular_conjugate_ratio (primary_ne_zero hr)]
      push_cast
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticAngularShift_nonneg (ℓ : ℤ) : 0 ≤ metaplecticAngularShift ℓ := by
  unfold metaplecticAngularShift
  positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTransformContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour motion for the actual angular metaplectic transform. The two
fixed shifted Hecke Gamma strip estimates are the same published Stirling
input already used for the individual Hecke transforms. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticGamma_shift_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ-1/6) s *
      angularGammaFEQuotient (metaplecticAngularShift ℓ+1/6) s := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  push_cast
  rw [hk]
  have h1 : 1-s+((|ℓ|:ℤ)/2-1/6) = 5/6+(|ℓ|:ℤ)/2-s := by ring
  have h2 : 1-s+((|ℓ|:ℤ)/2+1/6) = 7/6+(|ℓ|:ℤ)/2-s := by ring
  have h3 : s+((|ℓ|:ℤ)/2-1/6) = s+(|ℓ|:ℤ)/2-1/6 := by ring
  have h4 : s+((|ℓ|:ℤ)/2+1/6) = s+(|ℓ|:ℤ)/2+1/6 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma metaplecticGamma_strip_bound (ℓ : ℤ) (a : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ (σ+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨Cm,Nm,hCm,hgm⟩ := hm
  obtain ⟨Cp,Np,hCp,hgp⟩ := hp
  refine ⟨Cm*Cp,Nm+Np,mul_nonneg hCm hCp,?_⟩
  intro σ hσ t
  rw [metaplecticGamma_shift_factor,norm_mul]
  calc
    _ ≤ (Cm*(1+|t|)^Nm)*(Cp*(1+|t|)^Np) :=
      mul_le_mul (hgm σ hσ t) (hgp σ hσ t) (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma differentiableOn_metaplecticGammaQuotient (ℓ : ℤ) :
    DifferentiableOn ℂ (metaplecticGammaQuotient ℓ) {s : ℂ | s.re < 5/6} := by
  intro s hs
  have hk : 0 ≤ ((|ℓ|:ℤ):ℝ)/2 := by positivity
  have hreg (c : ℝ) (hc : 5/6 ≤ c) :
      ∀ n : ℕ, (c:ℂ)+(|ℓ|:ℤ)/2-s ≠ -(n:ℂ) := by
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,Complex.ofReal_re,
      Complex.intCast_re,Complex.neg_re,Complex.natCast_re] at he
    change s.re < 5/6 at hs
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  have h1 := (Complex.differentiableAt_Gamma ((5/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (5/6) le_rfl)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (5/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h2 := (Complex.differentiableAt_Gamma ((7/6:ℂ)+(|ℓ|:ℤ)/2-s)
    (by simpa using hreg (7/6) (by norm_num))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => (7/6:ℂ)+(|ℓ|:ℤ)/2-z) s by fun_prop)
  have h3 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2-1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2-1/6) s by fun_prop)
  have h4 := (Complex.differentiable_one_div_Gamma (s+(|ℓ|:ℤ)/2+1/6)).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(|ℓ|:ℤ)/2+1/6) s by fun_prop)
  convert ((h1.mul h2).mul (h3.mul h4)).differentiableWithinAt using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  dsimp [metaplecticGammaQuotient]
  ring

lemma norm_angularGammaFEQuotient_half {k : ℝ} (hk : -1/2 < k) (t : ℝ) :
    ‖angularGammaFEQuotient k ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  let z : ℂ := (1/2:ℂ)+(t:ℂ)*Complex.I+(k:ℂ)
  have hz : 0 < z.re := by dsimp [z]; simp; linarith
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have he : 1-((1/2:ℂ)+(t:ℂ)*Complex.I)+(k:ℂ) = starRingEnd ℂ z := by
    dsimp [z]
    simp only [map_add,map_mul,map_div₀,map_one,map_ofNat,
      Complex.conj_ofReal,Complex.conj_I]
    ring
  unfold angularGammaFEQuotient
  rw [he,Complex.Gamma_conj,norm_div,Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hG)

lemma norm_metaplecticGamma_half (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)‖ = 1 := by
  rw [metaplecticGamma_shift_factor,norm_mul,
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),
    norm_angularGammaFEQuotient_half (by linarith [metaplecticAngularShift_nonneg ℓ]),one_mul]

private lemma metaplectic_scale_strip {a b v : ℝ} (hv : 0 < v)
    {σ : ℝ} (hσ : σ ∈ Icc a b) :
    v^σ ≤ max (v^a) (v^b) := by
  by_cases h : 1 ≤ v
  · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hv (le_of_not_ge h) hσ.1).trans (le_max_left _ _)

/-- Exact vertical contour move for the transform integrand. The scale
may lie on either side of one. -/
theorem metaplectic_transform_contour (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {a b v : ℝ} (hab : a ≤ b) (hb : b ≤ 1/2)
    (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) a)
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) a) :
    (∫ t : ℝ, (v:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((a:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((a:ℂ)+(t:ℂ)*Complex.I)) =
    ∫ t : ℝ, (v:ℂ)^((b:ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((b:ℂ)+(t:ℂ)*Complex.I)*
      mellin W ((b:ℂ)+(t:ℂ)*Complex.I) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_strip_bound ℓ a hm hp
  let L : ℂ → ℂ := fun s => (v:ℂ)^s*metaplecticGammaQuotient ℓ s
  let D : ℝ := max (v^a) (v^b)*C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖L (σ+((t-0:ℝ):ℂ)*Complex.I)‖ ≤ D*(1+|t-0|)^N := by
    simp only [sub_zero]
    dsimp [L]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    calc
      _ ≤ max (v^a) (v^b)*(C*(1+|t|)^N) :=
        mul_le_mul (metaplectic_scale_strip hv hσ) (hQ σ ⟨hσ.1,hσ.2.trans hb⟩ t)
          (_root_.norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; ring
  have : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hd : DifferentiableOn ℂ L (closedVerticalStrip a b) := by
    apply (differentiable_const_cpow_of_neZero _).differentiableOn.mul
    exact (differentiableOn_metaplecticGammaQuotient ℓ).mono (by
      intro s hs
      exact lt_of_le_of_lt (hs.2.trans hb) (by norm_num))
  let f : ℂ → ℂ := fun s => mellin W s*L s
  have hf : DifferentiableOn ℂ f (closedVerticalStrip a b) :=
    (smooth_mellin_entire W hW hpos hsm.continuous).differentiableOn.mul hd
  obtain ⟨K,_hK,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm
    (Z := 1) (by norm_num) 0 L hD N hg
  have hmajor (σ : ℝ) (hσ : σ ∈ Icc a b) (t : ℝ) :
      ‖f (σ+(t:ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K t := by
    simpa only [f,sub_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using hbound σ hσ t
  have hs := mellin_contour_shift_of_majorant hab f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 hmajor
  convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> funext t <;> dsimp [f,L] <;> ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support turns the literal completed sum, at every translated
height, into the finite primary cube polynomial used by Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplecticPrimaryPair_injective : Function.Injective metaplecticPrimaryPair := by
  intro du ev h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma metaplecticPrimalSupport_of_nonzero {r : Eisenstein} (ℓ : ℤ)
    (W : ℝ → ℂ) {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (du : PrimaryArgument × PrimaryArgument)
    (hn : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) ≠ 0) :
    du ∈ metaplecticPrimalSupport V := by
  have hnW : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) ≠ 0 := by
    intro hh
    exact hn (by simp [metaplecticPrimalCoefficient,hh])
  have hsize : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V := by
    have hb : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ B*X := by
      by_contra h
      exact hnW (hW _ ((lt_div_iff₀ hX).mpr (lt_of_not_ge h)))
    exact hb.trans hBV
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    primary_mul du.2.property hcube
  have hd : (du.1:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) :=
    (dvd_pow_self du.1.val (by norm_num : (3:ℕ) ≠ 0)).trans (dvd_mul_left _ _)
  have hu : (du.2:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) := dvd_mul_right _ _
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.1.property,(norm_le_of_dvd (primary_ne_zero hp) hd).trans hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.2.property,(norm_le_of_dvd (primary_ne_zero hp) hu).trans hsize⟩

/-- Exact finite support, independent of the height parameter. -/
theorem metaplecticHeightCompleted_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ metaplecticPrimalElementSupport V,
        metaplecticPrimalCoefficient r ℓ W X du*mellinPhase t (norm (metaplecticCubeProduct du)) := by
  rw [metaplecticHeightCompleted,tsum_eq_sum (s := metaplecticPrimalSupport V) (fun du hdu => ?_)]
  · rw [metaplecticPrimalElementSupport,Finset.sum_image]
    exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h
  · have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      exact hdu (metaplecticPrimalSupport_of_nonzero ℓ W hX hBV hW du hn)
    rw [hc,zero_mul]

/-- Exact norm twist needed to apply the published Voronoi formula at
height t; its outside scalar has modulus one. -/
theorem metaplecticHeightCompleted_twist (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t = mellinPhase t X*
      metaplecticCompleted r ℓ (fun x => W x*mellinPhase t x) X := by
  unfold metaplecticHeightCompleted metaplecticCompleted
  rw [←tsum_mul_left]
  apply tsum_congr
  intro du
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hn : 0 < norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    norm_pos_of_ne_zero (primary_ne_zero (primary_mul du.2.property hcube))
  have ht : mellinPhase t X*mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) =
      mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) := by
    rw [←mellinPhase_mul_pos t hX (div_pos hn hX)]
    congr 1
    field_simp
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [metaplecticPrimalCoefficient,metaplecticPrimaryPair,
      hc,ite_true, if_true,metaplecticCubeProduct] at ht ⊢
    rw [←ht]
    ring
  · simp only [metaplecticPrimalCoefficient,metaplecticPrimaryPair,
      hc,ite_false, if_false,zero_mul,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualTailWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exponent bookkeeping for truncating the metaplectic dual
series. The cutoff is in the actual norm N(d³ν). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplecticDualNorm_pos (nd : MetaplecticDualArgument × PrimaryArgument) :
    0 < metaplecticDualNorm nd :=
  mul_pos (pow_pos (norm_pos_of_ne_zero (primary_ne_zero nd.2.property)) _)
    (Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTwistedTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm twist in the original Voronoi formula is exactly the
translated Mellin variable in the shifted transform. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma mellin_mul_phase (W : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    mellin (fun x => W x*mellinPhase t x) s = mellin W (s+(t:ℂ)*Complex.I) := by
  calc
    _ = mellin (fun x => (x:ℂ)^((t:ℂ)*Complex.I) • W x) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [mellinPhase_eq_cpow hx t]
      simp only [smul_eq_mul]
      ring
    _ = _ := mellin_cpow_smul W s ((t:ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShiftedVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published small-line formula equals the actual far-left series.
Every contour change is proved for the literal transform before summing. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplecticDualNorm_eq (nd : MetaplecticDualArgument × PrimaryArgument) :
    Complex.normSq (((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1) =
      metaplecticDualNorm nd := by
  rw [Complex.normSq_mul,map_pow]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed first column with lower-right entry divisible by nine.
This makes the common-lattice additive phase a literal residue character. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaNineGaussMatrix_multiplier (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) j=cubicSymbol r u := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCuspMultiplier_constant g hc hd j,
    cubicThetaPrimaryBottom_multiplier_adapted g hc ha hd,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).1,
    cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr,
    cubicSymbol_cube_of_isCoprime hr lambdaE (primary_coprime_lambda hr),one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCuspCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dual three-cusp coefficient before local cube cancellation.
All dependence on a coprime additive numerator is in its cubic character. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaProjectedCoefficient_factor (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0)
    (hd : (3:Eisenstein)∣g 1 1) (n : Eisenstein) :
    cubicThetaProjectedCoefficient g hc n=
      star (cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc))*
        cubicThetaCommonCuspCoefficient n := by
  have ht (j : Fin 3) : cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j)=
      cubicThetaActualCuspCoefficient (j.val:ℤ) :=
    cubicThetaActualCuspCoefficient_periodic (cubicThetaProjectedCuspType_congr g hc ha j)
  unfold cubicThetaProjectedCoefficient cubicThetaCommonCuspCoefficient
  simp_rw [cubicThetaProjectedCuspMultiplier_constant g hc hd,ht]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cubicThetaNineGaussMatrix_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (n : Eisenstein) :
    cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) n=
      star (cubicSymbol r u)*cubicThetaCommonCuspCoefficient n := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCoefficient_factor g hc ha hd]
  have he := cubicThetaProjectedCuspMultiplier_constant g hc hd (0:Fin 3)
  rw [cubicThetaNineGaussMatrix_multiplier] at he
  rw [←he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing an unramified prime cube preserves the exact arithmetic
support. Consequently cube scaling holds on every index, including the
zero extension of all three coefficient families. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinates_primeCube_dvd {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : p ∣ R.cubePart := by
  by_contra hd
  have hpu : IsCoprime p (R.unit:Eisenstein) := hp.2.coprime_iff_not_dvd.mpr
    (fun hv => hp.2.not_isUnit (isUnit_of_dvd_unit hv R.unit.isUnit))
  have hpl : IsCoprime p (lambdaE^R.order) := (primary_coprime_lambda hp.1).pow_right
  have hpd : IsCoprime p (R.cubePart^3) := (hp.2.coprime_iff_not_dvd.mpr hd).pow_right
  have hc : p^2 ∣ R.squarefreePart := by
    have heq : n*p^3=((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      R.numerator_eq.trans (by ring)
    have he : p^2 ∣ ((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      ((pow_dvd_pow p (by omega : 2 ≤ 3)).trans (dvd_mul_left (p^3) n)).trans (dvd_of_eq heq)
    exact ((hpu.mul_right hpl).mul_right hpd).pow_left.dvd_of_dvd_mul_left he
  exact hp.2.not_isUnit (R.squarefree p (by simpa only [pow_two] using hc))

theorem cubicThetaCoordinates_remove_primeCube {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨d,hd⟩ := cubicThetaCoordinates_primeCube_dvd hp R
  have hdp : primary d := primary_of_mul hp.1 (hd ▸ R.cube_primary)
  refine ⟨{
    unit := R.unit
    order := R.order
    squarefreePart := R.squarefreePart
    cubePart := d
    squarefree_primary := R.squarefree_primary
    cube_primary := hdp
    squarefree := R.squarefree
    numerator_eq := ?_ }⟩
  apply mul_right_cancel₀ (pow_ne_zero 3 hp.2.ne_zero)
  calc
    n*p^3 = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
    _ = ((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*d^3))*p^3 := by rw [hd]; ring

theorem cubicThetaCoordinates_primeCube_iff {p n : Eisenstein} (hp : primaryPrime p) :
    Nonempty (CubicThetaCoordinates (n*p^3)) ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨R⟩
    exact cubicThetaCoordinates_remove_primeCube hp R
  · rintro ⟨R⟩
    exact ⟨R.mulPrimaryCube p hp.1⟩

theorem cubicThetaArithmeticCoefficient_primeCube {p : Eisenstein} (hp : primaryPrime p)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*p^3)=(norm p:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  classical
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · exact cubicThetaArithmeticCoefficient_mulPrimaryCube (Classical.choice hn) p hp.1
  · have hnp := mt (cubicThetaCoordinates_primeCube_iff hp).mp hn
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hnp,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCubeScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a primary cube scales the actual three-cusp coefficient by
its norm. This includes all zero-extension cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaArithmeticCoefficient_primaryCube (d : Eisenstein) (hd : primary d)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  revert n
  apply primary_induction (b:=d) ?_ ?_ hd
  · intro n
    have h1 : norm (1:Eisenstein)=1 := by norm_num [norm]
    simp only [one_pow,mul_one,h1,Complex.ofReal_one,inv_one,one_mul]
  · intro p b hp hb ih n
    rw [show n*(p*b)^3=(n*p^3)*b^3 by ring,ih,
      cubicThetaArithmeticCoefficient_primeCube hp,norm_mul_eq,Complex.ofReal_mul,mul_inv_rev]
    ring

lemma cubicThetaShiftedLatticeCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaShiftedLatticeCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaShiftedLatticeCoefficient j n := by
  have hp : primary (d^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using primary_mul hd (primary_mul hd hd)
  have hl3 : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
    rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
  have hl : lambdaE∣n*d^3-n := by
    have H := dvd_mul_of_dvd_right (dvd_trans hl3 hp) n
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hi : lambdaE∣n*d^3-(j:Eisenstein) ↔ lambdaE∣n-(j:Eisenstein) := by
    constructor
    · intro h
      convert dvd_sub h hl using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · intro h
      convert dvd_add h hl using 1
      all_goals try with_reducible_and_instances rfl
      ring
  unfold cubicThetaShiftedLatticeCoefficient
  rw [hi]
  split_ifs
  · rw [show 3*(lambdaE*(n*d^3))=(3*(lambdaE*n))*d^3 by ring,
      cubicThetaArithmeticCoefficient_primaryCube d hd]
    ring
  · ring

lemma cubicThetaActualCuspCoefficient_primaryCube (j : ℤ) (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaActualCuspCoefficient j (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaActualCuspCoefficient j n := by
  unfold cubicThetaActualCuspCoefficient
  split_ifs
  · exact cubicThetaArithmeticCoefficient_primaryCube d hd n
  · exact cubicThetaShiftedLatticeCoefficient_primaryCube j d hd n

theorem cubicThetaCommonCuspCoefficient_primaryCube (d : Eisenstein)
    (hd : primary d) (n : Eisenstein) :
    cubicThetaCommonCuspCoefficient (n*d^3)=
      (norm d:ℂ)⁻¹*cubicThetaCommonCuspCoefficient n := by
  unfold cubicThetaCommonCuspCoefficient
  simp_rw [show -(n*d^3)=(-n)*d^3 by ring,
    cubicThetaActualCuspCoefficient_primaryCube _ d hd,star_mul]
  simp only [map_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-cusp coefficient has squarefree-times-cube support.
This is proved for the constructed cusps, including their ramified shifts. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaArithmetic_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  unfold cubicThetaArithmeticCoefficient
  apply dite_eq_right
  exact fun he => hn ((cubicThetaCoordinates_primary_power_iff hh e k).mp he)

lemma cubicThetaCommon_zero_of_no_primary_coordinates {h : Eisenstein}
    (hh : primary h)
    (hn : ¬∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3)
    (e : Eisensteinˣ) (k : ℕ) :
    cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*h)=0 := by
  have hbase : cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    simpa only [Units.val_neg,neg_mul] using
      cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn (-e) k
  have hshift : cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h))))=0 := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*h)))=
        (e:Eisenstein)*lambdaE^(k+3)*h := by
      rw [pow_add,pow_succ,lambdaE_sq]
      ring
    rw [he]
    exact cubicThetaArithmetic_zero_of_no_primary_coordinates hh hn e (k+3)
  have hc (j : ℤ) :
      cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*h))=0 := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hbase
    · simp only [cubicThetaShiftedLatticeCoefficient,hshift,mul_zero,ite_self]
  unfold cubicThetaCommonCuspCoefficient
  simp only [hc,star_zero,mul_zero,Finset.sum_const_zero,zero_div]

theorem cubicThetaCommonCuspCoefficient_support {n : Eisenstein} (hn : n≠0)
    (ha : cubicThetaCommonCuspCoefficient n≠0) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨e,k,h,hh,he⟩ := unit_ramified_primary_decomposition hn
  obtain ⟨c,d,hc,hd,hs,hcd⟩ :
      ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3 := by
    by_contra hbad
    rw [he,cubicThetaCommon_zero_of_no_primary_coordinates hh hbad] at ha
    exact ha rfl
  exact ⟨{
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := by rw [he,hcd] }⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual support is indexed once by its unit, ramified order,
squarefree primary factor and primary cube factor. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCommonNumerator_injective : Function.Injective cubicThetaCommonNumerator := by
  rintro ⟨u,k,cd⟩ ⟨v,l,ef⟩ he
  have hp (x : CubicThetaPrimaryPair) : primary (x.val.1*x.val.2^3) :=
    primary_mul x.property.1 (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul x.property.2.1 (primary_mul x.property.2.1 x.property.2.1))
  have h := unit_ramified_primary_unique (hp cd) (hp ef) he
  have hc := primary_squarefree_cube_unique cd.property.1 cd.property.2.1
    ef.property.1 ef.property.2.1 cd.property.2.2 ef.property.2.2 h.2.2
  have hcd : cd=ef := Subtype.ext (Prod.ext hc.1 hc.2)
  exact Prod.ext h.1 (Prod.ext h.2.1 hcd)

lemma cubicThetaCommonNumerator_range (n : Eisenstein) :
    n∈Set.range cubicThetaCommonNumerator ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x⟩
  · rintro ⟨R⟩
    refine ⟨(R.unit,R.order,⟨(R.squarefreePart,R.cubePart),
      R.squarefree_primary,R.cube_primary,R.squarefree⟩),?_⟩
    exact R.numerator_eq.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTwistFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fourier inversion for the periodic numerator twists in the
cubic theta formula. The trace pairing is perfect for primary moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaResidueChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    cubicThetaResidueChar q hq (Ideal.Quotient.mk (modulus q) a) =
      (Real.fourierChar (tracePair (a:ℂ) (1/(q:ℂ))):ℂ) := by
  rw [cubicThetaResidueChar,AddChar.mulShift_apply,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]

lemma cubicThetaResidueChar_primitive {q : Eisenstein} (hq : primary q) :
    (cubicThetaResidueChar q (primary_ne_zero hq)).IsPrimitive := by
  let u : (Residues q)ˣ := (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) lambdaE :=
    (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit_spec
  intro a ha he
  have hna : (u:Residues q)*a ≠ 0 := by
    intro hz
    apply ha
    have h := congrArg (fun x : Residues q => (u⁻¹:((Residues q)ˣ))*x) hz
    simpa only [←mul_assoc,Units.inv_mul,mul_zero,one_mul] using h
  apply residueFourierChar_isPrimitive q (primary_ne_zero hq)
    (a := (u:Residues q)*a) hna
  simpa only [cubicThetaResidueChar,AddChar.mulShift_mulShift,←hu] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamanujan
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Ramanujan sum in the trace normalization of the actual
cubic theta series. Its weight is the cube of the cubic residue character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaSymbol_cube_indicator {r : Eisenstein} (hr : primary r) (x : Eisenstein) :
    cubicSymbol r x^3=(if IsCoprime r x then 1 else 0) := by
  by_cases hx : IsCoprime r x
  · rw [ite_eq_left hx,cubicSymbol_cube_of_isCoprime hr x hx]
  · rw [ite_eq_right hx,cubicSymbol_eq_zero_of_not_isCoprime hr hx]
    norm_num

lemma cubicThetaRamanujan_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan p h=if p∣h then (norm p:ℂ)-1 else -1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicThetaResidueChar p hp.2.ne_zero
  let a := Ideal.Quotient.mk (modulus p) h
  have ha : a=0 ↔ p∣h := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hc (x : Residues p) : IsCoprime p (residueRepresentative p x) ↔ x≠0 := by
    constructor
    · intro hx
      have hu := residue_isUnit_of_isCoprime hx
      rw [residueRepresentative_spec,isUnit_iff_ne_zero] at hu
      exact hu
    · intro hx
      apply isCoprime_of_residue_isUnit
      rw [residueRepresentative_spec]
      exact isUnit_iff_ne_zero.mpr hx
  have he (x : Residues p) : additivePhase p (h*residueRepresentative p x)=χ (a*x) := by
    rw [additivePhase_fourierChar]
    have hh := cubicThetaResidueChar_mk p hp.2.ne_zero (h*residueRepresentative p x)
    rw [map_mul,residueRepresentative_spec] at hh
    exact hh.symm
  rw [cubicThetaRamanujan,tsum_fintype]
  simp_rw [cubicThetaSymbol_cube_indicator hp.1,hc,he]
  have hs : (∑ x : Residues p,(if x≠0 then (1:ℂ) else 0)*χ (a*x))=
      (∑ x : Residues p,χ (a*x))-1 := by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [ne_eq,not_true_eq_false,ite_false, if_false,mul_zero,zero_mul,χ.map_zero_eq_one,add_zero]
    rw [eq_sub_iff_add_eq]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [mul_zero,χ.map_zero_eq_one]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_left (Finset.ne_of_mem_erase hx),one_mul]
  rw [hs]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift a (cubicThetaResidueChar_primitive hp.1),ha]
  have hn : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  split_ifs <;> simp_all

lemma cubicThetaRamanujan_one (h : Eisenstein) : cubicThetaRamanujan 1 h=1 := by
  have he := frequencyGauss_one h
  have hn : norm (1:Eisenstein)=1 := by norm_num [norm]
  rw [frequencyGauss,hn,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul] at he
  simpa only [frequencyGauss,cubicThetaRamanujan,cubicSymbol_one_lower,one_pow,one_mul,
    norm_one,Real.sqrt_one,Complex.ofReal_one,inv_one] using he

lemma cubicThetaRamanujan_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    cubicThetaRamanujan (a*b) h=cubicThetaRamanujan a h*cubicThetaRamanujan b h := by
  let : Finite (Residues a) := finite_residues (primary_ne_zero ha)
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b)
    (residueMix_bijective (primary_ne_zero ha) (primary_ne_zero hb) hab)
  let f (q : Eisenstein) (x : Residues q) : ℂ :=
    cubicSymbol q (residueRepresentative q x)^3*additivePhase q (h*residueRepresentative q x)
  have ht (v : Residues a × Residues b) : f (a*b) (e v)=f a v.1*f b v.2 := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h*residueRepresentative (a*b) (e v))=
        Ideal.Quotient.mk (modulus (a*b))
          (h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      rw [map_mul,map_mul,heq]
    dsimp only [f]
    rw [cubicSymbol_congr heq]
    rw [additivePhase_congr (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
      heqh]
    rw [cubicSymbol_mix ha hb,mul_pow,mul_pow,mul_pow,
      cubicSymbol_cube_of_isCoprime ha b hab,cubicSymbol_cube_of_isCoprime hb a hab.symm]
    rw [show h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2)=
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix (primary_ne_zero ha) (primary_ne_zero hb)]
    ring
  simp only [cubicThetaRamanujan,tsum_fintype]
  change (∑ x : Residues (a*b),f (a*b) x)=(∑ x,f a x)*(∑ x,f b x)
  rw [←Equiv.sum_comp e (f (a*b))]
  simp_rw [ht]
  rw [Fintype.sum_prod_type,←Finset.sum_mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamanujanProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Ramanujan average is precisely the squarefree local
Euler coefficient in the published Voronoi formula. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRamanujan_prod (s : Finset Eisenstein)
    (hp : ∀ p∈s,primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan (∏ p∈s,p) h=
      ∏ p∈s,if p∣h then (norm p:ℂ)-1 else -1 := by
  induction s using Finset.induction_on with
  | empty => simp [cubicThetaRamanujan_one]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q∈s,primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q∈s,q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
    rw [Finset.prod_insert hps,cubicThetaRamanujan_mul hp'.1 hprimary hc,
      cubicThetaRamanujan_prime hp',ih hs,Finset.prod_insert hps]

theorem cubicThetaRamanujan_squarefree {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (n : MetaplecticDualArgument) :
    cubicThetaRamanujan r n.val=metaplecticLocalCoefficient r n := by
  calc
    _ = ∏ p∈primaryPrimeFactors r,if p∣n.val then (norm p:ℂ)-1 else -1 := by
      conv_lhs => rw [←primaryPrimeFactors_prod hr hs]
      exact cubicThetaRamanujan_prod _ (fun p hp => (primaryPrimeFactor_spec hr hp).1) n.val
    _ = _ := by
      unfold metaplecticLocalCoefficient
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> push_cast <;> rfl

lemma cubicTheta_sum_eq_units {R : Type*} [CommRing R] [Fintype R]
    (f : R→ℂ) (hf : ∀ x,¬IsUnit x→f x=0) :
    (∑ x : R,f x)=∑ u : Rˣ,f u := by
  have hs : Function.support f ⊆ {x | IsUnit x} := by
    intro x hx
    by_contra hu
    exact hx (hf x hu)
  let e := (Submonoid.unitsTypeEquivIsUnitSubmonoid (M:=R)).toEquiv
  calc
    _ = ∑' x : R,f x := (tsum_fintype _).symm
    _ = ∑' x : {x : R // IsUnit x},f x := (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' u : Rˣ,f u := (e.tsum_eq (fun x => f x.val)).symm
    _ = _ := tsum_fintype _

theorem cubicThetaRamanujan_units {r : Eisenstein} (hr : primary r)
    [Fintype (Residues r)] (h : Eisenstein) :
    cubicThetaRamanujan r h=
      ∑ u : (Residues r)ˣ,additivePhase r (h*residueRepresentative r u) := by
  rw [cubicThetaRamanujan,tsum_fintype]
  have hz (x : Residues r) (hx : ¬IsUnit x) :
      cubicSymbol r (residueRepresentative r x)^3*additivePhase r (h*residueRepresentative r x)=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro hh
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime hh)
    rw [cubicThetaSymbol_cube_indicator hr,ite_eq_right hn,zero_mul]
  rw [cubicTheta_sum_eq_units _ hz]
  apply Finset.sum_congr rfl
  intro u _
  have hu : IsCoprime r (residueRepresentative r u) := by
    apply isCoprime_of_residue_isUnit
    rw [residueRepresentative_spec]
    exact u.isUnit
  rw [cubicThetaSymbol_cube_indicator hr,ite_eq_left hu,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-cube scaling of the actual dual coefficient and its
local Ramanujan factor. These are the algebraic inputs to free-cube removal. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFrequency_mul_cube (n d : Eisenstein) :
    cubicThetaFrequency (n*d^3)=cubicThetaFrequency n*(d:ℂ)^3 := by
  unfold cubicThetaFrequency
  push_cast
  ring

lemma cubicThetaLocalCoefficient_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument) :
    metaplecticLocalCoefficient r (cubicThetaDualCube d hd n)=
      metaplecticLocalCoefficient r n := by
  unfold metaplecticLocalCoefficient
  apply Finset.prod_congr rfl
  intro p hp
  have hs := primaryPrimeFactor_spec hr hp
  have hpd : ¬p∣d := fun h => hs.1.2.not_isUnit (hcop.isUnit_of_dvd' h hs.2)
  have he : p∣n.val*d^3 ↔ p∣n.val := by
    constructor
    · intro h
      rcases hs.1.2.dvd_mul.mp h with h | h
      · exact h
      · exact False.elim (hpd (hs.1.2.dvd_of_dvd_pow h))
    · intro h
      exact dvd_mul_of_dvd_left h _
  simp only [cubicThetaDualCube,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCusps
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational-cusp lift on every residue. Nonunit residues get
an arbitrary determinant-one lift, and their cubic character weight is zero. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaProjectedCoefficient_congr {g h : SL(2,Eisenstein)} (he : g=h)
    (hg : primary (g 1 0)) (hh : primary (h 1 0)) :
    cubicThetaProjectedCoefficient g hg = cubicThetaProjectedCoefficient h hh := by
  subst h
  rfl

lemma cubicThetaResidueCuspMatrix_of_coprime (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaResidueCuspMatrix r hr u = cubicThetaNineGaussMatrix r hr u hu := by
  exact dite_eq_left hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVoronoiScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency bookkeeping for the constructed transform. The common
cusp numerator `n` represents `n/lambda^4`; the published dual argument
represents `n/lambda`. The conversion is recorded without changing either
normalization or identifying the two transform arguments. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_metaplectic_normSq (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n)=norm n.val/3 := by
  rw [metaplecticFrequency,Complex.normSq_div,traceLambda_normSq]
  rfl

lemma cubicThetaLevelScale_fourth {r : Eisenstein} (_hr : primary r) :
    cubicThetaLevelScale r^4=(norm r^2)⁻¹ := by
  have hs := Real.sq_sqrt (norm_nonneg r)
  unfold cubicThetaLevelScale
  rw [inv_pow]
  congr 1
  nlinarith [sq_nonneg (Real.sqrt (norm r))]

lemma cubicThetaVoronoi_dual_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2=
      (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2) := by
  rw [cubicThetaDualScale,cubicThetaLevelScale_fourth hr,cubicThetaFrequency_sq,
    cubicTheta_metaplectic_normSq]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeCubeIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact bijection separating every primary cube factor into the
part supported on the level and the free part. No multiplicity is lost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicTheta_free_cube_tsum {r : Eisenstein} (hr : r≠0)
    (f : CubicThetaCommonIndex→ℂ) :
    (∑' x : CubicThetaCommonIndex,f x)=
      ∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,f (cubicThetaFreeCubeJoin r x) :=
  ((cubicThetaFreeCubeEquiv r hr).tsum_eq f).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineDualPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A lower-right entry divisible by nine identifies the actual dual
phase with an ordinary residue-ring additive character. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicTheta_additivePhase_one (a : Eisenstein) : additivePhase 1 a=1 := by
  rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (a-0))),additivePhase_zero]

lemma cubicTheta_trace_integral_phase (a : Eisenstein) :
    (Real.fourierChar (tracePair (a:ℂ) 1):ℂ)=1 := by
  simpa only [additivePhase_fourierChar,Subalgebra.coe_one,div_one] using cubicTheta_additivePhase_one a

lemma cubicThetaNineDual_phase (g : SL(2,Eisenstein)) (r δ : Eisenstein)
    (hc : g 1 0=r) (hd : g 1 1=9*δ) (n : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)):ℂ)=
      additivePhase r (-n*δ) := by
  have he : tracePair (cubicThetaFrequency n) (cubicThetaPrimaryDualCenter g)=
      tracePair ((n*δ:Eisenstein):ℂ) 1+
        tracePair ((-n*δ:Eisenstein):ℂ) (1/(r:ℂ)) := by
    rw [cubicThetaFrequency_div_nine]
    unfold cubicThetaPrimaryDualCenter
    rw [hc,hd]
    unfold tracePair
    push_cast
    simp only [mul_one,one_div]
    rw [←mul_add,←Complex.add_re]
    rw [show ((9:Eisenstein):ℂ)=(9:ℂ) from rfl]
    congr 2
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,cubicTheta_trace_integral_phase,one_mul]
  exact (additivePhase_fourierChar _ _).symm

lemma cubicThetaNineGaussMatrix_weighted_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) (n : Eisenstein) :
    cubicSymbol r u*cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
        (cubicThetaNineGaussMatrix_primary r hr u hu))
      (cubicThetaPrimaryDualCenter (cubicThetaNineGaussMatrix r hr u hu)) n=
      cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ) := by
  rw [cubicThetaCoefficientTwist,cubicThetaNineGaussMatrix_coefficient,
    cubicThetaNineDual_phase _ r δ (cubicThetaNineGaussMatrix_entries r hr u hu).2.1 hd]
  have he : cubicSymbol r u*star (cubicSymbol r u)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hr hu]
    norm_num
  calc
    _ = (cubicSymbol r u*star (cubicSymbol r u))*
      (cubicThetaCommonCuspCoefficient n*additivePhase r (-n*δ)) := by ring
    _ = _ := by rw [he,one_mul]

lemma cubicThetaNineGaussMatrix_inverse (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (δ : Eisenstein)
    (hd : cubicThetaNineGaussMatrix r hr u hu 1 1=9*δ) :
    r∣(9*lambdaE^3*u*δ)-1 := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,hd] at he
  refine ⟨g 0 1,?_⟩
  linear_combination he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInverseResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse residues arising from determinant-one cusp lifts permute
the actual unit group. No distribution or cancellation estimate is assumed. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaNineConductorUnit_val (r : Eisenstein) (hr : primary r) :
    (cubicThetaNineConductorUnit r hr:Residues r)=
      Ideal.Quotient.mk (modulus r) (9*lambdaE^3) :=
  (residue_isUnit_of_isCoprime
    ((cubicTheta_coprime_nine hr).mul_right ((primary_coprime_lambda hr).pow_right (n:=3)))).unit_spec

lemma cubicThetaNineUnitInverse_spec (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    cubicThetaNineGaussMatrix r hr (residueRepresentative r u)
      (cubicThetaUnitRepresentative_coprime r u) 1 1=9*cubicThetaNineUnitInverse r hr u :=
  Classical.choose_spec (cubicThetaNineGaussMatrix_nine r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u))

lemma cubicThetaNineUnitInverse_residue (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) :
    Ideal.Quotient.mk (modulus r) (cubicThetaNineUnitInverse r hr u)=
      (((cubicThetaNineConductorUnit r hr*u)⁻¹ : (Residues r)ˣ):Residues r) := by
  let A := cubicThetaNineConductorUnit r hr
  let δ := cubicThetaNineUnitInverse r hr u
  have hd := cubicThetaNineGaussMatrix_inverse r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u) δ (cubicThetaNineUnitInverse_spec r hr u)
  have he := residue_eq_of_dvd_sub hd
  have hp : ((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ=1 := by
    rw [Units.val_mul,cubicThetaNineConductorUnit_val]
    simpa only [map_mul,map_pow,map_one,residueRepresentative_spec,mul_assoc] using he
  have hi : (((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r)=1 :=
    (A*u).inv_mul
  change Ideal.Quotient.mk (modulus r) δ=_
  calc
    _ = 1*Ideal.Quotient.mk (modulus r) δ := (one_mul _).symm
    _ = ((((A*u)⁻¹:(Residues r)ˣ):Residues r)*((A*u:(Residues r)ˣ):Residues r))*
        Ideal.Quotient.mk (modulus r) δ := by rw [hi]
    _ = (((A*u)⁻¹:(Residues r)ˣ):Residues r)*
        (((A*u:(Residues r)ˣ):Residues r)*Ideal.Quotient.mk (modulus r) δ) := mul_assoc _ _ _
    _ = _ := by rw [hp,mul_one]

theorem cubicThetaNineUnitInverse_average (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] (n : Eisenstein) :
    (∑ u : (Residues r)ˣ,additivePhase r (-n*cubicThetaNineUnitInverse r hr u))=
      cubicThetaRamanujan r n := by
  let A := cubicThetaNineConductorUnit r hr
  let e : Equiv.Perm ((Residues r)ˣ) :=
    ((Equiv.mulLeft A).trans (Equiv.inv _)).trans (Equiv.neg _)
  have he (u : (Residues r)ˣ) : (e u:Residues r)=
      -((((A*u)⁻¹:(Residues r)ˣ):Residues r)) := rfl
  have ht (u : (Residues r)ˣ) :
      additivePhase r (-n*cubicThetaNineUnitInverse r hr u)=
        additivePhase r (n*residueRepresentative r (e u)) := by
    apply additivePhase_congr (primary_ne_zero hr)
    rw [map_mul,map_mul,residueRepresentative_spec,he,map_neg,
      cubicThetaNineUnitInverse_residue]
    ring
  simp_rw [ht]
  calc
    _ = ∑ u : (Residues r)ˣ, additivePhase r (n*residueRepresentative r u) :=
      Equiv.sum_comp e (fun u : (Residues r)ˣ => additivePhase r (n*residueRepresentative r u))
    _ = _ := (cubicThetaRamanujan_units hr n).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueLocalCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite dual cusp coefficient equals the universal
three-cusp coefficient times the exact local Ramanujan product. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaResidueDualCoefficient_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (n : MetaplecticDualArgument) :
    cubicThetaResidueDualCoefficient r hr n.val=
      cubicThetaCommonCuspCoefficient n.val*metaplecticLocalCoefficient r n := by
  let F (x : Residues r) : ℂ := cubicSymbol r (residueRepresentative r x)*
    cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r x)))
      (cubicThetaPrimaryDualCenter (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))) n.val
  have hz (x : Residues r) (hx : ¬IsUnit x) : F x=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro h
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime h)
    dsimp only [F]
    rw [cubicSymbol_eq_zero_of_not_isCoprime hr hn,zero_mul]
  have ht (u : (Residues r)ˣ) : F u=
      cubicThetaCommonCuspCoefficient n.val*
        additivePhase r (-n.val*cubicThetaNineUnitInverse r hr u) := by
    have hu := cubicThetaUnitRepresentative_coprime r u
    have hg := cubicThetaResidueCuspMatrix_of_coprime r hr _ hu
    have ha := cubicThetaProjectedCoefficient_congr hg
      (cubicThetaResidueCuspPrimary r hr _) (cubicThetaNineGaussMatrix_primary r hr _ hu)
    have hz := congrArg cubicThetaPrimaryDualCenter hg
    dsimp only [F,cubicThetaCoefficientTwist]
    rw [ha,hz]
    have H := cubicThetaNineGaussMatrix_weighted_coefficient r hr (residueRepresentative r u) hu
      (cubicThetaNineUnitInverse r hr u) (cubicThetaNineUnitInverse_spec r hr u) n.val
    exact H
  change (∑ x : Residues r,F x)=_
  rw [cubicTheta_sum_eq_units F hz]
  simp_rw [ht]
  rw [←Finset.mul_sum,cubicThetaNineUnitInverse_average,cubicThetaRamanujan_squarefree hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero-angular summation formula with the finite cusp
average evaluated as its exact Ramanujan Euler product. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaResidueDualTerm_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaResidueDualTerm r hr rev k W σ X=cubicThetaLocalDualTerm r rev k W σ X := by
  funext n
  unfold cubicThetaResidueDualTerm cubicThetaLocalDualTerm
  rw [cubicThetaResidueDualCoefficient_local hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalCubeTerm
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact free-cube denominator and transform argument in each actual
local dual term. The exponent 5/2 is derived, not assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_norm_sqrt (d : Eisenstein) : ‖(d:ℂ)‖=Real.sqrt (norm d) := by
  rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]

lemma cubicTheta_five_halves (d : Eisenstein) :
    norm d^(5/2:ℝ)=norm d*(Real.sqrt (norm d))^3 := by
  by_cases hd : d=0
  · subst d
    norm_num [norm]
  · rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (norm_nonneg d),
      show (5/2:ℝ)=1+(1/2:ℝ)*3 by norm_num,
      Real.rpow_add (norm_pos_of_ne_zero hd),Real.rpow_one]
    norm_num

lemma cubicThetaFrequency_cube_norm (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖=‖cubicThetaFrequency n‖*(Real.sqrt (norm d))^3 := by
  rw [cubicThetaFrequency_mul_cube,norm_mul,norm_pow,cubicTheta_norm_sqrt]

lemma cubicThetaFrequency_cube_square (n d : Eisenstein) :
    ‖cubicThetaFrequency (n*d^3)‖^2=‖cubicThetaFrequency n‖^2*norm d^3 := by
  rw [cubicThetaFrequency_cube_norm,mul_pow,←pow_mul,
    show (3:ℕ)*2=2*3 by norm_num,pow_mul,Real.sq_sqrt (norm_nonneg d)]

theorem cubicThetaLocalDualTerm_cube {r d : Eisenstein} (hr : primary r)
    (hd : primary d) (hcop : IsCoprime d r) (n : MetaplecticDualArgument)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ) :
    cubicThetaLocalDualTerm r rev k W σ X (cubicThetaDualCube d hd n)=
      theta (cubicThetaCircleOrder rev k) (n.val*d^3)*
        (cubicThetaCommonTau n.val*metaplecticLocalCoefficient r n)/
          ((‖cubicThetaFrequency n.val‖^2*norm d^(5/2:ℝ):ℝ):ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
              (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3) := by
  have hn0 : (‖cubicThetaFrequency n.val‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaFrequency_pos n.property).ne'
  have hd0 : (norm d:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hds0 : (Real.sqrt (norm d):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hd))).ne'
  unfold cubicThetaLocalDualTerm
  rw [cubicThetaLocalCoefficient_cube hr hd hcop]
  dsimp only [cubicThetaDualCube]
  change theta _ (n.val*d^3)*
    (cubicThetaCommonCuspCoefficient (n.val*d^3)*metaplecticLocalCoefficient r n)/
      (‖cubicThetaFrequency (n.val*d^3)‖:ℂ)*_= _
  rw [cubicThetaCommonCuspCoefficient_primaryCube d hd,cubicThetaFrequency_cube_square,
    cubicThetaFrequency_cube_norm,cubicTheta_five_halves,cubicThetaCommonTau]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  congr 1
  · field_simp
  · congr 1
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeLocalVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete angular transform with the free cube variable separated.
Both its coefficient bound and its absolutely convergent sum are proved. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaCommonArgument_injective : Function.Injective cubicThetaCommonArgument := by
  intro x y he
  exact cubicThetaCommonNumerator_injective (congrArg Subtype.val he)

lemma cubicThetaLocalDualTerm_reindex {r : Eisenstein} (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' n,cubicThetaLocalDualTerm r rev k W σ X n)=
      ∑' x : CubicThetaCommonIndex,
        cubicThetaLocalDualTerm r rev k W σ X (cubicThetaCommonArgument x) := by
  apply (cubicThetaCommonArgument_injective.tsum_eq ?_).symm
  intro n hn
  have ha : cubicThetaCommonCuspCoefficient n.val≠0 := by
    intro h
    exact hn (by simp [cubicThetaLocalDualTerm,h])
  obtain ⟨x,hx⟩ := (cubicThetaCommonNumerator_range n.val).mpr
    (cubicThetaCommonCuspCoefficient_support n.property ha)
  exact ⟨x,Subtype.ext hx⟩

lemma cubicThetaCoreCoefficient_index (r : Eisenstein) (x : CubicThetaCoreIndex r) :
    cubicThetaCoreCoefficient r (cubicThetaCommonArgument x.val)=
      cubicThetaCommonTau (cubicThetaCommonNumerator x.val) := by
  unfold cubicThetaCoreCoefficient
  apply ite_eq_left
  exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩

lemma cubicThetaFreeCubeJoin_argument (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x)=
      cubicThetaDualCube (x.2.val:Eisenstein) x.2.val.property
        (cubicThetaCommonArgument x.1.val) := by
  apply Subtype.ext
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3
  unfold cubicThetaCommonNumerator cubicThetaFreeCubeJoin
  ring

lemma cubicThetaFreeLocalDualTerm_eq {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaLocalDualTerm r rev k W σ X
      (cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x))=
        cubicThetaFreeLocalDualTerm r rev k W σ X x := by
  rw [cubicThetaFreeCubeJoin_argument,cubicThetaLocalDualTerm_cube hr x.2.val.property x.2.property]
  unfold cubicThetaFreeLocalDualTerm
  rw [cubicThetaCoreCoefficient_index]
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  rw [he]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreArguments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported core indices and free primary factors give exactly the
nonzero domain of the full dual sum, with all zero extensions retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaCoreArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreArgument (r:=r)) := by
  intro x y he
  exact Subtype.ext (cubicThetaCommonArgument_injective he)

lemma cubicThetaCoreArgument_range (r : Eisenstein) (n : MetaplecticDualArgument) :
    n∈Set.range (cubicThetaCoreArgument (r:=r)) ↔ CubicThetaCoreSupport r n := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩
  · rintro ⟨R,k,hk⟩
    let x : CubicThetaCoreIndex r := ⟨(R.unit,R.order,
      ⟨(R.squarefreePart,R.cubePart),R.squarefree_primary,R.cube_primary,R.squarefree⟩),k,hk⟩
    exact ⟨x,Subtype.ext R.numerator_eq.symm⟩

lemma cubicThetaCoreFreeArgument_injective (r : Eisenstein) :
    Function.Injective (cubicThetaCoreFreeArgument r) := by
  intro x y he
  exact Prod.ext (cubicThetaCoreArgument_injective r (congrArg Prod.fst he))
    (Subtype.ext (congrArg Prod.snd he))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualFrequency
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion from the common theta lattice to the dual lattice.
The fixed dilation by 729 is retained in the transform argument. -/
noncomputable section
namespace CubicFirstMoment

lemma complexAngular_mul (ℓ : ℤ) (z w : ℂ) :
    complexAngular ℓ (z*w)=complexAngular ℓ z*complexAngular ℓ w := by
  simp only [complexAngular,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma cubicThetaCircleOrder_neg (rev : Bool) (k : ℕ) :
    cubicThetaCircleOrder rev k = -cubicThetaCircleOrder (!rev) k := by
  cases rev <;> simp [cubicThetaCircleOrder]

lemma cubicTheta_dual_phase (ℓ : ℤ) (n : MetaplecticDualArgument) (d : Eisenstein) :
    theta ℓ (n.val*d^3)=theta ℓ lambdaE*
      complexAngular ℓ ((d:ℂ)^3*metaplecticFrequency n) := by
  have he : ((n.val*d^3:Eisenstein):ℂ)=
      (lambdaE:ℂ)*((d:ℂ)^3*metaplecticFrequency n) := by
    simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,metaplecticFrequency]
    change (n.val:ℂ)*(d:ℂ)^3=traceLambda*((d:ℂ)^3*((n.val:ℂ)/traceLambda))
    field_simp [traceLambda_ne_zero]
  rw [←complexAngular_coe,he,complexAngular_mul,complexAngular_coe]

lemma cubicTheta_dual_norm (n : MetaplecticDualArgument) :
    ‖cubicThetaFrequency n.val‖^2=Complex.normSq (metaplecticFrequency n)/27 := by
  rw [cubicThetaFrequency_sq,cubicTheta_metaplectic_normSq]
  ring

lemma cubicTheta_dual_cube_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (d : Eisenstein) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2*norm d^3=
      (2*Real.pi)^4*Complex.normSq ((d:ℂ)^3*metaplecticFrequency n)*(X/729)/norm r^2 := by
  rw [cubicThetaVoronoi_dual_argument hr,Complex.normSq_mul,map_pow]
  change (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2)*norm d^3=
    (2*Real.pi)^4*(norm d^3*Complex.normSq (metaplecticFrequency n))*(X/729)/norm r^2
  ring

lemma cubicThetaFreeLocalDualTerm_frequency {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaFreeLocalDualTerm r rev k W σ X x=
      27*theta (cubicThetaCircleOrder rev k) lambdaE*
        metaplecticDualTerm cubicThetaCoreCoefficient r (cubicThetaCircleOrder (!rev) k)
          W σ (X/729) (cubicThetaCoreFreeArgument r x) := by
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  unfold cubicThetaFreeLocalDualTerm
  rw [he,show cubicThetaCommonNumerator x.1.val=(cubicThetaCoreArgument x.1).val from rfl]
  change theta _ ((cubicThetaCoreArgument x.1).val*(x.2.val:Eisenstein)^3)*
    (cubicThetaCoreCoefficient r (cubicThetaCoreArgument x.1)*
      metaplecticLocalCoefficient r (cubicThetaCoreArgument x.1))/_*_= _
  rw [cubicTheta_dual_phase,
    cubicTheta_dual_cube_argument hr (cubicThetaCoreArgument x.1) (x.2.val:Eisenstein),
    cubicTheta_dual_norm (cubicThetaCoreArgument x.1)]
  dsimp only [metaplecticDualTerm,cubicThetaCoreFreeArgument]
  rw [ite_eq_left x.2.property]
  simp only [←cubicThetaCircleOrder_neg rev k,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full dual sum of the concrete core coefficient, with summability
transferred from the proved arithmetic free-cube parametrization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaDualTerm_support (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Function.support (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) ⊆
      Set.range (cubicThetaCoreFreeArgument r) := by
  intro nd hnd
  have hd : IsCoprime (nd.2:Eisenstein) r := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_right h])
  have hn : CubicThetaCoreSupport r nd.1 := by
    by_contra h
    exact hnd (by simp only [metaplecticDualTerm,ite_eq_left hd,
      cubicThetaCoreCoefficient,ite_eq_right h,zero_mul,zero_div])
  obtain ⟨x,hx⟩ := (cubicThetaCoreArgument_range r nd.1).mpr hn
  exact ⟨(x,⟨nd.2,hd⟩),Prod.ext hx rfl⟩

lemma cubicThetaDualTerm_tsum (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' x : CubicThetaCoreIndex r × CubicThetaFreeArgument r,
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x))=
    ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X nd :=
  (cubicThetaCoreFreeArgument_injective r).tsum_eq (cubicThetaDualTerm_support r ℓ W σ X)

lemma cubicThetaDualTerm_summable_iff (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    Summable (fun x : CubicThetaCoreIndex r × CubicThetaFreeArgument r =>
      metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X (cubicThetaCoreFreeArgument r x)) ↔
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) :=
  (cubicThetaCoreFreeArgument_injective r).summable_iff
    (f:=metaplecticDualTerm cubicThetaCoreCoefficient r ℓ W σ X) (by
    intro nd hn
    by_contra hne
    exact hn (cubicThetaDualTerm_support r ℓ W σ X hne))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualPhase
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact angular phase of the constructed dual formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_theta_lambda (ℓ : ℤ) : theta ℓ lambdaE=Complex.I^ℓ := by
  have hnorm : ‖traceLambda‖=Real.sqrt 3 := by
    rw [traceLambda_eq,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold theta
  rw [lambdaE_coe,hnorm,traceLambda_eq]
  congr 1
  exact mul_div_cancel_left₀ Complex.I (Complex.ofReal_ne_zero.mpr (by positivity))

lemma cubicTheta_root_ratio {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    cubicThetaLevelAngularRoot r rev k=
      (-(star (r:ℂ)/(r:ℂ)))^(cubicThetaCircleOrder (!rev) k) := by
  have hz : (r:ℂ)≠0 := fun h => primary_ne_zero hr (Subtype.ext h)
  have hn : (norm r:ℂ)=(r:ℂ)*star (r:ℂ) := by
    simpa only [norm,Complex.star_def,Complex.normSq_eq_norm_sq,Complex.ofReal_pow] using (Complex.mul_conj' (r:ℂ)).symm
  have he : -(norm r:ℂ)/(r:ℂ)^2=-(star (r:ℂ)/(r:ℂ)) := by
    rw [hn]
    field_simp
  rw [cubicThetaLevelAngularRoot,he]
  cases rev
  · simp only [Bool.not_false,cubicThetaCircleMultiplier,ite_true, if_true,cubicThetaCircleOrder,
      star_neg,zpow_neg,zpow_natCast]
    rw [←inv_pow,inv_neg,inv_div]
    simp only [Complex.star_def,map_div₀,starRingEnd_self_apply]
  · simp only [Bool.not_true,cubicThetaCircleMultiplier,Bool.false_eq_true,ite_false, if_false,
      cubicThetaCircleOrder,zpow_natCast]

lemma cubicTheta_root_phase {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    (cubicThetaLevelAngularRoot r rev k)⁻¹*
      theta (cubicThetaCircleOrder rev k) lambdaE=
    theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
  let ℓ := cubicThetaCircleOrder (!rev) k
  let q := star (r:ℂ)/(r:ℂ)
  have hq : q≠0 := div_ne_zero (star_ne_zero.mpr (by
    intro h
    exact primary_ne_zero hr (Subtype.ext h))) (by
      intro h
      exact primary_ne_zero hr (Subtype.ext h))
  have hI : -q*Complex.I=Complex.I⁻¹*q := by rw [Complex.inv_I]; ring
  have he : (-q)^ℓ*Complex.I^ℓ=Complex.I^(-ℓ)*q^ℓ := by
    rw [←mul_zpow,hI,mul_zpow,inv_zpow,←zpow_neg]
  rw [cubicTheta_root_ratio hr,cubicThetaCircleOrder_neg rev k,
    cubicTheta_theta_lambda,cubicTheta_theta_lambda]
  change ((-q)^ℓ)⁻¹*Complex.I^(-ℓ)=Complex.I^ℓ*q^(-ℓ)
  apply mul_right_cancel₀ (zpow_ne_zero ℓ hq)
  calc
    _ = ((-q)^ℓ)⁻¹*(Complex.I^(-ℓ)*q^ℓ) := by ring
    _ = ((-q)^ℓ)⁻¹*((-q)^ℓ*Complex.I^ℓ) := by rw [he]
    _ = Complex.I^ℓ := by
      rw [←mul_assoc,inv_mul_cancel₀ (zpow_ne_zero _ (neg_ne_zero.mpr hq)),one_mul]
    _ = _ := by rw [mul_assoc,zpow_neg,inv_mul_cancel₀ (zpow_ne_zero _ hq),mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualScalar
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical and Gauss factors in the constructed transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaDualPrefactor_eq {r : Eisenstein} (hr : primary r) :
    cubicThetaDualPrefactor r=(norm r:ℂ)/((2*Real.pi:ℝ):ℂ)^2 := by
  have hsq := cubicThetaLevelScale_square r
  have hR : (norm r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hr)).ne'
  unfold cubicThetaDualPrefactor
  rw [show (-2:ℂ)=((-2:ℤ):ℂ) by norm_num,Complex.cpow_intCast,
    Complex.cpow_intCast]
  simp only [zpow_neg,zpow_ofNat,←Complex.ofReal_pow,hsq,Complex.ofReal_inv,inv_inv]
  rw [div_eq_mul_inv]

lemma cubicThetaGauss_square {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    ((Real.sqrt (norm r):ℂ)*gauss r)*star ((Real.sqrt (norm r):ℂ)*gauss r)=(norm r:ℂ) := by
  rw [mul_assoc,gauss_mul_conj_unnormalized hr hs,←Complex.ofReal_mul]
  congr 1
  nlinarith [Real.sq_sqrt (norm_nonneg r)]

lemma cubicThetaDual_scalar {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (rev : Bool) (k : ℕ) :
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*(81*metaplecticRawPrefactor r (cubicThetaCircleOrder (!rev) k))=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have hphase := cubicTheta_root_phase hr rev k
  have hrearrange : (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE)=
    (theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k))*(27*cubicThetaDualPrefactor r) := by
    rw [←hphase]
    ring
  rw [hrearrange,cubicThetaDualPrefactor_eq hr]
  unfold metaplecticRawPrefactor
  calc
    _ = ((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (81*(norm r:ℂ))/((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
      rw [←cubicThetaGauss_square hr hs]
      ring
    _ = _ := by
      rw [hthree]
      push_cast
      field_simp
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialDual
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial dual sum uses the same proved local support and free-cube
reindexing as the angular formula. Its separate actual pole is retained. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem cubicThetaFullDual_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      metaplecticRawCompleted r 0 W X=
      (cubicThetaDualPrefactor r*27)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
  obtain ⟨hS,hE⟩ := cubicThetaResidue_radial_voronoi hr hs W hW hpos hsm hσ hX
  rw [cubicThetaResidueDualTerm_local hr hs] at hS hE
  have hI := hS.comp_injective cubicThetaCommonArgument_injective
  have hJ := hI.comp_injective (cubicThetaFreeCubeJoin_injective (primary_ne_zero hr))
  have he := cubicThetaFreeLocalDualTerm_eq hr false 0 W σ X
  have hfree := hJ.congr he
  rw [cubicThetaLocalDualTerm_reindex,cubicTheta_free_cube_tsum (primary_ne_zero hr)] at hE
  simp only [he] at hE
  have hf (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
      cubicThetaFreeLocalDualTerm r false 0 W σ X x=
        27*metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)
          (cubicThetaCoreFreeArgument r x) := by
    simpa only [cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true, if_true,ite_false, if_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one] using
      cubicThetaFreeLocalDualTerm_frequency hr false 0 W σ X x
  have hprod := hfree.congr hf
  have hsmall := (summable_mul_left_iff (by norm_num : (27:ℂ)≠0)).mp hprod
  refine ⟨(cubicThetaDualTerm_summable_iff r 0 W σ (X/729)).mp hsmall,?_⟩
  simp only [hf,tsum_mul_left,cubicThetaDualTerm_tsum,mul_assoc] at hE
  simpa only [mul_assoc] using hE

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRawVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial raw/completed Voronoi identities. The main term remains
in terms of the computed residue, without asserting its normalization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialGauss_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r≠0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gauss_of_squarefree hr hs]
  norm_num

lemma cubicThetaRadialRawScalar_ne_zero {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))≠0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (norm_pos_of_ne_zero (primary_ne_zero hr))).ne') (cubicThetaRadialGauss_ne_zero hr hs)

theorem cubicTheta_raw_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729)) ∧
    metaplecticRawCompleted r 0 W X=
      81*metaplecticRawPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualRawRadialMain r W X := by
  obtain ⟨hS,hE⟩ := cubicThetaFullDual_radial_voronoi hr hs W hW hpos hsm hσ hX
  refine ⟨hS,?_⟩
  let A := ((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r)
  have hA : A≠0 := cubicThetaRadialRawScalar_ne_zero hr hs
  have hscalar : A*(81*metaplecticRawPrefactor r 0)=cubicThetaDualPrefactor r*27 := by
    simpa only [A,cubicThetaCircleOrder,Bool.not_false,Bool.false_eq_true,ite_true, if_true,ite_false, if_false,
      Nat.cast_zero,neg_zero,theta_zero,mul_one,cubicThetaLevelAngularRoot,pow_zero,
      inv_one,one_mul] using cubicThetaDual_scalar hr hs false 0
  have hp : A*cubicThetaActualRawRadialMain r W X=
      cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
    change A*(cubicThetaResidueRadialPole r/A*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ))=_
    field_simp
  apply mul_left_cancel₀ hA
  rw [mul_add,←mul_assoc,hscalar,hp]
  exact hE

lemma cubicTheta_radial_main_completed {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (X : ℝ) :
    gauss r*cubicThetaActualRawRadialMain r W X=cubicThetaActualCompletedRadialMain r W X := by
  have hg := cubicThetaRadialGauss_ne_zero hr hs
  have hthree : ((3^(5/2:ℝ):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hsqrt : (Real.sqrt (norm r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
  unfold cubicThetaActualRawRadialMain cubicThetaActualCompletedRadialMain
  field_simp

theorem cubicTheta_completed_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    metaplecticCompleted r 0 W X=
      81*metaplecticPrefactor r 0*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd+
      cubicThetaActualCompletedRadialMain r W X := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  rw [metaplecticCompleted_eq_raw hr,(cubicTheta_raw_radial_voronoi hr hs W hW hpos hsm hσ hX).2,
    theta_zero,mul_one,mul_add,cubicTheta_radial_main_completed hr hs]
  congr 1
  calc
    _ = 81*(gauss r*theta 0 r*metaplecticRawPrefactor r 0)*
        ∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0 W σ (X/729) nd := by rw [theta_zero]; ring
    _ = _ := by rw [metaplecticPrefactor_normalization hr hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMainConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact comparison of the constructed radial residue with the printed
main-term constant. The remaining arithmetic normalization is explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRadial_uncompletion_pole {r : Eisenstein} (hr : primary r) :
    cubicThetaAngularUncompletion r 0 (5/6)=
      ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ) := by
  unfold cubicThetaAngularUncompletion
  norm_num only [Nat.cast_zero,zero_div,add_zero,
    show 2*(5/6:ℂ)-1=2/3 by norm_num,
    show 2*(5/6:ℂ)=5/3 by norm_num,
    show (5/6:ℂ)+1/6=1 by norm_num,
    show (5/6:ℂ)-1/6=2/3 by norm_num,
    Complex.Gamma_one,inv_one,mul_one]
  rw [show (2/3:ℂ)=((2/3:ℝ):ℂ) by norm_num,
    show (5/3:ℂ)=((5/3:ℝ):ℂ) by norm_num,
    ←Complex.ofReal_cpow (cubicThetaLevelScale_pos hr).le,
    ←Complex.ofReal_cpow (by positivity : (0:ℝ)≤2*Real.pi),Complex.Gamma_ofReal]
  push_cast
  ring

lemma cubicThetaRadial_level_pole_power {r : Eisenstein} (hr : primary r) :
    cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r)=
      norm r^(-7/6:ℝ) := by
  have hN := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hS := Real.sqrt_pos.mpr hN
  rw [←Real.rpow_add (cubicThetaLevelScale_pos hr)]
  norm_num only [show (2/3:ℝ)+2/3=4/3 by norm_num]
  unfold cubicThetaLevelScale
  rw [Real.inv_rpow hS.le,div_eq_mul_inv,←Real.rpow_neg hS.le,
    ←Real.rpow_neg_one,←Real.rpow_add hS,
    Real.sqrt_eq_rpow,←Real.rpow_mul hN.le]
  congr 1
  norm_num

lemma cubicThetaSeriesConstant_mul_base :
    star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar=(cubicThetaConstant:ℂ) := by
  rw [←star_mul,cubicThetaSeriesConstant,mul_div_cancel₀ _ cubicThetaArithmeticBaseScalar_ne_zero]
  exact Complex.conj_ofReal _

lemma cubicThetaRadial_scale_pole {X : ℝ} (hX : 0<X) :
    (X/27)^(5/6:ℝ)=X^(5/6:ℝ)/(3:ℝ)^(5/2:ℝ) := by
  rw [Real.div_rpow hX.le (by norm_num)]
  congr 1
  calc
    (27:ℝ)^(5/6:ℝ)=((3:ℝ)^(3:ℝ))^(5/6:ℝ) := by norm_num
    _ = (3:ℝ)^((3:ℝ)*(5/6)) := (Real.rpow_mul (by norm_num) _ _).symm
    _ = _ := by norm_num

lemma cubicThetaRadial_real_main {r : Eisenstein} (hr : primary r) {X : ℝ} (hX : 0<X) :
    (4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))/2*
      (metaplecticTotient r*(cubicThetaConstant/3))*cubicThetaLevelScale r^(2/3:ℝ)/
      ((3:ℝ)^(5/2:ℝ)*Real.sqrt (norm r))*(X/27)^(5/6:ℝ)=
      metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have h35 : (3:ℝ)^(5/2:ℝ)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hG : Real.Gamma (2/3:ℝ)≠0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  calc
    _ = (2*cubicThetaConstant/(3*(3:ℝ)^(5/2:ℝ)))*
        (cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r))*
        ((2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))*metaplecticTotient r*(X/27)^(5/6:ℝ) := by ring
    _ = _ := by
      rw [cubicThetaRadial_level_pole_power hr,cubicThetaRadial_scale_pole hX]
      unfold cubicThetaConstant metaplecticA0
      rw [hthree]
      field_simp

/-- This comparison isolates the exact outstanding normalization: the
constructed main term times the conjugate base scalar is the printed one. -/
theorem cubicThetaActualCompletedRadialMain_mul_base {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X*star cubicThetaArithmeticBaseScalar=
      metaplecticMain r 0 W X := by
  rw [cubicThetaActualCompletedRadialMain,cubicThetaResidueRadialPole,
    cubicThetaRadial_uncompletion_pole hr]
  have hX27 : 0≤X/27 := (div_pos hX (by norm_num)).le
  rw [show (5/6:ℂ)=((5/6:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hX27]
  calc
    _ = ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ)/2*
        ((Nat.card (Residues r)ˣ:ℂ)*((star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar)/3))*
        ((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ)/
        (((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm r):ℂ))*
        (((X/27)^(5/6:ℝ):ℝ):ℂ)*mellin W (5/6) := by
      push_cast
      ring
    _ = _ := by
      rw [cubicThetaSeriesConstant_mul_base]
      have he := congrArg (fun q : ℝ => (q:ℂ)*mellin W (5/6)) (cubicThetaRadial_real_main hr hX)
      simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
        metaplecticMain,ite_true, if_true,metaplecticTotient,Complex.ofReal_natCast,mul_assoc] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the critical line the angular Gamma quotient has modulus one.
Thus the actual translated Mellin kernel has one common integrable
weight, independent of height and of the retained frequency polynomial. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma continuous_metaplecticGamma_half (ℓ : ℤ) :
    Continuous (fun t : ℝ => metaplecticGammaQuotient ℓ ((1/2:ℂ)+(t:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hopen : IsOpen {s : ℂ | s.re < 5/6} := isOpen_lt Complex.continuous_re continuous_const
  have hmem : (1/2:ℂ)+(t:ℂ)*Complex.I ∈ {s : ℂ | s.re < 5/6} := by
    change ((1/2:ℂ)+(t:ℂ)*Complex.I).re < 5/6
    norm_num
  have hg : ContinuousAt (fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) t := by fun_prop
  exact ((differentiableOn_metaplecticGammaQuotient ℓ).differentiableAt
    (hopen.mem_nhds hmem)).continuousAt.comp
    (f := fun u : ℝ => (1/2:ℂ)+(u:ℂ)*Complex.I) hg

lemma norm_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ) (c : ℝ)
    (P : ℝ → ℂ) (τ t : ℝ) :
    ‖metaplecticCriticalKernel ℓ W c P τ t‖ =
      ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*‖P (τ-t)‖ := by
  simp only [metaplecticCriticalKernel,norm_mul,norm_metaplecticGamma_half,
    mellinPhase_norm,mul_one]

lemma continuous_metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2) := by
  have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
  have hg := (continuous_metaplecticGamma_half ℓ).comp
    (continuous_fst.sub continuous_snd)
  have hp : Continuous (fun z : ℝ × ℝ => mellinPhase (z.1-z.2) c) := by
    unfold mellinPhase
    fun_prop
  exact (((hm.comp (by fun_prop)).mul hg).mul hp).mul
    (hP.comp (continuous_fst.sub continuous_snd))

lemma metaplectic_mellin_half_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    Integrable (fun τ : ℝ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)) := by
  convert ((mellinVerticalSchwartz W hW hpos hsm (1/2)).integrable (μ := volume)) using 1
  all_goals try with_reducible_and_instances rfl
  ext τ
  rw [mellinVerticalSchwartz_apply]
  norm_num

lemma metaplecticCriticalKernel_integrable (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P)
    {B : ℝ} (hB : ∀ u, ‖P u‖ ≤ B) (t : ℝ) :
    Integrable (fun τ : ℝ => metaplecticCriticalKernel ℓ W c P τ t) := by
  have hx : Continuous (fun τ : ℝ => (τ,t)) := continuous_id.prodMk continuous_const
  have hc := Continuous.comp
    (f := fun τ : ℝ => (τ,t))
    (g := fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2)
    (continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP) hx
  apply ((metaplectic_mellin_half_integrable W hW hpos hsm).norm.mul_const B).mono'
    hc.aestronglyMeasurable
  filter_upwards with τ
  dsimp only [Function.comp_def]
  rw [norm_metaplecticCriticalKernel]
  exact mul_le_mul_of_nonneg_left (hB (τ-t)) (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalTransform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Move each finite retained transform to the critical line before
summing. The Mellin weight is translated back to one fixed function. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_critical (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A v =
      (Real.sqrt v:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
  have hc := metaplectic_transform_contour ℓ (fun x => W x*mellinPhase t x)
    (phaseWeight_compact hW t) (phaseWeight_positive hpos t)
    (phaseWeight_smooth hpos hsm t) (a := -A) (b := 1/2)
    (by linarith) le_rfl hv hm hp
  let F : ℝ → ℂ := fun τ =>
    (v:ℂ)^((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)
  have he (τ : ℝ) :
      (v:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        mellin (fun x => W x*mellinPhase t x) ((1/2:ℂ)+(τ:ℂ)*Complex.I) = F (τ+t) := by
    rw [mellin_mul_phase]
    dsimp [F]
    have h1 : ((τ+t-t:ℝ):ℂ) = (τ:ℂ) := by push_cast; ring
    have h2 : (1/2:ℂ)+(τ:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        (1/2:ℂ)+((τ+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [h1,h2]
  have hf (τ : ℝ) : F τ = (Real.sqrt v:ℂ)*
      metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
    dsimp [F,metaplecticCriticalKernel]
    rw [hecke_scale_phase hv]
    ring
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hc
  unfold metaplecticTransform
  rw [hc]
  simp_rw [he]
  rw [integral_add_right_eq_self F t]
  simp_rw [hf]
  rw [integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact extraction of the common critical-line kernel from a finite
retained frequency sum. No common-majorant hypothesis is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem metaplectic_finite_transform_critical {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (q : ι → ℝ) (hq : ∀ i ∈ S, 0 < q i)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    (∑ i ∈ S, b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i)) =
      (Real.sqrt c:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c
          (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
  let F : ι → ℝ → ℂ := fun i τ => b i*(Real.sqrt (c*q i):ℂ)*
    metaplecticCriticalKernel ℓ W (c*q i) (fun _ => 1) τ t
  have hF (i : ι) (_hi : i ∈ S) : Integrable (F i) := by
    exact (metaplecticCriticalKernel_integrable ℓ W hW hpos hsm (c*q i)
      (P := fun _ => 1) continuous_const (B := 1) (by intro u; norm_num) t).const_mul _
  have ht (i : ι) (hi : i ∈ S) :
      b i*metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A (c*q i) =
        ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ := by
    rw [metaplecticTransform_critical ℓ W hW hpos hsm hA (mul_pos hc (hq i hi)) hm hp t]
    dsimp [F]
    rw [integral_const_mul]
    ring
  have hf (τ : ℝ) : (∑ i ∈ S, F i τ) =
      (Real.sqrt c:ℂ)*metaplecticCriticalKernel ℓ W c
        (fun u => ∑ i ∈ S, b i*(Real.sqrt (q i):ℂ)*mellinPhase u (q i)) τ t := by
    unfold metaplecticCriticalKernel
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F,metaplecticCriticalKernel]
    rw [Real.sqrt_mul hc.le,Complex.ofReal_mul,
      mellinPhase_mul_pos (τ-t) hc (hq i hi)]
    ring
  calc
    _ = ∑ i ∈ S, ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, F i τ :=
      Finset.sum_congr rfl ht
    _ = ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ, ∑ i ∈ S, F i τ := by
      rw [integral_finsetSum S hF,Finset.mul_sum]
    _ = _ := by simp_rw [hf]; rw [integral_const_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained Voronoi sum is an actual finite frequency polynomial.
Its cutoff is independent of the height parameter. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_frequency_norm_numerator (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n) = norm n.val/3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [traceLambda_eq,Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  rfl

lemma metaplecticDualNorm_coordinate_bound (nd : MetaplecticDualArgument × PrimaryArgument)
    {J : ℝ} (hcut : metaplecticDualNorm nd ≤ J) :
    norm nd.1.val ≤ 3*J ∧ norm nd.2.val ≤ 3*J := by
  have hN : 1 ≤ norm nd.1.val := one_le_norm nd.1.property
  have hD : 1 ≤ norm nd.2.val := one_le_norm (primary_ne_zero nd.2.property)
  have hD0 : 0 ≤ norm nd.2.val := norm_nonneg _
  have hN0 : 0 ≤ norm nd.1.val := norm_nonneg _
  have hraw : norm nd.2.val^3*norm nd.1.val ≤ 3*J := by
    unfold metaplecticDualNorm at hcut
    rw [metaplectic_frequency_norm_numerator] at hcut
    nlinarith
  have hD3 : 1 ≤ norm nd.2.val^3 := one_le_pow₀ hD
  have hn : norm nd.1.val ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD3 hN0
  have hd3 : norm nd.2.val^3 ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (pow_nonneg hD0 3)
  have hd : norm nd.2.val ≤ norm nd.2.val^3 := by
    have hsq : 1 ≤ norm nd.2.val^2 := one_le_pow₀ hD
    have hh := mul_le_mul_of_nonneg_left hsq hD0
    nlinarith
  exact ⟨hn.trans hraw,(hd.trans hd3).trans hraw⟩

lemma mem_metaplecticDualBall (nd : MetaplecticDualArgument × PrimaryArgument) (J : ℝ) :
    nd ∈ metaplecticDualBall J ↔ metaplecticDualNorm nd ≤ J := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hn,hd⟩ := metaplecticDualNorm_coordinate_bound nd h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,h⟩
    · exact Finset.mem_subtype.mpr (mem_nonzeroNormBall.mpr ⟨hn,nd.1.property⟩)
    · exact Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨nd.2.property,hd⟩)

lemma metaplecticRetainedTerm_finite (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ) :
    (∑' nd, metaplecticRetainedTerm a r ℓ W A X J nd) =
      ∑ nd ∈ metaplecticDualBall J, metaplecticDualTerm a r ℓ W A X nd := by
  rw [tsum_eq_sum (s := metaplecticDualBall J) (fun nd hnd => ?_)]
  · apply Finset.sum_congr rfl
    intro nd hnd
    simp only [metaplecticRetainedTerm,(mem_metaplecticDualBall nd J).mp hnd,ite_true, if_true]
  · have hn : ¬metaplecticDualNorm nd ≤ J := fun h => hnd ((mem_metaplecticDualBall nd J).mpr h)
    simp only [metaplecticRetainedTerm,hn,ite_false, if_false]

/-- Exact retained/tail split of the actual absolutely convergent dual
series. The retained part is the displayed finite sum. -/
theorem metaplecticDualTerm_split (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (hs : Summable (metaplecticDualTerm a r ℓ W A X)) :
    (∑' nd, metaplecticDualTerm a r ℓ W A X nd) =
      (∑ nd ∈ metaplecticDualBall J, metaplecticDualTerm a r ℓ W A X nd)+
        ∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd := by
  have hr : Summable (metaplecticRetainedTerm a r ℓ W A X J) := by
    apply (hasSum_sum_of_ne_finset_zero (s := metaplecticDualBall J) ?_).summable
    intro nd hnd
    have hn : ¬metaplecticDualNorm nd ≤ J := fun h => hnd ((mem_metaplecticDualBall nd J).mpr h)
    simp only [metaplecticRetainedTerm,hn,ite_false, if_false]
  have hf : Summable (metaplecticFarTailTerm a r ℓ W A X J) := by
    convert hs.sub hr using 1
    all_goals try with_reducible_and_instances rfl
    funext nd
    by_cases h : metaplecticDualNorm nd ≤ J
    · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,not_lt_of_ge h,ite_true, if_true,ite_false, if_false,sub_self]
    · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,lt_of_not_ge h,ite_true, if_true,ite_false, if_false,sub_zero]
  calc
    _ = ∑' nd, (metaplecticRetainedTerm a r ℓ W A X J nd+
        metaplecticFarTailTerm a r ℓ W A X J nd) := by
      apply tsum_congr
      intro nd
      by_cases h : metaplecticDualNorm nd ≤ J
      · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,not_lt_of_ge h,ite_true, if_true,ite_false, if_false,add_zero]
      · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,lt_of_not_ge h,ite_true, if_true,ite_false, if_false,zero_add]
    _ = _ := by rw [hr.tsum_add hf,metaplecticRetainedTerm_finite]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedCritical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite retained Voronoi sum on the critical line, with
its coefficients normalized for ordinary free-variable mean value. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_sqrt_quotient {D N : ℝ} (hD : 0 < D) (hN : 0 < N) :
    Real.sqrt (D^3*N)/(N*D^(5/2:ℝ)) = 1/(Real.sqrt N*D) := by
  have hsD : Real.sqrt (D^3) = D*Real.sqrt D := by
    rw [show D^3 = D^2*D by ring,Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq_eq_abs,
      abs_of_pos hD]
  have hpD : D^(5/2:ℝ) = D^2*Real.sqrt D := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_add hD]
    congr 1
    norm_num
  have he : Real.sqrt (D^3*N)*(Real.sqrt N*D) = N*D^(5/2:ℝ) := by
    rw [Real.sqrt_mul (by positivity),hsD,hpD]
    calc
      _ = D^2*Real.sqrt D*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]; ring
  apply (div_eq_div_iff (mul_ne_zero hN.ne' (Real.rpow_pos_of_pos hD _).ne')
    (mul_ne_zero (Real.sqrt_pos.mpr hN).ne' hD.ne')).mpr
  simpa only [one_mul] using he

lemma metaplecticRawDualCoefficient_normalize
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticRawDualCoefficient a r ℓ nd*(Real.sqrt (metaplecticDualNorm nd):ℂ) =
      metaplecticNormalizedDualCoefficient a r ℓ nd := by
  have hD := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hN := Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  have he := metaplectic_sqrt_quotient hD hN
  unfold metaplecticDualNorm
  have hec : ((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ) =
      1/((Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2:ℝ):ℂ) := by
    exact_mod_cast he
  unfold metaplecticRawDualCoefficient metaplecticNormalizedDualCoefficient
  split_ifs
  · calc
      _ = (a r nd.1*metaplecticLocalCoefficient r nd.1)*
          complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)*
          (((Real.sqrt (norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)):ℝ):ℂ)/
            ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)) := by ring
      _ = _ := by rw [hec]; ring
  · simp only [zero_mul]

lemma metaplecticDualTerm_factor
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (A X : ℝ) (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticDualTerm a r ℓ W A X nd =
      metaplecticRawDualCoefficient a r ℓ nd *
        metaplecticTransform ℓ W A
          (((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd) := by
  unfold metaplecticDualTerm metaplecticRawDualCoefficient
  rw [metaplecticDualNorm_eq]
  have he : (2*Real.pi)^4*metaplecticDualNorm nd*X/norm r^2 =
      ((2*Real.pi)^4*X/norm r^2)*metaplecticDualNorm nd := by ring
  rw [he]
  split_ifs <;> ring

/-- The cutoff is arbitrary and independent of height. This is an exact
identity for the original retained Voronoi terms. -/
theorem metaplectic_retained_critical
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) (J t : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    (∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) =
      (Real.sqrt ((2*Real.pi)^4*X/norm r^2):ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W ((2*Real.pi)^4*X/norm r^2)
          (fun u => ∑ nd ∈ metaplecticDualBall J,
            metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)) τ t := by
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hc : 0 < (2*Real.pi)^4*X/norm r^2 := by positivity
  simp_rw [metaplecticDualTerm_factor]
  rw [metaplectic_finite_transform_critical _ _ _
    (fun nd _ => metaplecticDualNorm_pos nd) ℓ W hW hpos hsm hA hc hm hp t]
  simp_rw [metaplecticRawDualCoefficient_normalize]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite retained transform. The common
critical-line majorant proves it without a uniform-series assumption. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_metaplectic_kernel_integral (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P)
    {B : ℝ} (hB : ∀ u, ‖P u‖ ≤ B) :
    Continuous (fun t : ℝ => ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ t) := by
  have hc : Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2) :=
    continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP
  have hslice (τ : ℝ) : Continuous (fun t : ℝ => metaplecticCriticalKernel ℓ W c P τ t) := by
    have hx : Continuous (fun t : ℝ => (τ,t)) := continuous_const.prodMk continuous_id
    exact hc.comp (f := fun t : ℝ => (τ,t)) hx
  apply continuous_of_dominated
    (F := fun t τ : ℝ => metaplecticCriticalKernel ℓ W c P τ t) (μ := volume)
    (bound := fun τ : ℝ => ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*B)
  · intro t
    exact (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun τ => by
      rw [norm_metaplecticCriticalKernel]
      exact mul_le_mul_of_nonneg_left (hB (τ-t)) (_root_.norm_nonneg _))
  · exact (metaplectic_mellin_half_integrable W hW hpos hsm).norm.mul_const B
  · exact Filter.Eventually.of_forall hslice

lemma continuous_metaplectic_retained
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) (J : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    Continuous (fun t : ℝ => ∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) := by
  let P := fun u : ℝ => ∑ nd ∈ metaplecticDualBall J,
    metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hB (u : ℝ) : ‖P u‖ ≤ ∑ nd ∈ metaplecticDualBall J,
      ‖metaplecticNormalizedDualCoefficient a r ℓ nd‖ := by
    calc
      _ ≤ ∑ nd ∈ metaplecticDualBall J,
        ‖metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)‖ :=
          norm_sum_le _ _
      _ = _ := by simp only [norm_mul,mellinPhase_norm,mul_one]
  have hc := continuous_metaplectic_kernel_integral ℓ W hW hpos hsm
    ((2*Real.pi)^4*X/norm r^2) hP hB
  have he (t : ℝ) := metaplectic_retained_critical a hr ℓ W hW hpos hsm hA hX J t hm hp
  simp_rw [he]
  exact continuous_const.mul hc

lemma continuous_metaplectic_height_completed (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0 < X) :
    Continuous (metaplecticHeightCompleted r ℓ W X) := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  have hcut : ∀ x : ℝ, B < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hB x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self x]
  have he (t : ℝ) := metaplecticHeightCompleted_finite r ℓ W hX
    (le_refl (B*X)) hcut t
  change Continuous (fun t : ℝ => metaplecticHeightCompleted r ℓ W X t)
  simp_rw [he]
  apply continuous_finsetSum
  intro du hdu
  apply continuous_const.mul
  unfold mellinPhase
  fun_prop

lemma continuous_metaplectic_height_main (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (X : ℝ) :
    Continuous (fun t : ℝ => mellinPhase t X*
      metaplecticMain r ℓ (fun x => W x*mellinPhase t x) X) := by
  have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
  have hp : Continuous (fun t : ℝ => mellinPhase t X) := by
    unfold mellinPhase
    fun_prop
  by_cases hℓ : ℓ = 0
  · simp only [metaplecticMain,hℓ,ite_true, if_true,mellin_mul_phase]
    exact hp.mul (continuous_const.mul (hm.comp (by fun_prop)))
  · simp only [metaplecticMain,hℓ,ite_false, if_false,mul_zero]
    exact continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm twists and finite dual-tail reduction for the actual radial
remainder. Its main term is the computed one, not an assumed normalization. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma continuous_cubicThetaRadialHeightMain {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0<X) :
    Continuous (fun t : ℝ => mellinPhase t X*
      cubicThetaActualCompletedRadialMain r (fun x => W x*mellinPhase t x) X) := by
  have hB : star cubicThetaArithmeticBaseScalar≠0 := star_ne_zero.mpr cubicThetaArithmeticBaseScalar_ne_zero
  have he (t : ℝ) : mellinPhase t X*cubicThetaActualCompletedRadialMain r
      (fun x => W x*mellinPhase t x) X=
      (mellinPhase t X*metaplecticMain r 0 (fun x => W x*mellinPhase t x) X)/
        star cubicThetaArithmeticBaseScalar := by
    apply (eq_div_iff hB).mpr
    rw [mul_assoc,cubicThetaActualCompletedRadialMain_mul_base hr _ hX]
  exact ((continuous_metaplectic_height_main r 0 W hW hpos hsm X).div_const _).congr
    (fun t => (he t).symm)

lemma continuous_cubicThetaRadialHeightRemainder {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X : ℝ} (hX : 0<X) :
    Continuous (cubicThetaRadialHeightRemainder r W X) :=
  (continuous_metaplectic_height_completed r 0 W hW hX).sub
    (continuous_cubicThetaRadialHeightMain hr W hW hpos hsm hX)

theorem cubicTheta_radial_height_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W⊆Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X A : ℝ} (hX : 0<X) (hA : 0<A) (t : ℝ) :
    Summable (metaplecticDualTerm cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729)) ∧
    cubicThetaRadialHeightRemainder r W X t=mellinPhase t X*
      (81*metaplecticPrefactor r 0*∑' nd,metaplecticDualTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) nd) := by
  let : Finite (Residues r) := finite_residues (primary_ne_zero hr)
  let : Fintype (Residues r) := Fintype.ofFinite _
  have htW := phaseWeight_compact hW t
  have htP := phaseWeight_positive hpos t
  have htS := phaseWeight_smooth hpos hsm t
  refine ⟨(cubicTheta_raw_radial_voronoi hr hs _ htW htP htS hA hX).1,?_⟩
  rw [cubicThetaRadialHeightRemainder,metaplecticHeightCompleted_twist r 0 W hX t,
    cubicTheta_completed_radial_voronoi hr hs _ htW htP htS hA hX,mul_add,add_sub_cancel_right]

theorem cubicTheta_radial_remainder_tail_mean_oai {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X A J T E : ℝ} (hX : 0<X) (hA : 0<A) (hT : 0<T)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift 0-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift 0+1/6) (-A))
    (htail : ∀ t : ℝ, |t|≤2*T →
      ‖∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤E) :
    (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r W X t‖)/T≤
      81*((∫ t in T..2*T,‖metaplecticPrefactor r 0*
        ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) nd‖)/T+
        ‖metaplecticPrefactor r 0‖*E) := by
  let F := fun t : ℝ => cubicThetaRadialHeightRemainder r W X t
  let P := fun t : ℝ => metaplecticPrefactor r 0*
    ∑ nd ∈ metaplecticDualBall J,metaplecticDualTerm cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729) nd
  have hF : Continuous F := continuous_cubicThetaRadialHeightRemainder hr W hW hpos hsm hX
  have hP : Continuous P := continuous_const.mul
    (continuous_metaplectic_retained cubicThetaCoreCoefficient hr 0 W hW hpos hsm hA.le
      (div_pos hX (by norm_num : (0:ℝ)<729)) J hm hp)
  have hb (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖F t‖≤81*‖P t‖+81*‖metaplecticPrefactor r 0‖*E := by
    have habs : |t|≤2*T := by rw [abs_of_nonneg (hT.le.trans ht.1)]; exact ht.2
    obtain ⟨hS,hE⟩ := cubicTheta_radial_height_voronoi hr hsr W hW hpos hsm hX hA t
    rw [metaplecticDualTerm_split cubicThetaCoreCoefficient r 0
      (fun x => W x*mellinPhase t x) A (X/729) J hS] at hE
    have he : F t=mellinPhase t X*(81*(P t+metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) J nd)) := by
      dsimp only [F,P]
      rw [hE]
      ring
    rw [he,norm_mul,mellinPhase_norm,one_mul,norm_mul,Complex.norm_ofNat]
    have hadd := norm_add_le (P t) (metaplecticPrefactor r 0*
      ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
        (fun x => W x*mellinPhase t x) A (X/729) J nd)
    have hbound := mul_le_mul_of_nonneg_left (htail t habs)
      (_root_.norm_nonneg (metaplecticPrefactor r 0))
    have htailnorm : ‖metaplecticPrefactor r 0*
        ∑' nd,metaplecticFarTailTerm cubicThetaCoreCoefficient r 0
          (fun x => W x*mellinPhase t x) A (X/729) J nd‖≤‖metaplecticPrefactor r 0‖*E := by
      rw [norm_mul]
      exact hbound
    have hh := hadd.trans (add_le_add le_rfl htailnorm)
    nlinarith only [hh]
  have hFi : IntervalIntegrable (fun t => ‖F t‖) volume T (2*T) :=
    hF.norm.intervalIntegrable T (2*T)
  have hPi : IntervalIntegrable (fun t => (81:ℝ)*‖P t‖) volume T (2*T) :=
    (continuous_const.mul hP.norm).intervalIntegrable T (2*T)
  have hCi : IntervalIntegrable (fun _ : ℝ => 81*‖metaplecticPrefactor r 0‖*E) volume T (2*T) :=
    continuous_const.intervalIntegrable T (2*T)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (show T≤2*T by linarith)
    hFi (hPi.add hCi) hb
  apply (div_le_iff₀ hT).mpr
  apply hi.trans_eq
  rw [intervalIntegral.integral_add hPi hCi,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  dsimp only [F,P]
  field_simp [hT.ne']
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean_oai := @OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean_oai
