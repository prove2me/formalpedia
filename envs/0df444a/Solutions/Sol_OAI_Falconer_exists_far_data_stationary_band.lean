-- Prove2me | solution 1 for OAI.Falconer.exists_far_data_stationary_band
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:17:50.566309+00:00
-- url     : https://prove2.me/submissions/e5772acf-43c9-45a4-86c6-9cfb230a8b8c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SchwartzFourierMomentBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CompactStationaryAmplitude
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_fourierDerivativeL1_bound (φ : 𝓢(ℝ,ℂ)) {a b C D : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n) :
    fourierDerivativeL1 φ n ≤ C*(b-a)*D^n/(2*Real.pi)^n := by
  unfold fourierDerivativeL1
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (C*D^n)*(b-a) := compact_derivative_integral_bound φ hab hs n hC
    _ = _ := by ring

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LinearNonstationary
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff RealInnerProductSpace

 theorem compact_fourier_nonstationary {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖𝓕 f ξ‖ ≤ C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hs' : tsupport (φ : ℝ → ℂ) ⊆ Icc a z := by simpa [hφ] using hs
  have hC' : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n := by simpa [hφ] using hC
  have hh := (schwartz_fourier_weighted_pointwise φ n ξ).trans
    (compact_fourierDerivativeL1_bound φ haz hs' n hC')
  rw [SchwartzMap.fourier_coe,hφ] at hh
  have hpos : 0 < ‖ξ‖^n := pow_pos (norm_pos_iff.mpr hξ) _
  have hi : ‖𝓕 f ξ‖ ≤ (C*(z-a)*D^n/(2*Real.pi)^n)/‖ξ‖^n :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hh)
  simpa [div_div] using hi

 theorem compact_linear_phase_bound {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖∫ x : ℝ, Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x‖ ≤
      C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  have he : 𝓕 f ξ = ∫ x : ℝ,
      Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.inner_apply, smul_eq_mul]
    push_cast
    congr 2
    ring
  rw [← he]
  exact compact_fourier_nonstationary hf hs haz hξ n hC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LinearRadialDecay
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

theorem radialPhaseIntegral_bound {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b)
    (hb : ∀ s, ‖f s‖ ≤ C) : ‖radialPhaseIntegral f xi‖ ≤ C*(b-a) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hh := compact_derivative_integral_bound φ hab (by simpa [hφ] using hs) 0
    (by simpa only [iteratedDeriv_zero,hφ] using hb)
  simp only [iteratedDeriv_zero,hφ] at hh
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,sub_self,
    Real.exp_zero,one_mul] using hh

theorem radialPhaseIntegral_nonzero {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b)
    (hxi : xi ≠ 0) (n : ℕ) (hb : ∀ s, ‖iteratedDeriv n f s‖ ≤ C) :
    ‖radialPhaseIntegral f xi‖ ≤ C*(b-a)/|xi|^n := by
  have hp : (2:ℝ)*Real.pi ≠ 0 := by positivity
  have hh := compact_linear_phase_bound (ξ := -xi/(2*Real.pi)) (C := C) (D := 1)
    hf hs hab (div_ne_zero (neg_ne_zero.mpr hxi) hp) n (by simpa using hb)
  have he (s : ℝ) : -(2:ℂ)*(Real.pi:ℂ)*Complex.I*(s:ℂ)*((-xi/(2*Real.pi):ℝ):ℂ) =
      Complex.I*(xi:ℂ)*(s:ℂ) := by
    push_cast
    have hpc : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  simp_rw [he] at hh
  have hd : (2*Real.pi)^n*‖-xi/(2*Real.pi)‖^n = |xi|^n := by
    rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi),div_pow]
    field_simp
  simpa only [radialPhaseIntegral,one_pow,mul_one,hd] using hh

theorem radialPhaseIntegral_two_derivatives {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b) (hC : 0 ≤ C)
    (h0 : ∀ s, ‖f s‖ ≤ C) (h2 : ∀ s, ‖iteratedDeriv 2 f s‖ ≤ C) :
    ‖radialPhaseIntegral f xi‖ ≤ 4*C*(b-a)/(1+|xi|)^2 := by
  have hbase := radialPhaseIntegral_bound hf hs hab h0 (xi := xi)
  have ht : 0 ≤ C*(b-a) := mul_nonneg hC (sub_nonneg.mpr hab)
  have hden : 0 < (1+|xi|)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hsmall : |xi| ≤ 1
  · have hsquare : (1+|xi|)^2 ≤ 4 := by nlinarith [abs_nonneg xi]
    nlinarith [mul_le_mul_of_nonneg_left hsquare (norm_nonneg (radialPhaseIntegral f xi))]
  · have hbig : 1 < |xi| := lt_of_not_ge hsmall
    have hxi : xi ≠ 0 := by intro hz; norm_num [hz] at hbig
    have hh := (le_div_iff₀ (pow_pos (abs_pos.mpr hxi) 2)).mp
      (radialPhaseIntegral_nonzero hf hs hab hxi 2 h2)
    have hsquare : (1+|xi|)^2 ≤ 4*|xi|^2 := by nlinarith [sq_nonneg (|xi|-1)]
    nlinarith [mul_le_mul_of_nonneg_left hsquare (norm_nonneg (radialPhaseIntegral f xi))]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem signed_distance_frequency {d₁ d₂ s₁ s₂ : ℝ} (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    |d₁-d₂| ≤ |s₁*d₁+s₂*d₂| := by
  have hh : |d₁-d₂| ≤ d₁+d₂ :=
    abs_le.mpr ⟨by linarith only [h1], by linarith only [h2]⟩
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
  · simpa only [one_mul,abs_of_nonneg (add_nonneg h1 h2)] using hh
  · simp only [one_mul,neg_one_mul,← sub_eq_add_neg,le_refl]
  · rw [neg_one_mul,one_mul,show -d₁+d₂ = -(d₁-d₂) by ring,abs_neg]
  · rw [neg_one_mul,neg_one_mul,show -d₁+-d₂ = -(d₁+d₂) by ring,abs_neg,
      abs_of_nonneg (add_nonneg h1 h2)]
    exact hh

theorem angular_radial_kernel_bound {f : ℝ → ℂ} {C S R d₁ d₂ s₁ s₂ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc (1/4:ℝ) 4)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hR : 0 ≤ R) (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h0 : ∀ t, ‖f t‖ ≤ C*S) (hder : ∀ t, ‖iteratedDeriv 2 f t‖ ≤ C*S) :
    ‖radialPhaseIntegral f (R*(s₁*d₁+s₂*d₂))‖ ≤ 15*C*S/(1+R*|d₁-d₂|)^2 := by
  have hh := radialPhaseIntegral_two_derivatives hf hs (by norm_num) (mul_nonneg hC hS) h0 hder
    (xi := R*(s₁*d₁+s₂*d₂))
  have he : 4*(C*S)*((4:ℝ)-1/4) = 15*C*S := by ring
  rw [he] at hh
  apply hh.trans
  have hfreq : R*|d₁-d₂| ≤ |R*(s₁*d₁+s₂*d₂)| := by
    rw [abs_mul,abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (signed_distance_frequency h1 h2 hs₁ hs₂) hR
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (add_le_add_right hfreq 1) 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The failed perpendicular test in an actual spherical chart

The normalized affine chart stays within twice its tangent displacement
of the cap center. Its coordinate derivative therefore inherits the
uniform lower bound proved for the tangential sphere field.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_chart_nonzero {w h : E} (hw : ‖w‖ = 1) (hh : inner ℝ w h = 0) :
    w+h ≠ 0 := by
  intro he
  have hi := congrArg (inner ℝ w) he
  simp only [inner_add_right,real_inner_self_eq_norm_sq,hw,one_pow,hh,add_zero,
    inner_zero_right] at hi
  norm_num at hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small sphere caps have small gnomonic coordinates

This estimate converts the geometric cap support of an angular partition
into the compact coordinate support required by nonstationary integration.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem small_cap_chart_displacement {w h : E} (hw : ‖w‖ = 1)
    (horth : inner ℝ w h = 0) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ‖‖w+h‖⁻¹ • (w+h)-w‖ ≤ δ) : ‖h‖ ≤ 2*δ := by
  have hne := tangent_chart_nonzero hw horth
  have hr : 0 < ‖w+h‖ := norm_pos_iff.mpr hne
  have he : perpendicularPart w (‖w+h‖⁻¹ • (w+h)-w) = ‖w+h‖⁻¹ • h := by
    simp only [perpendicularPart,inner_sub_right,real_inner_smul_right,inner_add_right,
      real_inner_self_eq_norm_sq,hw,one_pow,horth,add_zero,mul_one]
    module
  have hp := (norm_perpendicularPart_le hw (‖w+h‖⁻¹ • (w+h)-w)).trans hcap
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)] at hp
  have hh : ‖h‖ ≤ ‖w+h‖*δ := by
    have hh := mul_le_mul_of_nonneg_left hp hr.le
    rwa [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at hh
  have ht : ‖w+h‖ ≤ 1+‖h‖ := by simpa only [hw] using norm_add_le w h
  have hbound := hh.trans (mul_le_mul_of_nonneg_right ht hδ)
  have hm : δ*‖h‖ ≤ (1/2 : ℝ)*‖h‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_RadialStationaryProfile
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem radialStationaryProfile_contDiff {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    ContDiff ℝ ∞ (radialStationaryProfile Ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hz : s = 0
  · subst s
    have he : radialStationaryProfile Ψ p =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)] with t ht
      have ht0 : Ψ t = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hs t hn).1.le) ht
      simp [radialStationaryProfile,ht0]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (hΨ.contDiffAt.mul (contDiffAt_id.rpow_const_of_ne hz))

theorem radialStationaryProfile_tsupport {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    tsupport (radialStationaryProfile Ψ p) ⊆ Icc (1/4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hn : Ψ t ≠ 0 := by
    intro hz
    exact ht (by simp [radialStationaryProfile,hz])
  exact Ioo_subset_Icc_self (hs t hn)

theorem compact_complex_derivatives_bounded {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport f ⊆ K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j f s‖ ≤ C := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr (show (j:ℕ∞) ≤ ⊤ from le_top))
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j).continuousOn
  let B := ∑ j ∈ Finset.range (n+1), max 0 (C j)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro j hj s
  by_cases hmem : s ∈ K
  · apply (hC j s hmem).trans
    apply (le_max_right 0 (C j)).trans
    exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · have hz : iteratedDeriv j f s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hmem (hs (complex_iteratedDeriv_tsupport f j ht)))
    simpa only [hz,norm_zero] using hB

theorem radialStationaryProfile_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (p : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j (radialStationaryProfile Ψ p) s‖ ≤ C :=
  compact_complex_derivatives_bounded (radialStationaryProfile_contDiff hΨ hs p)
    isCompact_Icc (radialStationaryProfile_tsupport hs p) n

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite-derivative bounds for stationary jets

The Laplacian is a fixed finite sum of second directional derivatives.
Expressing that contraction as a continuous linear map gives bounds for
all mixed Fréchet derivatives, without replacing them by separate bounds
on a single chart coordinate. Vertical unit vectors in a parameter/tangent
product give the partial Laplacian used by the actual stationary operators.
-/

namespace Falconer
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.Falconer.instNormedSpaceRealContinuousLinearMapIdComplex_solutions
attribute [local instance] OAI.Falconer.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions
theorem directionalLaplacianTrace_norm_le {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖directionalLaplacianTrace v‖ ≤ n := by
  apply (directionalLaplacianTrace v).opNorm_le_bound (Nat.cast_nonneg n)
  intro T
  rw [directionalLaplacianTrace_apply]
  calc
    ‖∑ i : Fin n, T (v i) (v i)‖ ≤ ∑ i : Fin n, ‖T (v i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖T (v i) (v i)‖ ≤ ‖T (v i)‖ * ‖v i‖ := (T (v i)).le_opNorm _
        _ ≤ (‖T‖ * ‖v i‖) * ‖v i‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖T‖ := by
          simpa only [mul_one] using mul_le_mul
            (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg T))
            (hv i) (norm_nonneg (v i)) (mul_nonneg (norm_nonneg T) zero_le_one)
    _ = (n : ℝ) * ‖T‖ := by simp

theorem directionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directionalLaplacian v f) := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    h₁.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (directionalLaplacianTrace v).contDiff.comp hd

theorem directionalLaplacian_derivative_bound {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (directionalLaplacian v f) x‖ ≤
      (n : ℝ) * ‖iteratedFDeriv ℝ (k+2) f x‖ := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    h₁.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ k
    ((directionalLaplacianTrace v) ∘ (fderiv ℝ (fderiv ℝ f))) x‖ ≤ _
  rw [(directionalLaplacianTrace v).iteratedFDeriv_comp_left hd.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  have h := (directionalLaplacianTrace v).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ f)) x)
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right (directionalLaplacianTrace_norm_le v hv)
    (norm_nonneg _))

theorem iteratedDirectionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ ((directionalLaplacian v)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      exact directionalLaplacian_contDiff v hj

/-- Every mixed derivative of order `k` of the `j`th directional Laplacian
uses only the amplitude's derivative of order `k+2j`, with loss `n^j`. -/
theorem iteratedDirectionalLaplacian_derivative_bound {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (j k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k ((directionalLaplacian v)^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  induction j generalizing k with
  | zero => simp
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      have h₁ := directionalLaplacian_derivative_bound v hv
        (iteratedDirectionalLaplacian_contDiff v hf j) k x
      have h₂ := mul_le_mul_of_nonneg_left (hj (k+2)) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      apply (h₁.trans h₂).trans_eq
      rw [show k+2+2*j = k+2*(j+1) by omega, pow_succ]
      ring

theorem directionalLaplacian_basis {n : ℕ} (f : Space n → ℂ) :
    directionalLaplacian (EuclideanSpace.basisFun (Fin n) ℝ) f = Laplacian.laplacian f := by
  funext x
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  rfl

theorem euclidean_iterated_laplacian_derivative_bound {n : ℕ} {f : Space n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : ℕ) (x : Space n) :
    ‖iteratedFDeriv ℝ k
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  have he : directionalLaplacian (EuclideanSpace.basisFun (Fin n) ℝ) =
      (Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ)) := by
    funext g
    exact directionalLaplacian_basis g
  rw [← he]
  apply iteratedDirectionalLaplacian_derivative_bound _ _ hf
  intro i
  simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianIsometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance and locality of the actual quadratic jets

These are identities for the Euclidean derivatives in the published input.
They allow the choice of tangent orthonormal coordinates and fixed cutoffs
to be removed from the resulting stationary coefficients.
-/

namespace Falconer
open InnerProductSpace
open scoped Topology

theorem euclidean_iterated_laplacian_congr {n : ℕ} {f g : Space n → ℂ}
    {x : Space n} (h : f =ᶠ[𝓝 x] g) (j : ℕ) :
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) =ᶠ[𝓝 x]
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] g) := by
  induction j with
  | zero => exact h
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact laplacian_congr_nhds hj

theorem quadraticJetCoefficient_congr {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᶠ[𝓝 (0 : Space n)] g) (j : ℕ) :
    quadraticJetCoefficient j f = quadraticJetCoefficient j g := by
  unfold quadraticJetCoefficient
  rw [(euclidean_iterated_laplacian_congr h j).self_of_nhds]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuadraticChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed quadratic chart at a sphere pole

This is the actual chart in `osc:stationary`. Its phase is exactly quadratic,
in every dimension. Surface measure transport and its Jacobian are separate
from the geometric statements here.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem quadraticSpherePoint_norm {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u‖ = 1 := by
  have hu2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have harg : 0 ≤ 1-‖u‖^2/4 := by nlinarith
  have hs := Real.sq_sqrt harg
  have he := coordinateJoin_norm_sq (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs] at he
  change ‖quadraticSpherePoint u‖^2 = _ at he
  nlinarith [norm_nonneg (quadraticSpherePoint u)]

/-- The oscillatory phase at the pole is exactly `1 - ‖u‖²/2`. -/
theorem quadraticSpherePoint_phase {n : ℕ} (u : Space n) :
    inner ℝ (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1) =
      1-‖u‖^2/2 := by
  simp [quadraticSpherePoint, coordinateJoin_inner]

theorem gnomonicChart_quadraticToGnomonic {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (gnomonicChart (quadraticToGnomonic u) : Space (n+1)) = quadraticSpherePoint u := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; nlinarith
  have he : northLift (quadraticToGnomonic u) = a⁻¹ • quadraticSpherePoint u := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [northLift_zero, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_zero_coord]
      change 1 = a⁻¹ * a
      exact (inv_mul_cancel₀ ha.ne').symm
    · simp only [northLift_succ, quadraticToGnomonic, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_succ_coord]
      dsimp only [a]
      ring
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    rw [he, norm_smul, quadraticSpherePoint_norm (hu.le.trans (by norm_num)),
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_one]
  change ‖northLift (quadraticToGnomonic u)‖⁻¹ • northLift (quadraticToGnomonic u) = _
  rw [hn, he, smul_smul, inv_inv, mul_inv_cancel₀ ha.ne', one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the quadratic expansion to the actual sphere integral

The amplitude is the explicitly computed surface density times the spherical
amplitude, extended by zero from the fixed unit chart. Smoothness and its
quantitative derivative bounds are retained as local obligations. The only
published inputs are the gnomonic measure formula and the fixed Euclidean
quadratic stationary-phase theorem.
-/

namespace Falconer
open Set MeasureTheory Metric
open scoped BigOperators ContDiff

/-- A mask that vanishes in the outer half of the fixed chart removes the
boundary issue in extending its chart amplitude by zero. -/
theorem quadraticAmplitude_contDiff (m : ℕ) (b : Sphere (m+3) → ℂ)
    (hb : ContDiffOn ℝ ∞
      (fun u : Space (m+2) => b (gnomonicChart (quadraticToGnomonic u)))
      (Metric.ball (0 : Space (m+2)) 1))
    (hmask : ∀ u : Space (m+2), (1:ℝ)/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (gnomonicChart (quadraticToGnomonic u)) = 0) :
    ContDiff ℝ ∞ (quadraticAmplitude m b) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : ‖u‖ < 1
  · have hum : u ∈ Metric.ball (0 : Space (m+2)) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hsq : ‖u‖^2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
    have hd : ContDiffAt ℝ ∞
        (fun v : Space (m+2) => ((Real.sqrt (1-‖v‖^2/4))^m : ℂ)) u := by
      apply ContDiffAt.pow
      exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
        ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
          (by linarith : 1-‖u‖^2/4 ≠ 0))
    apply (hd.mul ((hb u hum).contDiffAt (isOpen_ball.mem_nhds hum))).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hum] with v hv
    simp only [quadraticAmplitude, indicator_of_mem hv]
  · have hlarge : (1:ℝ)/2 < ‖u‖ := by linarith
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlarge] with v hv
    by_cases hvin : v ∈ Metric.ball (0 : Space (m+2)) 1
    · have hvnorm : ‖v‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hvin
      simp only [quadraticAmplitude, indicator_of_mem hvin,
        hmask v (le_of_lt hv) hvnorm, mul_zero]
    · simp only [quadraticAmplitude, indicator_of_notMem hvin]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

theorem stationaryPoleRotation_pole {n : ℕ} (e : Sphere (n+1)) :
    stationaryPoleRotation e (gnomonicChart (0 : Space n)) = (e : Space (n+1)) := by
  have h := Submodule.reflection_sub
    (v := (gnomonicChart (0 : Space n) : Space (n+1))) (w := -(e : Space (n+1)))
    (by rw [norm_neg, sphere_norm, sphere_norm])
  rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
  exact neg_injective h

theorem stationaryPoleRotation_apply {n : ℕ} (e : Sphere (n+1)) (x : Space (n+1)) :
    stationaryPoleRotation e x =
      poleRotationFormula (gnomonicChart (0 : Space n)) e x := by
  rw [stationaryPoleRotation, Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

theorem gnomonicChart_zero_pole (n : ℕ) :
    (gnomonicChart (0 : Space n) : Space (n+1)) = coordinateJoin (0 : Space n) 1 := by
  have hn : ‖northLift (0 : Space n)‖ = 1 := by
    have h : ‖northLift (0 : Space n)‖^2 = 1 := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
        northLift_norm_sq (0 : Space n)
    nlinarith [norm_nonneg (northLift (0 : Space n))]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [gnomonicChart_zero, hn]
    simp [coordinateJoin_eq]
  · simp [gnomonicChart_succ, coordinateJoin_eq]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartJetOperators
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual stationary operators on a smooth pole patch

The operators are the quadratic Laplacian jets of the explicit chart
amplitude. They depend smoothly on the evaluation direction away from the
opposite pole. Their equality with the coefficients in the local
sphere expansion follows by locality, including the fixed chart cutoff.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem actualStationaryCoefficient_eq (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m j B e =
      quadraticJetCoefficient j (quadraticAmplitude m
        (fun w => B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticJetCoefficient_congr
  filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : Space (m+2)) ∈ ball 0 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hu
  simp only [unmaskedStationaryAmplitude, quadraticAmplitude, indicator_of_mem hu]
  congr 1
  congr 1
  rw [← stationaryPoleRotation_apply, ← gnomonicChart_quadraticToGnomonic hu']
  rfl

@[simp] theorem actualStationaryCoefficient_zero (m : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m 0 B e = sphereStationaryConstant (m+2) * B e := by
  rw [actualStationaryCoefficient_eq, quadraticJetCoefficient_amplitude_zero]
  change _ * B (stationaryPoleRotation e (gnomonicChart (0 : Space (m+2)))) = _
  rw [stationaryPoleRotation_pole]

/-- The actual coefficient depends only on the original amplitude near its
evaluation direction; every cutoff that is constant there is invisible. -/
theorem actualStationaryCoefficient_local (m j : ℕ) {B G : Space (m+3) → ℂ}
    (e : Sphere (m+3)) (hBG : B =ᶠ[𝓝 (e : Space (m+3))] G) :
    actualStationaryCoefficient m j B e = actualStationaryCoefficient m j G e := by
  apply quadraticJetCoefficient_congr
  let γ : Space (m+2) → Space (m+3) :=
    fun u => stationaryPoleRotation e (quadraticSpherePoint u)
  have hq0 : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  have hγ0 : γ 0 = (e : Space (m+3)) := by
    change stationaryPoleRotation e (quadraticSpherePoint 0) = _
    rw [hq0, stationaryPoleRotation_pole]
  have hγ : Filter.Tendsto γ (𝓝 (0 : Space (m+2))) (𝓝 (e : Space (m+3))) := by
    rw [← hγ0]
    exact (stationaryPoleRotation e).continuous.continuousAt.comp
      (quadraticSpherePoint_contDiffAt (u := (0 : Space (m+2))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  filter_upwards [hBG.comp_tendsto hγ] with u hu
  simp only [unmaskedStationaryAmplitude, ← stationaryPoleRotation_apply]
  rw [show B (stationaryPoleRotation e (quadraticSpherePoint u)) =
    G (stationaryPoleRotation e (quadraticSpherePoint u)) from hu]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleCutoffs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem poleCutoff_zero {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : 1/4 ≤ ‖x-(e : Space d)‖) : poleCutoff e x = 0 := by
  apply (capBump (1/4) (by norm_num) e).zero_of_le_dist
  simpa only [dist_eq_norm,capBump] using hx

theorem poleCutoff_support {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : poleCutoff e x ≠ 0) : ‖x-(e : Space d)‖ < 1/4 := by
  by_contra h
  exact hx (poleCutoff_zero e x (le_of_not_gt h))

/-- In quadratic coordinates, Euclidean distance from the pole is exactly
the coordinate radius. This gives the needed interior cutoff support. -/
theorem quadraticSpherePoint_dist_pole {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u-coordinateJoin (0 : Space n) 1‖ = ‖u‖ := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    have h := coordinateJoin_norm_sq (0 : Space n) 1
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),one_pow] at h
    nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]
  have h := norm_sub_sq_real (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1)
  rw [quadraticSpherePoint_norm hu,hp,quadraticSpherePoint_phase] at h
  nlinarith [norm_nonneg (quadraticSpherePoint u-coordinateJoin (0 : Space n) 1),norm_nonneg u]

/-- Only a small fixed part of the coordinate image is needed for the
application. Radial continuity proves its inclusion without imposing a
global inverse chart. -/
theorem quadraticToGnomonic_image_smallBall {n : ℕ} (x : Space n)
    (hx : ‖x‖ ≤ 1/2) :
    x ∈ quadraticToGnomonic '' ball (0 : Space n) 1 := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0,by simp,by simp [quadraticToGnomonic]⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let g : ℝ → ℝ := fun r => Real.sqrt (1-r^2/4)/(1-r^2/2)*r
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul _ continuousOn_id
    apply ContinuousOn.div
    · exact (continuousOn_const.sub ((continuousOn_id.pow 2).div_const 4)).sqrt
    · exact continuousOn_const.sub ((continuousOn_id.pow 2).div_const 2)
    · intro r hr
      have hr2 : r^2 ≤ 1 := by
        simpa using (sq_le_sq₀ hr.1 (by norm_num : (0 : ℝ) ≤ 1)).mpr hr.2
      linarith
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : 1 ≤ g 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/4)
    have hn := Real.sqrt_nonneg (3/4 : ℝ)
    have he : g 1 = 2*Real.sqrt (3/4 : ℝ) := by dsimp [g]; norm_num; ring
    rw [he]
    nlinarith
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hg
    (show ‖x‖ ∈ Icc (g 0) (g 1) from ⟨by rw [hg0]; exact hxn.le,hx.trans (by linarith)⟩)
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hr.2
    intro hrEq
    have he1 : g 1 = ‖x‖ := by simpa only [hrEq] using he
    linarith
  let u : Space n := (r/‖x‖) • x
  have hu : ‖u‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr.1 hxn.le),div_mul_cancel₀ _ hxn.ne']
  refine ⟨u,by simpa only [mem_ball,dist_zero_right,hu] using hr1,?_⟩
  change (Real.sqrt (1-‖u‖^2/4)/(1-‖u‖^2/2)) • u = x
  rw [hu]
  change (Real.sqrt (1-r^2/4)/(1-r^2/2)) • ((r/‖x‖) • x) = x
  rw [smul_smul]
  have hc : (Real.sqrt (1-r^2/4)/(1-r^2/2))*(r/‖x‖) = 1 := by
    apply (mul_right_cancel₀ hxn.ne')
    calc
      _ = (Real.sqrt (1-r^2/4)/(1-r^2/2))*r := by field_simp
      _ = ‖x‖ := he
      _ = 1*‖x‖ := (one_mul _).symm
  rw [hc,one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleStationarySupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual support conditions for the pole expansion

Geometric support in a radius-1/4 cap implies all support conditions in
the quadratic stationary theorem. The ambient pole bump is invisible to
the actual coefficient jets at its center.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem gnomonic_small_cap_coordinates {n : ℕ} (x : Space n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hcap : ‖(gnomonicChart x : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ δ) :
    ‖x‖ ≤ 2*δ := by
  let p := coordinateJoin (0 : Space n) 1
  let h := coordinateJoin x 0
  have hp : ‖p‖ = 1 := by
    change ‖coordinateJoin (0 : Space n) 1‖ = 1
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have horth : inner ℝ p h = 0 := by simp [p,h,coordinateJoin_inner]
  have hh : ‖h‖ = ‖x‖ := by
    change ‖coordinateJoin x 0‖ = ‖x‖
    have he := coordinateJoin_norm_sq x 0
    simp only [zero_pow (by decide : 2 ≠ 0),zero_add] at he
    nlinarith [norm_nonneg (coordinateJoin x 0),norm_nonneg x]
  have hsplit : northLift x = p+h := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [p,h,northLift,coordinateJoin_eq]
  have hc : ‖‖p+h‖⁻¹ • (p+h)-p‖ ≤ δ := by
    simpa only [gnomonicChart,hsplit] using hcap
  rw [← hh]
  exact small_cap_chart_displacement hp horth hδ hδsmall hc

private theorem fixed_cap_mem_north {n : ℕ} (w : Sphere (n+1))
    (hw : ‖(w : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ 1/4) :
    w ∈ northHemisphere n := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have hi : inner ℝ (w : Space (n+1)) (coordinateJoin (0 : Space n) 1) =
      (w : Space (n+1)) 0 := by
    rw [PiLp.inner_apply,Fin.sum_univ_succ]
    simp [coordinateJoin_eq]
  have he := norm_sub_sq_real (w : Space (n+1)) (coordinateJoin (0 : Space n) 1)
  rw [sphere_norm,hp,hi] at he
  change 0 < (w : Space (n+1)) 0
  nlinarith [norm_nonneg ((w : Space (n+1))-coordinateJoin (0 : Space n) 1)]

theorem rotated_cap_quadratic_support (m : ℕ) (e : Sphere (m+3))
    (b : Sphere (m+3) → ℂ)
    (hcap : ∀ w, b w ≠ 0 → ‖(w : Space (m+3))-(e : Space (m+3))‖ ≤ 1/4) :
    let T := stationaryPoleRotation e
    (∀ w, w ∉ northHemisphere (m+2) → b (sphereMap T w) = 0) ∧
    (∀ x : Space (m+2), x ∉ quadraticToGnomonic '' ball (0 : Space (m+2)) 1 →
      b (sphereMap T (gnomonicChart x)) = 0) ∧
    (∀ u : Space (m+2), 1/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (sphereMap T (gnomonicChart (quadraticToGnomonic u))) = 0) := by
  let T := stationaryPoleRotation e
  have htransport (w : Sphere (m+3)) (hw : b (sphereMap T w) ≠ 0) :
      ‖(w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1‖ ≤ 1/4 := by
    have he : T (coordinateJoin (0 : Space (m+2)) 1) = (e : Space (m+3)) := by
      rw [← gnomonicChart_zero_pole]
      exact stationaryPoleRotation_pole e
    calc
      _ = ‖T ((w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1)‖ := (T.norm_map _).symm
      _ = ‖(sphereMap T w : Space (m+3))-(e : Space (m+3))‖ := by rw [T.map_sub,he]; rfl
      _ ≤ _ := hcap _ hw
  refine ⟨?_,?_,?_⟩
  · intro w hw
    by_contra hb
    exact hw (fixed_cap_mem_north w (htransport w hb))
  · intro x hx
    by_contra hb
    have hc := gnomonic_small_cap_coordinates x (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1/2) (htransport _ hb)
    exact hx (quadraticToGnomonic_image_smallBall x (by linarith))
  · intro u hu hu1
    by_contra hb
    have hc := htransport _ hb
    rw [gnomonicChart_quadraticToGnomonic hu1,
      quadraticSpherePoint_dist_pole (hu1.le.trans (by norm_num))] at hc
    linarith

theorem poleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (poleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).mul hB

theorem poleLocalizedAmbient_cap {d : ℕ} (e : Sphere d) (B : Space d → ℂ)
    (w : Sphere d) (hw : poleLocalizedAmbient e B w ≠ 0) :
    ‖(w : Space d)-(e : Space d)‖ ≤ 1/4 := by
  apply (poleCutoff_support e w _).le
  intro hz
  exact hw (by simp only [poleLocalizedAmbient,hz,Complex.ofReal_zero,zero_mul])

theorem poleLocalizedAmbient_coefficient (m j : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    actualStationaryCoefficient m j (poleLocalizedAmbient e B) e =
      actualStationaryCoefficient m j B e := by
  apply actualStationaryCoefficient_local m j e
  have he := (capBump (1/4) (by norm_num) e).eventuallyEq_one
  filter_upwards [he] with x hx
  change capBump (1/4) (by norm_num) e x = (1 : ℝ) at hx
  simp only [poleLocalizedAmbient,poleCutoff,hx,Complex.ofReal_one,one_mul]

theorem poleLocalized_quadratic_contDiff (m : ℕ) (e : Sphere (m+3))
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticAmplitude_contDiff
  · let T := stationaryPoleRotation e
    have h : ContDiffOn ℝ ∞
        (fun u => poleLocalizedAmbient e B (T (quadraticSpherePoint u)))
        (ball (0 : Space (m+2)) 1) := by
      intro u hu
      have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
      exact ((poleLocalizedAmbient_contDiff e hB).comp
        T.toContinuousLinearMap.contDiff).contDiffAt.comp u
          (quadraticSpherePoint_contDiffAt (hu1.trans (by norm_num))) |>.contDiffWithinAt
    apply h.congr
    intro u hu
    have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
    change poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic u))) = _
    rw [gnomonicChart_quadraticToGnomonic hu1]
  · exact (rotated_cap_quadratic_support m e (fun w => poleLocalizedAmbient e B w)
      (poleLocalizedAmbient_cap e B)).2.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FixedChartBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite derivative bounds for fixed quadratic geometry

Only compact sets inside the smooth chart are used. The chart need not
extend smoothly through its outer singularity.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_iteratedFDeriv_bound_at {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i f) K := by
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  choose A hA using fun i => hK.exists_bound_of_continuousOn (hc i)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  refine ⟨C,Finset.sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem norm_iteratedFDeriv_mul_le_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (k-i) g x‖ := by
  obtain ⟨U,hU,hxU,hfU⟩ := hf.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨V,hV,hxV,hgV⟩ := hg.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hxW : x ∈ W := ⟨hxU,hxV⟩
  have hfU' : ContDiffOn ℝ k f U := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hfU
  have hgV' : ContDiffOn ℝ k g V := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hgV
  have hfW : ContDiffOn ℝ k f W := hfU'.mono inter_subset_left
  have hgW : ContDiffOn ℝ k g W := hgV'.mono inter_subset_right
  have hh := norm_iteratedFDerivWithin_mul_le hfW hgW hW.uniqueDiffOn hxW (le_refl (k : ℕ∞ω))
  have hre (j : ℕ) (a : E → ℂ) : iteratedFDerivWithin ℝ j a W x = iteratedFDeriv ℝ j a x :=
    iteratedFDerivWithin_of_isOpen j hW hxW
  simpa only [hre] using hh

theorem fixed_quadratic_geometry_bounds (n m k : ℕ) :
    ∃ Q C : ℝ, 0 ≤ Q ∧ 0 ≤ C ∧ ∀ j ≤ k, ∀ u : Space n, ‖u‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j quadraticSpherePoint u‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ j (quadraticChartDensity m) u‖ ≤ C := by
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticSpherePoint_contDiffAt (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticChartDensity_contDiffAt m (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  refine ⟨Q,C,hQ,hC,?_⟩
  intro j hj u hu
  have hum : u ∈ closedBall (0 : Space n) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hu
  exact ⟨hQb j hj u hum,hCb j hj u hum⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative budget of the actual quadratic amplitude

The fixed pole cutoff and fixed quadratic geometry cost constants depending
only on the dimension and derivative order. The original symbol supplies
the entire scale power.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem mixed_product_uniform_bound_at {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (k : ℕ)
    (hfb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 2^k*A*B := by
  apply (norm_iteratedFDeriv_mul_le_at hf hg k).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb j hjk) (Nat.cast_nonneg _))
        (hgb (k-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      have hs : (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
        simpa only [one_pow,mul_one,one_mul,one_add_one_eq_two] using
          (add_pow (1 : ℝ) 1 k).symm
      rw [← Finset.sum_mul,← Finset.sum_mul,hs]

theorem poleLocalizedAmbient_uniform_budget (d K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ j (poleLocalizedAmbient e B) w‖ ≤ A*C*D^K := by
  choose P hP hPb using fun j => capBump_ambient_derivatives d j
  let Q := ∑ j ∈ Finset.range (K+1), P j*4^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  have hPQ (j : ℕ) (hj : j ≤ K) : P j*4^j ≤ Q := by
    change P j*(4 : ℝ)^j ≤ ∑ i ∈ Finset.range (K+1), P i*4^i
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hP i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*Q,by positivity,?_⟩
  intro e B hB C D hC hD hb j hj w
  have hCD : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  have hcut (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun x => (poleCutoff e x : ℂ)) w‖ ≤ Q := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((poleCutoff_contDiff e).contDiffAt (x := (w : Space d)))
      (show (i : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ poleCutoff e) w‖ ≤ Q
    rw [hn]
    apply (hPb i (1/4) (by norm_num) e w).trans
    simpa only [one_div,inv_inv] using hPQ i (hi.trans hj)
  have hBb (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i B w‖ ≤ C*D^K :=
    (hb i (hi.trans hj) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (hi.trans hj)) hC)
  have hh := mixed_product_uniform_bound_at
    ((Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).contDiffAt)
    hB.contDiffAt hQ hCD j hcut hBb
  apply hh.trans
  calc
    _ ≤ 2^K*Q*(C*D^K) := by gcongr; norm_num
    _ = _ := by ring

theorem quadraticAmplitude_tsupport_half (m : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    tsupport (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) ⊆
      closedBall (0 : Space (m+2)) (1/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  by_contra hout
  have hlarge : 1/2 < ‖u‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hout
  by_cases hunit : ‖u‖ < 1
  · have hz := (rotated_cap_quadratic_support m e
      (fun w => poleLocalizedAmbient e B w) (poleLocalizedAmbient_cap e B)).2.2 u hlarge.le hunit
    have hum : u ∈ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_mem hum,hz,mul_zero])
  · have hum : u ∉ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_notMem hum])

theorem quadratic_chart_composition_uniform_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (T : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1))
      (B : Space (n+1) → ℂ), ContDiff ℝ ∞ B → ∀ E : ℝ, 0 ≤ E →
      (∀ j ≤ K, ∀ w : Sphere (n+1), ‖iteratedFDeriv ℝ j B w‖ ≤ E) →
      ∀ j ≤ K, ∀ u : Space n, ‖u‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j (fun y => B (T (quadraticSpherePoint y))) u‖ ≤ H*E := by
  obtain ⟨Q,_C,hQ,_hC,hgeometry⟩ := fixed_quadratic_geometry_bounds n 0 K
  let a : ℕ → ℝ := fun j => mixedCompositionBudget (fun _ => Q) j
  have ha (j : ℕ) : 0 ≤ a j := mixedCompositionBudget_nonneg (fun _ => hQ) j
  let H := ∑ j ∈ Finset.range (K+1), a j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => ha j)
  have haH (j : ℕ) (hj : j ≤ K) : a j ≤ H :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨H,hH,?_⟩
  intro T B hB E hE hb j hj u hu
  have hu2 : ‖u‖ < 2 := by linarith
  have hQu := quadraticSpherePoint_contDiffAt hu2
  let f : Space n → Space (n+1) := fun y => T (quadraticSpherePoint y)
  have hf : ContDiffAt ℝ ∞ f u := T.toContinuousLinearMap.contDiff.contDiffAt.comp u hQu
  let w : Sphere (n+1) := ⟨f u,by
    rw [mem_sphere,dist_zero_right]
    exact (T.norm_map _).trans (quadraticSpherePoint_norm hu2.le)⟩
  have hinner (i : ℕ) (_hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i f u‖ ≤ Q*(1 : ℝ)^i := by
    have he := T.toLinearIsometry.norm_iteratedFDeriv_comp_left hQu
      (show (i : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ i (T.toLinearIsometry ∘ quadraticSpherePoint) u‖ ≤ _
    rw [he,one_pow,mul_one]
    exact (hgeometry i (hij.trans hj) u hu).1
  have hh := mixed_composition_derivative_bound hf hB.contDiffAt hE j
    (fun i hi => hb i (hi.trans hj) w) hinner
  change ‖iteratedFDeriv ℝ j (B ∘ f) u‖ ≤ H*E
  apply hh.trans
  simp only [one_pow,mul_one]
  exact mul_le_mul_of_nonneg_right (haH j hj) hE

/-- Uniform global bounds for the actual zero-extended quadratic amplitude.
The scale appears with exactly the highest requested derivative order K. -/
theorem pole_quadratic_amplitude_budget (m K : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ u,
        ‖iteratedFDeriv ℝ j (quadraticAmplitude m
          (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) u‖ ≤
          L*C*D^K := by
  obtain ⟨A,hA,hAb⟩ := poleLocalizedAmbient_uniform_budget (m+3) K
  obtain ⟨H,hH,hHb⟩ := quadratic_chart_composition_uniform_budget (m+2) K
  obtain ⟨_Q,R,_hQ,hR,hgeometry⟩ := fixed_quadratic_geometry_bounds (m+2) m K
  refine ⟨2^K*R*H*A,by positivity,?_⟩
  intro e B hB C D hC hD hder j hj u
  let b := fun w : Sphere (m+3) => poleLocalizedAmbient e B w
  let amp := quadraticAmplitude m (fun w => b (sphereMap (stationaryPoleRotation e) w))
  let T := stationaryPoleRotation e
  let G : Space (m+2) → ℂ := fun y => poleLocalizedAmbient e B (T (quadraticSpherePoint y))
  let F : Space (m+2) → ℂ := fun y => quadraticChartDensity m y * G y
  have hE : 0 ≤ A*C*D^K := by positivity
  have hGb := hHb T (poleLocalizedAmbient e B) (poleLocalizedAmbient_contDiff e hB)
    (A*C*D^K) hE (hAb e B hB C D hC hD hder)
  by_cases hu : ‖u‖ < 1
  · have hu2 : ‖u‖ < 2 := hu.trans (by norm_num)
    have hG : ContDiffAt ℝ ∞ G u :=
      ((poleLocalizedAmbient_contDiff e hB).comp T.toContinuousLinearMap.contDiff).contDiffAt.comp u
        (quadraticSpherePoint_contDiffAt hu2)
    have hbound := mixed_product_uniform_bound_at (quadraticChartDensity_contDiffAt m hu2)
      hG hR (mul_nonneg hH hE) j
      (fun i hi => (hgeometry i (hi.trans hj) u hu.le).2)
      (fun i hi => hGb i (hi.trans hj) u hu.le)
    have he : amp =ᶠ[𝓝 u] F := by
      have hum : u ∈ ball (0 : Space (m+2)) 1 := by simpa only [mem_ball,dist_zero_right] using hu
      filter_upwards [isOpen_ball.mem_nhds hum] with y hy
      have hy1 : ‖y‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy
      dsimp only [amp,quadraticAmplitude,F,G,b,quadraticChartDensity]
      rw [indicator_of_mem hy]
      change _ * poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic y))) = _
      rw [gnomonicChart_quadraticToGnomonic hy1]
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
    apply hbound.trans
    calc
      _ ≤ 2^K*R*(H*(A*C*D^K)) := by gcongr; norm_num
      _ = _ := by ring
  · have hn : u ∉ tsupport amp := by
      intro hm
      have hh := quadraticAmplitude_tsupport_half m e B hm
      have huHalf : ‖u‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hh
      linarith
    have he := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ j
    have hz : iteratedFDeriv ℝ j amp u = 0 := by simpa using he.self_of_nhds
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [hz,norm_zero]
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereStationaryAssembly
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration for the two stationary poles

These identities retain the original sphere measure and the original
ambient amplitude. The antipodal contribution uses the same smooth pole
patch as the outgoing contribution.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem antipodalConjugate_contDiff {d : ℕ} {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (antipodalConjugate B) :=
  Complex.conjCLE.contDiff.comp (hB.comp contDiff_id.neg)

theorem antipodalConjugate_derivative_norm {d : ℕ} (B : Space d → ℂ)
    (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (antipodalConjugate B) x‖ = ‖iteratedFDeriv ℝ k B (-x)‖ := by
  change ‖iteratedFDeriv ℝ k (Complex.conjLIE ∘
    (B ∘ LinearIsometryEquiv.neg ℝ (E := Space d))) x‖ = _
  rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left,
    (LinearIsometryEquiv.neg ℝ (E := Space d)).norm_iteratedFDeriv_comp_right]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.cover_descendants {d : ℕ} (Q : DyadicCube d) (n : ℕ) :
    Q.carrier = ⋃ p ∈ cubePaths d n, (Q.descendant p).carrier := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨p, hp, hxp⟩
  · exact iUnion₂_subset fun p _ => Q.descendant_subset p

/-- Exact disjoint measure decomposition; no boundaries or extra spatial
cutoffs are added to the original law. -/
theorem DyadicCube.restrict_descendants {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier = ∑ p ∈ cubePaths d n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.cover_descendants n]
  rw [Measure.restrict_biUnion_finset]
  · simp only [Measure.sum_fintype, Finset.univ_eq_attach]
    exact Finset.sum_attach (cubePaths d n) (fun p => μ.restrict (Q.descendant p).carrier)
  · intro p hp q hq hpq
    exact Q.descendants_disjoint ((mem_cubePaths d n p).mp hp |>.trans
      ((mem_cubePaths d n q).mp hq).symm) hpq
  · intro p
    exact (Q.descendant p).measurable

theorem DyadicCube.restrict_occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier =
      ∑ p ∈ Q.occupiedPaths μ n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.restrict_descendants μ n]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpo
  apply Measure.restrict_eq_zero.mpr
  have hz : ¬ 0 < μ (Q.descendant p).carrier := by
    intro hpos
    exact hpo (Finset.mem_filter.mpr ⟨hp, hpos⟩)
  exact le_antisymm (le_of_not_gt hz) bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_AngularTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

theorem angularTubeEvent_measurable {d : ℕ} (v : Space d) (W : ℝ) :
    MeasurableSet (angularTubeEvent v W) := by
  have hc : Continuous (fun w : Sphere d => v-inner ℝ (w:Space d) v • (w:Space d)) :=
    continuous_const.sub ((continuous_subtype_val.inner (𝕜 := ℝ) continuous_const).smul continuous_subtype_val)
  exact measurableSet_le hc.norm.measurable measurable_const

theorem finiteTubeCount_eq_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    (finiteTubeCount S v W w : ℝ≥0∞) =
      ∑ i ∈ S, (angularTubeEvent (v i) W).indicator (fun _ => (1:ℝ≥0∞)) w := by
  classical
  simp only [finiteTubeCount,Finset.natCast_card_filter,Set.indicator_apply]

theorem finiteTubeCount_measurable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) :
    Measurable (fun w : Sphere d => (finiteTubeCount S v W w : ℝ≥0∞)) := by
  simp_rw [finiteTubeCount_eq_sum]
  exact Finset.measurable_sum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

namespace Regularization
variable {d : ℕ}

theorem parallelGoodSet_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) :
    MeasurableSet (parallelGoodSet Q ρ g p P W T) := by
  classical
  unfold parallelGoodSet
  split_ifs
  · exact measurableSet_le (finiteTubeCount_measurable _ _ _) measurable_const
  · exact MeasurableSet.empty

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurable_projectionCollision (μ : Measure (Space d)) [IsFiniteMeasure μ] (W : ℝ) :
    Measurable (fun w : Sphere d => projectionCollision μ (w:Space d) W) := by
  let S := {p : Sphere d × (Space d × Space d) |
    |inner ℝ (p.2.1-p.2.2) (p.1:Space d)| ≤ W}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem measurableSet_projectionGoodSet (μ : Measure (Space d)) [IsFiniteMeasure μ] (W T : ℝ) :
    MeasurableSet (projectionGoodSet μ W T) :=
  measurableSet_le (measurable_projectionCollision μ W) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

theorem conditionalProjectionGoodSet_measurable (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) (W T : ℝ) :
    MeasurableSet (conditionalProjectionGoodSet Q ρ P W T) := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact measurableSet_projectionGoodSet _ _ _
  · exact MeasurableSet.empty

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

theorem descriptorGoodDirections_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (P : List (Fin d → Bool)) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodDirections Q ρ m N σ J i P b) := by
  cases b with
  | parallel g p => exact Regularization.parallelGoodSet_measurable _ _ _ _ _ _ _
  | projection p t => exact Regularization.conditionalProjectionGoodSet_measurable _ _ _ _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorEndpointGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) :
    MeasurableSet (descriptorEndpointGood Q ρ m N σ J i b) := by
  classical
  have hm : MeasurableSet (⋂ p ∈ cubePaths d (descriptorAnchor b),
      {z : Space d × Sphere d | z.1 ∈ (Q.descendant p).carrier →
        z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}) := by
    apply Finset.measurableSet_biInter
    intro p _
    convert ((Q.descendant p).measurable.preimage measurable_fst).compl.union
      ((descriptorGoodDirections_measurable Q ρ m N σ J i p b).preimage measurable_snd) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,imp_iff_not_or]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorEndpointGood]

theorem descriptorPairTests_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    MeasurableSet (descriptorPairTests w₀ Q ρ m N σ J i B) := by
  classical
  have hm := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  have hset : MeasurableSet (⋂ b ∈ B, {z : Space d × Space d |
      (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
      (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}) := by
    apply Finset.measurableSet_biInter
    intro b _
    exact ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
      (measurable_fst.prodMk hm)).inter
        ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
          (measurable_snd.prodMk hm))
  convert hset using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorPairTests]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_Bins
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinOffsets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BinKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinEstimates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteMeasureProducts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_measure_prod_sum {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : Finset ι) (T : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    (∑ i ∈ S, μ i).prod (∑ j ∈ T, ν j) = ∑ i ∈ S, ∑ j ∈ T, (μ i).prod (ν j) := by
  apply Measure.ext_prod
  intro s t hs ht
  simp only [Measure.prod_prod,Measure.finsetSum_apply,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem finite_measure_restrict_sum {α ι : Type*} [MeasurableSpace α]
    (S : Finset ι) (μ : ι → Measure α) (A : Set α) :
    (∑ i ∈ S, μ i).restrict A = ∑ i ∈ S, (μ i).restrict A := by
  ext s hs
  simp only [Measure.restrict_apply hs,Measure.finsetSum_apply]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FarCellGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual cell geometry used by the far transition

The fixed separation constant may be chosen as 2000(d+1).  Comparable
point displacements at a dyadic depth then give cells satisfying that
separation, while a center displacement outside the near graph remains
large throughout both cells.
-/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem DyadicCube.point_center_bound (P : DyadicCube d) (hP : 0 < P.side)
    {ℓ : ℝ} (hside : P.side ≤ ℓ) {x : Space d} (hx : x ∈ P.carrier) :
    dist x P.center ≤ ((d:ℝ)+1)*ℓ := by
  exact (P.dist_le hP.le hx (P.center_mem hP)).trans
    ((mul_le_mul_of_nonneg_left hside (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (sqrt_dimension_le d) (hP.le.trans hside)))

theorem DyadicCube.comparable_points_separate_cells (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {ℓ : ℝ}
    (hPs : P.side ≤ ℓ) (hQs : Q.side ≤ ℓ)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hlo : 256*((d:ℝ)+1)*ℓ < dist x y)
    (hhi : dist x y ≤ 1024*((d:ℝ)+1)*ℓ) :
    250*((d:ℝ)+1)*ℓ ≤ dist P.center Q.center ∧
      dist P.center Q.center ≤ 1100*((d:ℝ)+1)*ℓ := by
  have hpx := P.point_center_bound hP hPs hx
  have hqy := Q.point_center_bound hQ hQs hy
  have hℓ : 0 < ℓ := hP.trans_le hPs
  have hdim : 0 < ((d:ℝ)+1)*ℓ := by positivity
  have ht₁ := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  have ht₂ := (dist_triangle x P.center y).trans
    (add_le_add (le_refl _) (dist_triangle P.center Q.center y))
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₂
  constructor <;> linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ComparableBands
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Borel dyadic bands for the two original comparable displacements

The finite cover has the exact constants used by the far-cell partner
geometry. Nonnegative integration only needs a cover, so no arbitrary
choice of a depth or additional measurability hypothesis is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem comparableLengthBand_measurable (d b : ℕ) :
    MeasurableSet (comparableLengthBand d b) := by
  have h₁ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.1.1 z.1.2) := by fun_prop
  have h₂ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.2.1 z.2.2) := by fun_prop
  exact ((measurableSet_lt measurable_const h₁).inter
    (measurableSet_le h₁ measurable_const)).inter
    ((measurableSet_lt measurable_const h₂).inter
      (measurableSet_le h₂ measurable_const))

theorem comparableFarRegion_measurable (d a h : ℕ) :
    MeasurableSet (comparableFarRegion d a h) := by
  have h₁ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.1.1 z.1.2) := by fun_prop
  have h₂ : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      dist z.2.1 z.2.2) := by fun_prop
  have hm := h₁.max h₂
  exact (measurableSet_le hm measurable_const).inter
    ((measurableSet_lt measurable_const hm).inter
      ((measurableSet_le hm (measurable_const.mul h₁)).inter
        (measurableSet_le hm (measurable_const.mul h₂))))

theorem comparableLengthBand_dist_lower {d b : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableLengthBand d b) :
    (2:ℝ)^(-(b:ℝ)) ≤ dist z.1.1 z.1.2 ∧
      (2:ℝ)^(-(b:ℝ)) ≤ dist z.2.1 z.2.2 := by
  have hp : 0 ≤ (2:ℝ)^(-(b:ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hd : 1 ≤ 256*((d:ℝ)+1) := by have h := Nat.cast_nonneg (α := ℝ) d; linarith
  have hscale := mul_le_mul_of_nonneg_right hd hp
  exact ⟨(by simpa only [one_mul] using hscale.trans hz.1.1.le),
    (by simpa only [one_mul] using hscale.trans hz.2.1.le)⟩

theorem comparableLengthBand_descendants {d a b : ℕ} (Q : DyadicCube d)
    (hQ : Q.side = 1) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) (hab : a ≤ b)
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableLengthBand d b) :
    (256*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^(b-a)) < dist z.1.1 z.1.2 ∧
      dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^(b-a))) ∧
    (256*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^(b-a)) < dist z.2.1 z.2.2 ∧
      dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^(b-a))) := by
  rwa [descendant_common_band_scale Q hQ X hX hab,
    descendant_common_band_scale Q hQ Y hY hab]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MaskSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Buffered masks retain their good-direction support under differentiation -/

namespace Falconer
open Set MeasureTheory
open scoped Topology

theorem capCutoffAmbient_tsupport_subset {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) :
    tsupport (capCutoffAmbient δ hδ S U) ⊆
      ⋃ c ∈ cutoffCapCenters δ S U, Metric.closedBall (c : Space d) δ := by
  apply closure_minimal _ (isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall))
  intro x hx
  obtain ⟨c,hc,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  apply mem_iUnion₂.mpr ⟨c,hc,?_⟩
  have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hm : x ∈ Metric.ball (c : Space d) δ := by
    change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
    rw [← (capBump δ hδ c).support_eq]
    exact hb
  exact Metric.ball_subset_closedBall hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorAmbientMask_tsupport_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (hw : (w : Space d) ∈ tsupport (descriptorAmbientMask Q ρ m N σ J i b S x)) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro p hp hx
  have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
    ((mem_cubePaths d _ p).mp hp) hx)
  rw [he] at hw
  have hs := capCutoffAmbient_tsupport_subset (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b) hw
  obtain ⟨c,hc,hwc⟩ := Set.mem_iUnion₂.mp hs
  exact (Finset.mem_filter.mp hc).2 w
    (by simpa only [Metric.mem_closedBall,Subtype.dist_eq] using hwc)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizedCellCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

theorem RegularizedProfileData.descendant_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X : CellPath d) (hX : X.length = a) :
    (((Q.descendant X).occupiedPaths ρ (p-a)).card : ℝ) ≤
      ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) := by
  let := h.probability
  let R := (2:ℝ)^N
  let ℓ := ((d:ℝ)+1)*lam
  let lo := R^(-ℓ-m ((p:ℝ)/N))
  let S := (Q.descendant X).occupiedPaths ρ (p-a)
  have hlo : 0 < lo := by dsimp [lo,R]; positivity
  have hmass (z : CellPath d) (hz : z ∈ S) :
      lo ≤ (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    have hz' : z ∈ cubePaths d (p-a) ∧
        0 < ρ ((Q.descendant X).descendant z).carrier := by
      simpa only [S,DyadicCube.occupiedPaths,Finset.mem_filter] using hz
    obtain ⟨hz,hpos⟩ := hz'
    have hlen : (X++z).length = p := by
      simp only [List.length_append,hX,(mem_cubePaths _ _ _).mp hz]
      omega
    have hh := (h.cells p hp (X++z) hlen
      (by simpa only [Q.descendant_append] using hpos)).1
    simpa only [Q.descendant_append,lo,R,ℓ,sub_eq_add_neg,neg_mul,
      Real.rpow_add (by positivity : 0 < (2:ℝ)^N)] using hh
  have he : ρ (Q.descendant X).carrier =
      ∑ z ∈ S, ρ ((Q.descendant X).descendant z).carrier := by
    have hh := congrArg (fun ν : Measure (Space d) => ν univ)
      ((Q.descendant X).restrict_occupiedPaths ρ (p-a))
    simpa only [Measure.restrict_apply_univ,Measure.finsetSum_apply,S] using hh
  have hr : (ρ (Q.descendant X).carrier).toReal =
      ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    rw [he,ENNReal.toReal_sum]
    intro z _
    exact measure_ne_top ρ _
  have hc : (S.card:ℝ)*lo ≤ R^(ℓ-m ((a:ℝ)/N)) := by
    calc
      _ = ∑ _z ∈ S, lo := by simp
      _ ≤ ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal :=
        Finset.sum_le_sum hmass
      _ = (ρ (Q.descendant X).carrier).toReal := hr.symm
      _ ≤ _ := h.cell_mass_upper (hap.trans hp) X hX
  apply (le_div_iff₀ hlo).mpr at hc
  apply hc.trans_eq
  dsimp only [lo,R,ℓ]
  rw [← Real.rpow_sub (by positivity)]
  congr 1
  ring

theorem RegularizedProfileData.pair_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : CellPath d) (hX : X.length = a) (hY : Y.length = a) :
    ((((Q.descendant X).occupiedPaths ρ (p-a)) ×ˢ
      ((Q.descendant Y).occupiedPaths ρ (p-a))).card : ℝ) ≤
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) *
        ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) :=
      mul_le_mul (h.descendant_count hap hp X hX) (h.descendant_count hap hp Y hY)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_NearGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The near part of the independent angular energy

Nearness is imposed on both actual center displacements. Integer grid
packing gives a dimensional degree bound; positive Schur integration then
controls this part by the sum of the original child energies. No angular
localization or separation of the two parent cells is used.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.neighbor_card {d n L : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (a : List (Fin d → Bool)) (ha : a.length = n)
    {τ : ℝ} (hL : τ*((2:ℝ)^n/Q.side) ≤ L) :
    (A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)).card ≤
      (2*L+1)^d := by
  classical
  let T := A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)
  have hinj : Set.InjOn dyadicCode (↑T : Set (List (Fin d → Bool))) := by
    intro p hp q hq he
    exact dyadicCode_injective_at_depth (hA p (Finset.mem_filter.mp hp).1)
      (hA q (Finset.mem_filter.mp hq).1) he
  rw [← Finset.card_image_of_injOn hinj]
  apply grid_ball_card (show 0 < (2:ℝ)^n/Q.side by positivity) hL _ (dyadicCode a)
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp hp
  rwa [← Q.center_sub_eq_grid_sub p a (hA p hp) ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarCellCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only a dimensional number of partners at a comparable far depth -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem card_filtered_pairs_le {α : Type*} [DecidableEq α]
    (S : Finset α) (G : α → α → Prop) [DecidableRel G] (D : ℕ)
    (hD : ∀ x ∈ S, (S.filter (G x)).card ≤ D) :
    ((S ×ˢ S).filter (fun z => G z.1 z.2)).card ≤ S.card*D := by
  have hsub : (S ×ˢ S).filter (fun z => G z.1 z.2) ⊆
      S.biUnion (fun x => (S.filter (G x)).image (fun y => (x,y))) := by
    intro z hz
    obtain ⟨hz,hG⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hz
    exact Finset.mem_biUnion.mpr ⟨z.1,hx,Finset.mem_image.mpr
      ⟨z.2,Finset.mem_filter.mpr ⟨hy,hG⟩,rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S, ((S.filter (G x)).image (fun y => (x,y))).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, D := Finset.sum_le_sum (fun x hx =>
      Finset.card_image_le.trans (hD x hx))
    _ = _ := by simp

theorem farCellPartners_card {d : ℕ} (P : DyadicCube d) (hP : 0 < P.side)
    (ρ : Measure (Space d)) (n : ℕ) :
    (farCellPartners P ρ n).card ≤
      (P.occupiedPaths ρ n).card*(2*(1100*(d+1))+1)^d := by
  let S := P.occupiedPaths ρ n
  have hsub : farCellPartners P ρ n ⊆ (S ×ˢ S).filter (fun z =>
      ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ≤
        1100*((d:ℝ)+1)*P.side/(2:ℝ)^n) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.2⟩
  apply (Finset.card_le_card hsub).trans
  apply card_filtered_pairs_le (P.occupiedPaths ρ n) (fun x y =>
    ‖(P.descendant y).center-(P.descendant x).center‖ ≤
      1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)
  intro x hx
  apply P.neighbor_card hP _
    (fun p hp => (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1) x
    ((mem_cubePaths d n x).mp (Finset.mem_filter.mp hx).1)
  have he : (1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)*((2:ℝ)^n/P.side) =
      (1100*(d+1):ℕ) := by
    push_cast
    field_simp
  exact he.le

theorem farCellPartners_pair_card {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d)) (n : ℕ) :
    ((farCellPartners P μ n) ×ˢ (farCellPartners Q ν n)).card ≤
      (2*(1100*(d+1))+1)^(2*d)*
        (P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n).card := by
  rw [Finset.card_product,Finset.card_product]
  apply (Nat.mul_le_mul (farCellPartners_card P hP μ n) (farCellPartners_card Q hQ ν n)).trans_eq
  rw [Nat.mul_comm 2 d, pow_mul, pow_two]
  ring

theorem farCellPartners_of_comparable_points {d : ℕ} (P : DyadicCube d)
    (hP : 0 < P.side) (ρ : Measure (Space d)) (n : ℕ)
    (u : List (Fin d → Bool) × List (Fin d → Bool))
    (hu : u ∈ P.occupiedPaths ρ n ×ˢ P.occupiedPaths ρ n)
    {x y : Space d} (hx : x ∈ (P.descendant u.1).carrier)
    (hy : y ∈ (P.descendant u.2).carrier)
    (hlo : 256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist x y)
    (hhi : dist x y ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) :
    u ∈ farCellPartners P ρ n := by
  have hu₁ := (mem_cubePaths d n u.1).mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).1
  have hu₂ := (mem_cubePaths d n u.2).mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hu).2).1
  have hs₁ : (P.descendant u.1).side = P.side/(2:ℝ)^n := by
    rw [P.descendant_side,hu₁]
  have hs₂ : (P.descendant u.2).side = P.side/(2:ℝ)^n := by
    rw [P.descendant_side,hu₂]
  have hb := ((P.descendant u.1).comparable_points_separate_cells (P.descendant u.2)
    (P.descendant_side_pos hP _) (P.descendant_side_pos hP _) hs₁.le hs₂.le hx hy hlo hhi)
  apply Finset.mem_filter.mpr
  refine ⟨hu,?_,?_⟩
  · have hs : 0 < P.side/(2:ℝ)^n := by positivity
    rw [dist_eq_norm,norm_sub_rev] at hb
    have hdim : 0 < ((d:ℝ)+1)*(P.side/(2:ℝ)^n) := by positivity
    calc
      _ = 125*((d:ℝ)+1)*(P.side/(2:ℝ)^n) := by ring
      _ ≤ _ := by nlinarith [hb.1]
  · rw [dist_eq_norm,norm_sub_rev] at hb
    exact hb.2.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FourPointPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original four-point partitions before far rebinning

Each internal pair keeps its original two endpoint restrictions. These
identities allow a nonnegative kernel bound to discard a far-label
selection and then repartition at the common comparable-displacement depth.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem DyadicCube.pair_restrict_occupiedPaths {d : ℕ} (P : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ) :
    (μ.restrict P.carrier).prod (μ.restrict P.carrier) =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        (μ.restrict (P.descendant u.1).carrier).prod (μ.restrict (P.descendant u.2).carrier) := by
  rw [P.restrict_occupiedPaths μ n,PlanarFalconer.finite_measure_prod_sum,Finset.sum_product]

theorem originalFourPointMeasure_partition {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    originalFourPointMeasure P Q μ ν =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        ∑ v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n,
          fourPointChildMeasure P Q μ ν u v := by
  rw [originalFourPointMeasure,P.pair_restrict_occupiedPaths μ n,
    Q.pair_restrict_occupiedPaths ν n,PlanarFalconer.finite_measure_prod_sum]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourStationaryPhases
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four actual radial phases in a far spherical product -/

namespace Falconer

theorem stationaryPhase_star (t : ℝ) : star (stationaryPhase t) = stationaryPhase (-t) := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I*(t : ℂ))) = _
  rw [← Complex.exp_conj]
  simp only [stationaryPhase,map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_neg]
  congr 1
  ring

theorem stationaryPhase_mul (s t : ℝ) :
    stationaryPhase s*stationaryPhase t = stationaryPhase (s+t) := by
  rw [stationaryPhase,stationaryPhase,← Complex.exp_add,stationaryPhase]
  congr 1
  push_cast
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskedStationaryJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth fixed-patch extensions of actual stationary jets

The mask is one on the prepared inner cap and vanishes near the antipodal
singularity of the chosen frame. No global spherical differential operator
is assumed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem quadraticJetCoefficient_zero_amplitude (n j : ℕ) :
    quadraticJetCoefficient j (fun _ : Space n => (0 : ℂ)) = 0 := by
  have hz : (Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ)) (fun _ => 0) =
      (fun _ => 0) := InnerProductSpace.laplacian_const
  simp only [quadraticJetCoefficient,Function.iterate_fixed hz,mul_zero]

theorem actualStationaryCoefficient_zero_amplitude (m j : ℕ) (x : Space (m+3)) :
    actualStationaryCoefficient m j (fun _ => 0) x = 0 := by
  have he : (fun u => unmaskedStationaryAmplitude m (fun _ => 0) (x,u)) =
      (fun _ : Space (m+2) => (0 : ℂ)) := by
    funext u
    simp only [unmaskedStationaryAmplitude,mul_zero]
  change quadraticJetCoefficient j _ = 0
  rw [he]
  exact quadraticJetCoefficient_zero_amplitude _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetDerivativeBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds for individual ambient mask jets

These estimates retain the order of each differentiated mask. Evaluation
on fixed unit vectors is a contraction, so differentiating a mask jet costs
only the corresponding higher derivative of that same mask.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem norm_iteratedFDeriv_nested {d : ℕ} (f : Space d → ℝ)
    (k t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ =
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,ih]
    rw [show k+1+t = k+(t+1) by omega]

private theorem jetEvaluation_norm_le {d k : ℕ} (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) : ‖jetEvaluation v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L v‖ ≤ 1*‖L‖
  have hp : (∏ j, ‖v j‖) ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg (v j)) (fun j _ => hv j)
  simpa only [one_mul] using (L.le_opNorm v).trans
    (mul_le_of_le_one_right (norm_nonneg L) hp)

 theorem norm_iteratedFDeriv_jetValue_le {d : ℕ} (f : Space d → ℝ)
    (hf : ContDiff ℝ ∞ f) (k t : ℕ) (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) (z : Space d) :
    ‖iteratedFDeriv ℝ t (fun y => (iteratedFDeriv ℝ k f y) v) z‖ ≤
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  have hfd : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) :=
    hf.iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ t (jetEvaluation v ∘ iteratedFDeriv ℝ k f) z‖ ≤ _
  rw [(jetEvaluation v).iteratedFDeriv_comp_left hfd.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  calc
    _ ≤ ‖jetEvaluation v‖ * ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (jetEvaluation_norm_le v hv)
    _ = _ := norm_iteratedFDeriv_nested f k t z

 theorem descriptorJetValue_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (fun y =>
          (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤
        C * ((descriptorMaskRadius N σ b)⁻¹)^(k+t) := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientMask_global_derivatives d (k+t)
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  exact (norm_iteratedFDeriv_jetValue_le _
    (descriptorAmbientMask_contDiff Q ρ m N σ J i b S x) k t v hv z).trans
    (hbound Q ρ m N σ J i b S hsep x z)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NormalizedJetDerivatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized ambient derivatives of a single mask -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem normalizedAmbientDescriptorJet_contDiff {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) :
    ContDiff ℝ ∞ (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) := by
  exact contDiff_const.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))

 theorem normalizedAmbientDescriptorJet_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          C * ((descriptorMaskRadius N σ b)⁻¹)^t := by
  obtain ⟨C,hC,hbound⟩ := descriptorJetValue_derivatives d k t
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  have hr := descriptorMaskRadius_pos N σ b
  have hf : ContDiff ℝ ∞ (fun y =>
      (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  change ‖iteratedFDeriv ℝ t (fun y => (descriptorMaskRadius N σ b)^k •
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le k)]
  calc
    _ ≤ (descriptorMaskRadius N σ b)^k * (C*((descriptorMaskRadius N σ b)⁻¹)^(k+t)) :=
      mul_le_mul_of_nonneg_left (hbound Q ρ m N σ J i b S hsep v hv x z) (pow_nonneg hr.le k)
    _ = C*((descriptorMaskRadius N σ b)⁻¹)^t := by
      rw [pow_add]
      calc
        _ = ((descriptorMaskRadius N σ b)*(descriptorMaskRadius N σ b)⁻¹)^k *
            (C*((descriptorMaskRadius N σ b)⁻¹)^t) := by rw [mul_pow]; ring
        _ = _ := by rw [mul_inv_cancel₀ hr.ne',one_pow,one_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_UniformJetBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed derivative budget for each normalized mask jet

One constant is selected before all scales and descriptor lists. Only the
sum of actual derivative orders pays an amplitude cost.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem normalizedAmbientDescriptorJet_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ D : ℝ, 1 ≤ D → (descriptorMaskRadius N σ b)⁻¹ ≤ D →
      ∀ k ≤ K, ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ t ≤ L, ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          A^(k+t)*D^t := by
  classical
  choose C hC hbound using fun k t => normalizedAmbientDescriptorJet_derivatives d k t
  let A := 1+∑ p ∈ (Finset.range (K+1)).product (Finset.range (L+1)), C p.1 p.2
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2))
  have hCA (k t : ℕ) (hk : k ≤ K) (ht : t ≤ L) : C k t ≤ A := by
    have hp : (k,t) ∈ (Finset.range (K+1)).product (Finset.range (L+1)) :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
    have hh := Finset.single_le_sum
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2) hp
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨A,hA,?_⟩
  intro Q ρ m N σ J i b S hsep D hD hscale k hk v hv t ht x z
  by_cases hzero : k+t = 0
  · have hk0 : k = 0 := by omega
    have ht0 : t = 0 := by omega
    subst k
    subst t
    simp only [norm_iteratedFDeriv_zero,normalizedAmbientDescriptorJet,pow_zero,
      iteratedFDeriv_zero_apply,one_mul,zero_add]
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b S x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · apply (hbound k t Q ρ m N σ J i b S hsep v hv x z).trans
    exact mul_le_mul ((hCA k t hk ht).trans (le_self_pow₀ hA hzero))
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) hscale t)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) t)
      (pow_nonneg (zero_le_one.trans hA) (k+t))


private theorem weighted_jet_product_bound {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (F : Finset ι) (f : ι → E → ℝ) (c : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (L : ℕ) (z : E) (hc : ∀ i ∈ F, 0 ≤ c i)
    (hf : ∀ i ∈ F, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f i) z‖ ≤ c i*D^t) :
    ∀ t ≤ L, ‖iteratedFDeriv ℝ t (fun w => ∏ i ∈ F, f i w) z‖ ≤
      (∏ i ∈ F, c i)*((F.card:ℝ)*D)^t := by
  induction F using Finset.induction_on with
  | empty =>
    intro t _
    cases t with
    | zero => simp
    | succ t => simp [iteratedFDeriv_succ_const]
  | @insert i F hi ih =>
    have hcF : ∀ j ∈ F, 0 ≤ c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hfF : ∀ j ∈ F, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbF : ∀ j ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f j) z‖ ≤ c j*D^t :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hih := ih hcF hfF hbF
    intro t ht
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hff : ContDiff ℝ ∞ (fun w => ∏ j ∈ F, f j w) := contDiff_prod hfF
    simp only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfi hff z (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (t:ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*(c i*D^q)*
          ((∏ j ∈ F, c j)*((F.card:ℝ)*D)^(t-q)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqt : q ≤ t := by have := Finset.mem_range.mp hq; omega
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb i (Finset.mem_insert_self _ _) q (hqt.trans ht))
            (Nat.cast_nonneg _))
          (hih (t-q) ((Nat.sub_le _ _).trans ht)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hc i (Finset.mem_insert_self _ _))
            (pow_nonneg hD _)))
      _ = (c i*(∏ j ∈ F, c j)) *
          (∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*D^q*((F.card:ℝ)*D)^(t-q)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = (c i*(∏ j ∈ F, c j))*(D+(F.card:ℝ)*D)^t := by
        congr 1
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = _ := by congr 2; ring

 theorem normalizedAmbientJetProduct_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type*} (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
      (b : ι → PlanarFalconer.PolicyDescriptor) (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
      (k : ι → ℕ) (v : (j : ι) → Fin (k j) → Space d),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z → descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K → (∀ j ∈ F, ∀ t, ‖v j t‖ ≤ 1) →
      ∀ D : ℝ, 1 ≤ D → (∀ j ∈ F, (descriptorMaskRadius N σ (b j))⁻¹ ≤ D) →
      ∀ x z t, t ≤ L →
        ‖iteratedFDeriv ℝ t (fun w => ∏ j ∈ F,
          normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x w) z‖ ≤
        A^K*((F.card:ℝ)*A*D)^t := by
  classical
  obtain ⟨A,hA,hbound⟩ := normalizedAmbientDescriptorJet_uniform_budget d K L
  refine ⟨A,hA,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv D hD hscale x z t ht
  have hb : ∀ j ∈ F, ∀ q ≤ L,
      ‖iteratedFDeriv ℝ q
        (normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x) z‖ ≤
        A^(k j)*(A*D)^q := by
    intro j hj q hq
    have hk : k j ≤ K := (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) hj).trans horder
    convert hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) D hD (hscale j hj)
      (k j) hk (v j) (hv j hj) q hq x z using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_add,mul_pow]
    ring
  have h := weighted_jet_product_bound F
    (fun j => normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    (fun j => A^(k j)) (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hD)) L z
    (fun j _ => pow_nonneg (zero_le_one.trans hA) _)
    (fun j _ => normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    hb t ht
  rw [Finset.prod_pow_eq_pow_sum] at h
  apply h.trans
  have hAK := pow_le_pow_right₀ hA horder
  calc
    _ = A^(∑ j ∈ F, k j)*((F.card:ℝ)*A*D)^t := by rw [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hAK (pow_nonneg (by positivity) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient representatives of the exact recursive symbols

The bound is uniform in the descriptor list and scale. It retains the
ambient representative needed for the full-sphere far expansion.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem iteratedFDeriv_mul_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {B C D E : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (t : ℕ) (x : V)
    (hb : ∀ j ≤ t, ‖iteratedFDeriv ℝ j f x‖ ≤ B*D^j)
    (hc : ∀ j ≤ t, ‖iteratedFDeriv ℝ j g x‖ ≤ C*E^j) :
    ‖iteratedFDeriv ℝ t (fun x => f x*g x) x‖ ≤ (B*C)*(D+E)^t := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (t : ℕ∞ω) ≤ ∞)
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*(B*D^j)*(C*E^(t-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb j hjt) (Nat.cast_nonneg _))
        (hc (t-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (pow_nonneg hD _)))
    _ = (B*C)*(∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*D^j*E^(t-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (B*C)*(D+E)^t := by
      congr 1
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring


namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

 theorem ambient_smooth (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) :
    ContDiff ℝ ∞ (f.ambient Q ρ m N σ J i S A x) := by
  apply contDiff_const.mul
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_prod (fun b _ =>
    normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x))).mul f.angular_smooth

end DescriptorJetSymbol

 theorem exists_descriptorJetSymbol_ambient_budget (n K L : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol n K L F Dq) (x : Space (n+2)) (t : ℕ), t ≤ L →
      ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (f.ambient Q ρ m N σ J i S A x) w‖ ≤
          (B^K*A⁻¹)*(E+Dq)^t := by
  classical
  obtain ⟨B,hB,hjet⟩ := normalizedAmbientJetProduct_uniform_budget (n+2) K L
  refine ⟨B,hB,?_⟩
  intro F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x t ht w
  let P : Space (n+2) → ℝ := fun z => ∏ b ∈ F,
    normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z
  have hP : ContDiff ℝ ∞ P := contDiff_prod (fun b _ =>
    normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x)
  have hPc : ContDiff ℝ ∞ (fun z => (P z : ℂ)) := Complex.ofRealCLM.contDiff.comp hP
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ (F.card:ℝ)*B*Dmask).trans hE
  have hp (j : ℕ) (hj : j ≤ t) :
      ‖iteratedFDeriv ℝ j (fun z => (P z : ℂ)) w‖ ≤ B^K*E^j := by
    have he := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (hP.contDiffAt (x := (w:Space (n+2)))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (j:ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ P) w‖ ≤ _
    rw [he]
    exact (hjet Q ρ m N σ J i F id S (fun b => (f.jet b).order)
      (fun b => (f.jet b).vectors) hsep f.order_le (fun b _ => (f.jet b).norm_vectors)
      Dmask hDm hscale x w j (hj.trans ht)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hE j) (by positivity))
  have hpq := iteratedFDeriv_mul_bound (fun z => (P z : ℂ)) f.angular hPc f.angular_smooth
    (by positivity : 0 ≤ B^K) (by norm_num : (0:ℝ) ≤ 1) hE0 hDq t (w:Space (n+2)) hp
    (fun j hj => by simpa only [one_mul] using f.angular_derivative j (hj.trans ht) w)
  have hq : ContDiff ℝ ∞ (fun z => (P z : ℂ)*f.angular z) := hPc.mul f.angular_smooth
  change ‖iteratedFDeriv ℝ t (fun z => (f.spatial x*(A⁻¹:ℝ)) •
    ((P z : ℂ)*f.angular z)) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hq.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,norm_smul]
  have hs : ‖f.spatial x*(A⁻¹:ℝ)‖ ≤ A⁻¹ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hA)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_pos.mpr hA).le
  apply (mul_le_mul hs hpq (norm_nonneg _) (inv_pos.mpr hA).le).trans_eq
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual stationary amplitudes retain every old descriptor

The far expansion uses these internal endpoint pairs before any reached
mask is removed. Locality of the stationary operator preserves the old
support tests, also for already differentiated masks.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

 theorem ambient_eventually_zero (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2))
    {b : PolicyDescriptor} (hb : b ∈ F)
    (hbad : (x,w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b) :
    f.ambient Q ρ m N σ J i S A x =ᶠ[𝓝 (w:Space (n+2))] 0 := by
  have hnot : (w:Space (n+2)) ∉ tsupport (descriptorAmbientMask Q ρ m N σ J i b (S b) x) :=
    fun h => hbad (descriptorAmbientMask_tsupport_good Q ρ m N σ J i b (S b) x w h)
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).iteratedFDeriv (𝕜 := ℝ) (f.jet b).order
  filter_upwards [hz] with z hz
  have hj : normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z = 0 := by
    simp only [normalizedAmbientDescriptorJet,hz,iteratedFDeriv_zero,Pi.zero_apply,zero_apply,mul_zero]
  have hp : (∏ c ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i c (S c)
      (f.jet c).order (f.jet c).vectors x z) = 0 := Finset.prod_eq_zero hb hj
  simp only [ambient,hp,Complex.ofReal_zero,zero_mul,mul_zero,Pi.zero_apply]

 theorem pairAmbient_smooth (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y : Space (n+2)) :
    ContDiff ℝ ∞ (f.pairAmbient Q ρ m N σ J i S A x y) :=
  (f.ambient_smooth Q ρ m N σ J i S A x).mul
    (Complex.conjCLE.contDiff.comp (f.ambient_smooth Q ρ m N σ J i S A y))

 theorem pair_stationary_support {m₀ : ℕ}
    (f : DescriptorJetSymbol (m₀+1) K L F Dq)
    (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3)))
    (A : ℝ) (x y : Space (m₀+3)) (w : Sphere (m₀+3)) (j : ℕ)
    (hne : actualStationaryCoefficient m₀ j (f.pairAmbient Q ρ m N σ J i S A x y) w ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro b hb
  constructor
  · by_contra hbad
    have hz := f.ambient_eventually_zero Q ρ m N σ J i S A x w hb hbad
    have he : f.pairAmbient Q ρ m N σ J i S A x y =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      simp only [pairAmbient,hz,Pi.zero_apply,zero_mul]
    have hlocal := actualStationaryCoefficient_local m₀ j w he
    exact hne (hlocal.trans (actualStationaryCoefficient_zero_amplitude m₀ j w))
  · by_contra hbad
    have hz := f.ambient_eventually_zero Q ρ m N σ J i S A y w hb hbad
    have he : f.pairAmbient Q ρ m N σ J i S A x y =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      simp only [pairAmbient,hz,Pi.zero_apply,star_zero,mul_zero]
    have hlocal := actualStationaryCoefficient_local m₀ j w he
    exact hne (hlocal.trans (actualStationaryCoefficient_zero_amplitude m₀ j w))

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateAntipodal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The incoming stationary pole retains the same descriptor tests -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped Topology

 theorem perpendicularPart_neg_direction {d : ℕ} (w v : Space d) :
    perpendicularPart (-w) v = perpendicularPart w v := by
  simp [perpendicularPart,inner_neg_left]

 theorem finiteTubeCount_opposite {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    finiteTubeCount S v W (oppositePole w) = finiteTubeCount S v W w := by
  classical
  unfold finiteTubeCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [angularTubeEvent,Set.mem_ofPred_eq,oppositePole_coe,
    perpendicularPart_neg_direction]

 theorem projectionCollision_neg_direction {d : ℕ} (μ : Measure (Space d))
    (w : Space d) (W : ℝ) : projectionCollision μ (-w) W = projectionCollision μ w W := by
  simp only [projectionCollision,inner_neg_right,abs_neg]

 theorem descriptorGoodDirections_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (P : List (Fin d → Bool)) (b : PolicyDescriptor)
    (w : Sphere d) :
    oppositePole w ∈ descriptorGoodDirections Q ρ m N σ J i P b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i P b := by
  classical
  cases b with
  | parallel g p =>
    simp only [descriptorGoodDirections,Regularization.parallelGoodSet]
    split_ifs <;> simp only [mem_ofPred_eq,Regularization.parallelTestCount,
      finiteTubeCount_opposite,mem_empty_iff_false]
  | projection p t =>
    simp only [descriptorGoodDirections,Regularization.conditionalProjectionGoodSet]
    split_ifs <;> simp only [projectionGoodSet,mem_ofPred_eq,oppositePole_coe,
      projectionCollision_neg_direction,mem_empty_iff_false]

 theorem descriptorEndpointGood_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Space d) (w : Sphere d) :
    (x,oppositePole w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b := by
  simp only [descriptorEndpointGood,mem_ofPred_eq,descriptorGoodDirections_opposite]

 theorem DescriptorJetSymbol.pair_incoming_stationary_support {m₀ K L : ℕ}
    {F : Finset PolicyDescriptor} {Dq : ℝ} (f : DescriptorJetSymbol (m₀+1) K L F Dq)
    (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3)))
    (A : ℝ) (x y : Space (m₀+3)) (w : Sphere (m₀+3)) (j : ℕ)
    (hne : actualStationaryCoefficient m₀ j
      (antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y)) w ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  have hneg : Filter.Tendsto (fun z : Space (m₀+3) => -z)
      (𝓝 (w:Space (m₀+3))) (𝓝 (oppositePole w:Space (m₀+3))) :=
    continuous_neg.continuousAt
  intro b hb
  constructor
  · by_contra hbad
    have hbad' : (x,oppositePole w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b :=
      fun h => hbad ((descriptorEndpointGood_opposite Q ρ m N σ J (i+1) b x w).mp h)
    have hz := (f.ambient_eventually_zero Q ρ m N σ J i S A x (oppositePole w) hb hbad').comp_tendsto hneg
    have he : antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y) =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      change f.ambient Q ρ m N σ J i S A x (-z) = 0 at hz
      simp only [antipodalConjugate,DescriptorJetSymbol.pairAmbient,hz,Pi.zero_apply,zero_mul,star_zero]
    exact hne ((actualStationaryCoefficient_local m₀ j w he).trans
      (actualStationaryCoefficient_zero_amplitude m₀ j w))
  · by_contra hbad
    have hbad' : (y,oppositePole w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b :=
      fun h => hbad ((descriptorEndpointGood_opposite Q ρ m N σ J (i+1) b y w).mp h)
    have hz := (f.ambient_eventually_zero Q ρ m N σ J i S A y (oppositePole w) hb hbad').comp_tendsto hneg
    have he : antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y) =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      change f.ambient Q ρ m N σ J i S A y (-z) = 0 at hz
      simp only [antipodalConjugate,DescriptorJetSymbol.pairAmbient,hz,Pi.zero_apply,star_zero,mul_zero]
    exact hne ((actualStationaryCoefficient_local m₀ j w he).trans
      (actualStationaryCoefficient_zero_amplitude m₀ j w))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FarRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay for spherical stationary coefficients

Scalar compact-support integration by parts gives decay for the stationary
coefficient, with the dimensional gain of the full ambient sphere.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem actualStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ e : Sphere (m+3), ‖actualStationaryCoefficient m j B e‖ ≤ H*C*D^(2*j) := by
  obtain ⟨L,hL,hbound⟩ := pole_quadratic_amplitude_budget m (2*j)
  let q : ℂ := sphereStationaryConstant (m+2)/((2*Complex.I)^j*(j.factorial:ℂ))
  refine ⟨‖q‖*((m+2:ℕ):ℝ)^j*L,by positivity,?_⟩
  intro B hB C D hC hD hb e
  let a : Space (m+2) → ℂ := quadraticAmplitude m
    (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))
  have ha : ContDiff ℝ ∞ a := poleLocalized_quadratic_contDiff m e hB
  have hc : actualStationaryCoefficient m j B e = quadraticJetCoefficient j a := by
    dsimp [a]
    rw [← actualStationaryCoefficient_eq m j (poleLocalizedAmbient e B) e,
      poleLocalizedAmbient_coefficient]
  have hΔ := euclidean_iterated_laplacian_derivative_bound ha j 0 (0:Space (m+2))
  simp only [norm_iteratedFDeriv_zero] at hΔ
  have h0 := hbound e B hB C D hC hD hb (0+2*j) (by omega) 0
  have htotal := hΔ.trans (mul_le_mul_of_nonneg_left h0 (by positivity))
  rw [hc,quadraticJetCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_left htotal (norm_nonneg q)).trans_eq (by ring)

 theorem normalizedStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ e : Sphere (m+3), ‖normalizedStationaryCoefficient m j Λ B e‖ ≤ H*C := by
  obtain ⟨H,hH,hb⟩ := actualStationaryCoefficient_bound m j
  refine ⟨H,hH,?_⟩
  intro B hB C D Λ hC hD hΛ hscale hder e
  rw [normalizedStationaryCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hΛ.le _))]
  have hpow : D^(2*j) ≤ Λ^j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hscale j
  calc
    _ ≤ (Λ^j)⁻¹*(H*C*D^(2*j)) :=
      mul_le_mul_of_nonneg_left (hb B hB C D hC hD hder e) (by positivity)
    _ ≤ (Λ^j)⁻¹*(H*C*Λ^j) := by gcongr
    _ = H*C := by field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SignedStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual stationary signs and their radial scaling

The incoming coefficient is the conjugate coefficient of the antipodal
amplitude. Both signs use the original amplitude derivative budget.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem signedStationaryCoefficient_bound (m j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ (e : Sphere (m+3)) (outgoing : Bool),
        ‖signedStationaryCoefficient m j Λ B e outgoing‖ ≤ H*C := by
  obtain ⟨H,hH,hb⟩ := normalizedStationaryCoefficient_bound m j
  refine ⟨H,hH,?_⟩
  intro B hB C D Λ hC hD hΛ hscale hder e outgoing
  cases outgoing with
  | false =>
    simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false, if_false,norm_star]
    apply hb (antipodalConjugate B) (antipodalConjugate_contDiff hB)
      C D Λ hC hD hΛ hscale
    intro t ht w
    rw [antipodalConjugate_derivative_norm]
    exact hder t ht (oppositePole w)
  | true =>
    exact hb B hB C D Λ hC hD hΛ hscale hder e

theorem normalizedStationaryCoefficient_scale (m j : ℕ) (R d s : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    normalizedStationaryCoefficient m j (R*s*d) B e =
      ((s^j)⁻¹:ℝ)*normalizedStationaryCoefficient m j (R*d) B e := by
  have hp : (R*s*d)^j = s^j*(R*d)^j := by ring
  simp only [normalizedStationaryCoefficient,hp,mul_inv_rev,Complex.ofReal_mul]
  ring

theorem signedStationaryCoefficient_scale (m j : ℕ) (R d s : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (outgoing : Bool) :
    signedStationaryCoefficient m j (R*s*d) B e outgoing =
      ((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d) B e outgoing := by
  cases outgoing <;>
    simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
      normalizedStationaryCoefficient_scale,star_mul']
  rw [show star (((s^j)⁻¹:ℝ):ℂ) = (((s^j)⁻¹:ℝ):ℂ) from Complex.conj_ofReal _]

theorem directStationarySum_normalized (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    directStationarySum m J Λ B e =
      ∑ j ∈ Finset.range J, normalizedStationaryCoefficient m j Λ B e := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [normalizedStationaryCoefficient,Real.rpow_neg hΛ.le,Real.rpow_natCast]

theorem stationarySphereApprox_signed (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    stationarySphereApprox m J Λ B e =
      ((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*
        (stationaryPhase Λ*(∑ j ∈ Finset.range J, signedStationaryCoefficient m j Λ B e true)+
          stationaryPhase (-Λ)*(∑ j ∈ Finset.range J, signedStationaryCoefficient m j Λ B e false)) := by
  rw [stationarySphereApprox,directStationarySum_normalized m J hΛ,
    directStationarySum_normalized m J hΛ]
  simp only [signedStationaryCoefficient,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,neg_div]
  change ((Λ^(-(((m+2:ℕ):ℝ)/2)):ℝ):ℂ)*
    (stationaryPhase Λ*_+star (stationaryPhase Λ*_)) = _
  rw [star_mul',stationaryPhase_star,star_sum]

theorem DescriptorJetSymbol.signed_stationary_support {m K L : ℕ}
    {F : Finset PlanarFalconer.PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : MeasureTheory.Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x y : Space (m+3)) (w : Sphere (m+3)) (j : ℕ) (Λ : ℝ) (outgoing : Bool)
    (hne : signedStationaryCoefficient m j Λ
      (f.pairAmbient Q ρ profile N σ J i S A x y) w outgoing ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b := by
  cases outgoing with
  | false =>
    apply f.pair_incoming_stationary_support Q ρ profile N σ J i S A x y w j
    intro hz
    exact hne (by simp only [signedStationaryCoefficient,Bool.false_eq_true,ite_false, if_false,
      normalizedStationaryCoefficient,hz,mul_zero,star_zero])
  | true =>
    apply f.pair_stationary_support Q ρ profile N σ J i S A x y w j
    intro hz
    exact hne (by simp only [signedStationaryCoefficient,ite_true, if_true,
      normalizedStationaryCoefficient,hz,mul_zero])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SignedRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay with both actual stationary signs

The two Boolean indices are the outgoing and incoming terms of the full
sphere expansion. The original amplitude remains the argument in all
four cases; antipodal conjugation is internal to its signed coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem stationarySign_cases (outgoing : Bool) :
    stationarySign outgoing = 1 ∨ stationarySign outgoing = -1 := by
  cases outgoing <;> simp [stationarySign]

theorem signed_radial_kernel (m j k : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B G : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ContDiff ℝ ∞ G →
      ∀ C E D R d₁ d₂ : ℝ, 0 ≤ C → 0 ≤ E → 1 ≤ D →
      0 < R → 0 < d₁ → 0 < d₂ → D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      (∀ t ≤ 2*k, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t G w‖ ≤ E*D^t) →
      ∀ (e f : Sphere (m+3)) (ε η : Bool),
      ‖PlanarFalconer.radialPhaseIntegral (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η)
        (R*(stationarySign ε*d₁+stationarySign η*d₂))‖ ≤
      H*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  obtain ⟨Hj,hHj,hj⟩ := signedStationaryCoefficient_bound m j
  obtain ⟨Hk,hHk,hk⟩ := signedStationaryCoefficient_bound m k
  obtain ⟨P,hP,hprofile⟩ := PlanarFalconer.radialStationaryProfile_derivatives hΨ hs
    (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) 2
  refine ⟨15*(Hj*Hk*P),by positivity,?_⟩
  intro B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂ hb hg e f ε η
  let S := (R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let a := signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul
    (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _)
  have has : tsupport a ⊆ Icc (1/4:ℝ) 4 :=
    tsupport_mul_subset_right.trans (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcoeff : ‖signedStationaryCoefficient m j (R*d₁) B e ε*
      signedStationaryCoefficient m k (R*d₂) G f η‖ ≤ (Hj*C)*(Hk*E) := by
    rw [norm_mul]
    exact mul_le_mul (hj B hB C D (R*d₁) hC hD (mul_pos hR hd₁) hD₁ hb e ε)
      (hk G hG E D (R*d₂) hE hD (mul_pos hR hd₂) hD₂ hg f η)
      (norm_nonneg _) (mul_nonneg hHj hC)
  have hab (l : ℕ) (hl : l ≤ 2) (s : ℝ) :
      ‖iteratedDeriv l a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    change ‖iteratedDeriv l (fun t => ((S:ℂ)*
      (signedStationaryCoefficient m j (R*d₁) B e ε*
        signedStationaryCoefficient m k (R*d₂) G f η))*
          PlanarFalconer.radialStationaryProfile Ψ _ t) s‖ ≤ _
    rw [iteratedDeriv_const_mul_field,norm_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS]
    calc
      _ ≤ (S*((Hj*C)*(Hk*E)))*P :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoeff hS)
          (hprofile l hl s) (norm_nonneg _)
          (mul_nonneg hS (mul_nonneg (mul_nonneg hHj hC) (mul_nonneg hHk hE)))
      _ = _ := by ring
  have hzero (s : ℝ) : ‖a s‖ ≤ (Hj*Hk*P*C*E)*S := by
    simpa only [iteratedDeriv_zero] using hab 0 (by omega) s
  have h := PlanarFalconer.angular_radial_kernel_bound ha has (by positivity) hS
    hR.le hd₁.le hd₂.le (stationarySign_cases ε) (stationarySign_cases η) hzero (hab 2 le_rfl)
  apply h.trans_eq
  dsimp [S]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_StationaryRadialSum
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite radial expansion of the two full-sphere approximants -/

namespace Falconer
open Set MeasureTheory

theorem stationarySphereApprox_pole_sum (m J : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    stationarySphereApprox m J Λ B e =
      ∑ ε : Bool, ∑ j ∈ Finset.range J, stationaryPoleTerm m j Λ B e ε := by
  rw [stationarySphereApprox_signed m J hΛ]
  simp only [Fintype.sum_bool,stationaryPoleTerm,stationarySign,Bool.false_eq_true,
    ite_true, if_true,ite_false, if_false,neg_one_mul,one_mul,Finset.mul_sum,mul_add]
  ring_nf

theorem stationaryPoleTerm_radial_product (m j k : ℕ) (Ψ : ℝ → ℝ)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ s : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hs : 0 < s)
    (ε η : Bool) :
    (Ψ s:ℂ)*stationaryPoleTerm m j (R*s*d₁) B e ε*
      stationaryPoleTerm m k (R*s*d₂) G f η =
    stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s := by
  let p : ℝ := ((m+2:ℕ):ℝ)/2
  have hpow (d : ℝ) (hd : 0 < d) : (R*s*d)^(-p) = (R*d)^(-p)*s^(-p) := by
    rw [show R*s*d = (R*d)*s by ring,Real.mul_rpow (mul_pos hR hd).le hs.le]
  have hpowers : s^(-p)*(s^j)⁻¹*s^(-p)*(s^k)⁻¹ =
      s^(-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ)) := by
    rw [← Real.rpow_natCast s j,← Real.rpow_neg hs.le,
      ← Real.rpow_natCast s k,← Real.rpow_neg hs.le,
      ← Real.rpow_add hs,← Real.rpow_add hs,← Real.rpow_add hs]
    congr 1
    dsimp [p]
    ring
  have hphase : stationaryPhase (stationarySign ε*(R*s*d₁))*
      stationaryPhase (stationarySign η*(R*s*d₂)) =
      stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s) := by
    rw [stationaryPhase_mul]
    congr 1
    ring
  simp only [stationaryPoleTerm,neg_div]
  change (Ψ s:ℂ)*
    ((((R*s*d₁)^(-p):ℝ):ℂ)*stationaryPhase (stationarySign ε*(R*s*d₁))*
      signedStationaryCoefficient m j (R*s*d₁) B e ε)*
    ((((R*s*d₂)^(-p):ℝ):ℂ)*stationaryPhase (stationarySign η*(R*s*d₂))*
      signedStationaryCoefficient m k (R*s*d₂) G f η) = _
  rw [hpow d₁ hd₁,hpow d₂ hd₂,
    signedStationaryCoefficient_scale,signedStationaryCoefficient_scale]
  have halgebra : (Ψ s:ℂ)*
      ((((R*d₁)^(-p)*s^(-p):ℝ):ℂ)*stationaryPhase (stationarySign ε*(R*s*d₁))*
        (((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d₁) B e ε))*
      ((((R*d₂)^(-p)*s^(-p):ℝ):ℂ)*stationaryPhase (stationarySign η*(R*s*d₂))*
        (((s^k)⁻¹:ℝ)*signedStationaryCoefficient m k (R*d₂) G f η)) =
      (stationaryPhase (stationarySign ε*(R*s*d₁))*
        stationaryPhase (stationarySign η*(R*s*d₂)))*
      (((R*d₁)^(-p)*(R*d₂)^(-p):ℝ):ℂ)*
      (signedStationaryCoefficient m j (R*d₁) B e ε*
        signedStationaryCoefficient m k (R*d₂) G f η)*
      ((Ψ s*(s^(-p)*(s^j)⁻¹*s^(-p)*(s^k)⁻¹):ℝ):ℂ) := by
    push_cast
    ring
  rw [halgebra,hphase,hpowers]
  dsimp only [signedRadialCoefficient,PlanarFalconer.radialStationaryProfile,p]
  push_cast
  ring_nf

theorem stationarySphereApprox_radial_sum (m J : ℕ) (Ψ : ℝ → ℝ)
    (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (s : ℝ) :
    (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d₁) B e*
      stationarySphereApprox m J (R*s*d₂) G f =
    ∑ ε : Bool, ∑ j ∈ Finset.range J, ∑ η : Bool, ∑ k ∈ Finset.range J,
      stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
        signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s := by
  by_cases hs : 0 < s
  · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd₁),
      stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd₂)]
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ε _
    conv_lhs => lhs; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro k _
    exact stationaryPoleTerm_radial_product m j k Ψ B G e f hR hd₁ hd₂ hs ε η
  · have hz : Ψ s = 0 := by
      by_contra hn
      have hp := (hsupp s hn).1
      linarith
    simp only [hz,Complex.ofReal_zero,zero_mul,signedRadialCoefficient,
      PlanarFalconer.radialStationaryProfile,mul_zero,Complex.ofReal_zero,
      Finset.sum_const_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full-sphere expansion for the actual far-state amplitudes

All angular factors are the original normalized descriptor jets. The
constants precede the scale and list, while each pair keeps both endpoints.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_descriptorJetSymbol_pair_budget (n K L : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol n K L F Dq) (x y : Space (n+2)) (t : ℕ), t ≤ L →
      ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (f.pairAmbient Q ρ m N σ J i S A x y) w‖ ≤
          (B^K*A⁻¹)^2*(2*(E+Dq))^t := by
  obtain ⟨B,hB,hbound⟩ := exists_descriptorJetSymbol_ambient_budget n K L
  refine ⟨B,hB,?_⟩
  intro F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x y t ht w
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ (F.card:ℝ)*B*Dmask).trans hE
  have hD : 0 ≤ E+Dq := add_nonneg hE0 hDq
  have hC : 0 ≤ B^K*A⁻¹ := by positivity
  have hb (x : Space (n+2)) (j : ℕ) (hj : j ≤ t) :=
    hbound F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x j (hj.trans ht) w
  have hc (j : ℕ) (hj : j ≤ t) :
      ‖iteratedFDeriv ℝ j (fun z => star (f.ambient Q ρ m N σ J i S A y z)) w‖ ≤
        (B^K*A⁻¹)*(E+Dq)^j := by
    have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left
      (f.ambient Q ρ m N σ J i S A y) (w:Space (n+2)) j
    exact he.le.trans (hb y j hj)
  have h := iteratedFDeriv_mul_bound _ _ (f.ambient_smooth Q ρ m N σ J i S A x)
    (Complex.conjCLE.contDiff.comp (f.ambient_smooth Q ρ m N σ J i S A y))
    hC hC hD hD t (w:Space (n+2)) (hb x) hc
  have he : (fun z => f.ambient Q ρ m N σ J i S A x z *
      (Complex.conjCLE ∘ f.ambient Q ρ m N σ J i S A y) z) =
      f.pairAmbient Q ρ m N σ J i S A x y := rfl
  rw [he] at h
  simpa only [sq,two_mul] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarRegionScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform shell regimes throughout the actual far region -/

namespace Falconer
open Set MeasureTheory

 theorem far_band_frequency_mono {b h t : ℕ} (hb : b ≤ h+6) {D : ℝ}
    (hD : D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ))) :
    D^2 ≤ (2:ℝ)^((t:ℝ)-b) := by
  apply hD.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hcast : (b:ℝ) ≤ (h+6:ℕ) := by exact_mod_cast hb
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FarRadialIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The radial integral of the full two-sphere stationary expansion

Every sign and coefficient is retained. Only finite sums and the scalar
change of radial variable are used to pass from the pointwise expansion
to the comparable-displacement kernel.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem signedRadialCoefficient_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m j k : ℕ) (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    (R d₁ d₂ ξ : ℝ) (ε η : Bool) :
    Integrable (fun s : ℝ => stationaryPhase (ξ*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s) := by
  have hc : HasCompactSupport
      (PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)-(j:ℝ)-(k:ℝ))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η) :=
    continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by unfold stationaryPhase; fun_prop :
    Continuous (fun s : ℝ => stationaryPhase (ξ*s))).mul hcont).integrable_of_hasCompactSupport
      hc.mul_left.mul_left

theorem full_stationary_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B G : Space (m+3) → ℂ) (e f : Sphere (m+3))
    {R d₁ d₂ : ℝ} (hR : 0 < R) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
      stationarySphereApprox m J (r*d₂) G f) =
    ∑ ε : Bool, ∑ j ∈ Finset.range J, ∑ η : Bool, ∑ k ∈ Finset.range J,
      PlanarFalconer.radialPhaseIntegral (signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η)
        (R*(stationarySign ε*d₁+stationarySign η*d₂)) := by
  let H := fun (ε : Bool) (j : ℕ) (η : Bool) (k : ℕ) (s : ℝ) =>
    stationaryPhase ((R*(stationarySign ε*d₁+stationarySign η*d₂))*s)*
      signedRadialCoefficient m j k Ψ B G e f R d₁ d₂ ε η s
  have hi (ε : Bool) (j : ℕ) (η : Bool) (k : ℕ) : Integrable (H ε j η k) :=
    signedRadialCoefficient_integrable hΨ hs m j k B G e f R d₁ d₂ _ ε η
  calc
    _ = ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d₁) B e*
        stationarySphereApprox m J (R*s*d₂) G f := by
      have hh := Measure.integral_comp_mul_left
        (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
          stationarySphereApprox m J (r*d₂) G f) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
        abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ ε : Bool, ∑ j ∈ Finset.range J,
        ∑ η : Bool, ∑ k ∈ Finset.range J, H ε j η k s := by
      apply integral_congr_ae
      filter_upwards with s
      exact stationarySphereApprox_radial_sum m J Ψ hs B G e f hR hd₁ hd₂ s
    _ = _ := by
      rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k))))]
      apply Finset.sum_congr rfl
      intro ε _
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k)))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun η _ => integrable_finsetSum _ (fun k _ => hi ε j η k))]
      apply Finset.sum_congr rfl
      intro η _
      rw [integral_finsetSum _ (fun k _ => hi ε j η k)]
      apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with s
      dsimp [H,stationaryPhase,PlanarFalconer.radialPhaseIntegral]
      congr 2
      push_cast
      ring

theorem full_stationary_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B G : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ContDiff ℝ ∞ G →
      ∀ C E D R d₁ d₂ : ℝ, 0 ≤ C → 0 ≤ E → 1 ≤ D →
      0 < R → 0 < d₁ → 0 < d₂ → D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
      (∀ t ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      (∀ t ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t G w‖ ≤ E*D^t) →
      ∀ e f : Sphere (m+3),
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d₁) B e*
        stationarySphereApprox m J (r*d₂) G f)‖ ≤
      H*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  choose H hH hb using fun j k => signed_radial_kernel m j k hΨ hs
  let Htotal := ∑ _ε : Bool, ∑ j ∈ Finset.range J, ∑ _η : Bool, ∑ k ∈ Finset.range J, H j k
  refine ⟨Htotal,Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hH _ _)))),?_⟩
  intro B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂ hderB hderG e f
  rw [full_stationary_radial_integral hΨ hs m J B G e f hR hd₁ hd₂]
  calc
    _ ≤ ∑ _ε : Bool, ∑ j ∈ Finset.range J, ∑ _η : Bool, ∑ k ∈ Finset.range J,
        H j k*C*E*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
          (1+R*|d₁-d₂|)^2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ε _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro η _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      exact hb j k B G hB hG C E D R d₁ d₂ hC hE hD hR hd₁ hd₂ hD₁ hD₂
        (fun t ht => hderB t (ht.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hj)))))
        (fun t ht => hderG t (ht.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hk))))) e f ε η
    _ = _ := by simp only [Htotal,Finset.sum_mul,Finset.sum_div]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparable far kernels for the exact descriptor-jet states -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_far_radial_kernel (m K L J : ℕ) (hJL : 2*J ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B H : ℝ, 1 ≤ B ∧ 0 ≤ H ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (x x' y y' : Space (m+3))
        (e e' : Sphere (m+3)),
      ∀ R d₁ d₂ : ℝ, 0 < R → 0 < d₁ → 0 < d₂ →
      (2*(E+Dq))^2 ≤ R*d₁ → (2*(E+Dq))^2 ≤ R*d₂ →
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*
        stationarySphereApprox m J (r*d₁) (f.pairAmbient Q ρ profile N σ J₀ i S A x x') e*
        stationarySphereApprox m J (r*d₂) (g.pairAmbient Q ρ profile N σ J₀ i S A y y') e')‖ ≤
      H*(B^K*A⁻¹)^4*((R*d₁)^(-((m+2:ℕ):ℝ)/2)*(R*d₂)^(-((m+2:ℕ):ℝ)/2))/
        (1+R*|d₁-d₂|)^2 := by
  obtain ⟨B,hB,hbudget⟩ := exists_descriptorJetSymbol_pair_budget (m+1) K L
  obtain ⟨C,hC,hkernel⟩ := full_stationary_radial_bound hΨ hs m J
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f g x x' y y' e e' R d₁ d₂ hR hd₁ hd₂ hscale₁ hscale₂
  have hf (t : ℕ) (ht : t ≤ 2*J) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE f x x' t
      (ht.trans hJL) w
  have hg (t : ℕ) (ht : t ≤ 2*J) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE g y y' t
      (ht.trans hJL) w
  have h := hkernel _ _ (f.pairAmbient_smooth Q ρ profile N σ J₀ i S A x x')
    (g.pairAmbient_smooth Q ρ profile N σ J₀ i S A y y') _ _ _ R d₁ d₂
    (sq_nonneg _) (sq_nonneg _) hD hR hd₁ hd₂ hscale₁ hscale₂ hf hg e e'
  apply h.trans_eq
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarSupport
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original descriptor tests survive the full far radial sum -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem stationarySphereApprox_eq_zero_of_not_tested {m K L : ℕ}
    {F H : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (hHF : H ⊆ F)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ) (x y : Space (m+3))
    (hbad : (x,y) ∉ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H)
    (M : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    stationarySphereApprox m M Λ (f.pairAmbient Q ρ profile N σ J i S A x y)
      (normalizeToSphere w₀ (x-y)) = 0 := by
  have hc (j : ℕ) (ε : Bool) : signedStationaryCoefficient m j Λ
      (f.pairAmbient Q ρ profile N σ J i S A x y) (normalizeToSphere w₀ (x-y)) ε = 0 := by
    by_contra hn
    apply hbad
    intro b hb
    exact f.signed_stationary_support Q ρ profile N σ J i S A x y
      (normalizeToSphere w₀ (x-y)) j Λ ε hn b (hHF hb)
  rw [stationarySphereApprox_pole_sum m M hΛ]
  simp only [stationaryPoleTerm, hc, mul_zero, Finset.sum_const_zero]

end DescriptorJetSymbol

theorem jetStateStationaryKernel_eq_zero_of_not_tested {m K L : ℕ}
    {F H : Finset PolicyDescriptor} {Dq : ℝ}
    (f g : DescriptorJetSymbol (m+1) K L F Dq) (hHF : H ⊆ F)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ)
    (M : ℕ) {R : ℝ} (hR : 0 < R) (Ψ : ℝ → ℝ)
    (hΨ : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))
    (hd₁ : 0 < dist z.1.1 z.1.2) (hd₂ : 0 < dist z.2.1 z.2.2)
    (hbad : z ∉ (descriptorPairTests w₀ Q ρ profile N σ J (i+1) H) ×ˢ
      (descriptorPairTests w₀ Q ρ profile N σ J (i+1) H)) :
    jetStateStationaryKernel f g w₀ Q ρ profile N σ J i S A M R Ψ z = 0 := by
  have hz (r : ℝ) : (Ψ (r/R):ℂ)*
      stationarySphereApprox m M (r*dist z.1.1 z.1.2)
        (f.pairAmbient Q ρ profile N σ J i S A z.1.1 z.1.2)
        (normalizeToSphere w₀ (z.1.1-z.1.2))*
      stationarySphereApprox m M (r*dist z.2.1 z.2.2)
        (g.pairAmbient Q ρ profile N σ J i S A z.2.1 z.2.2)
        (normalizeToSphere w₀ (z.2.1-z.2.2)) = 0 := by
    by_cases hp : Ψ (r/R) = 0
    · simp only [hp, Complex.ofReal_zero, zero_mul]
    have hr : 0 < r := by
      have hh := (lt_div_iff₀ hR).mp (hΨ _ hp).1
      nlinarith
    by_cases hleft : z.1 ∈ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H
    · have hright : z.2 ∉ descriptorPairTests w₀ Q ρ profile N σ J (i+1) H :=
        fun h => hbad ⟨hleft,h⟩
      rw [g.stationarySphereApprox_eq_zero_of_not_tested hHF w₀ Q ρ profile N σ J i S A
        z.2.1 z.2.2 hright M (mul_pos hr hd₂), mul_zero]
    · rw [f.stationarySphereApprox_eq_zero_of_not_tested hHF w₀ Q ρ profile N σ J i S A
        z.1.1 z.1.2 hleft M (mul_pos hr hd₁), mul_zero, zero_mul]
  unfold jetStateStationaryKernel
  simp only [hz, integral_zero, smul_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarOriginalPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebinning the original four-point law at the comparable depth

The earlier labels do not occur in this identity. Only the common-depth
partners forced by the two actual point displacements survive.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem fourPointChildMeasure_restrict_eq_zero {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (u v : List (Fin d → Bool) × List (Fin d → Bool))
    (hu : u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n)
    (hv : v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*(Q.side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(Q.side/(2:ℝ)^n)))
    (hbad : (u,v) ∉ farCellPartners P μ n ×ˢ farCellPartners Q ν n) :
    (fourPointChildMeasure P Q μ ν u v).restrict U = 0 := by
  simp only [fourPointChildMeasure, Measure.prod_restrict, Measure.restrict_restrict hU]
  have he : U ∩ (((P.descendant u.1).carrier ×ˢ (P.descendant u.2).carrier) ×ˢ
      ((Q.descendant v.1).carrier ×ˢ (Q.descendant v.2).carrier)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hp,hq⟩ := hgeo z hz.1
    exact hbad (Finset.mem_product.mpr
      ⟨farCellPartners_of_comparable_points P hP μ n u hu hz.2.1.1 hz.2.1.2 hp.1 hp.2,
        farCellPartners_of_comparable_points Q hQ ν n v hv hz.2.2.1 hz.2.2.2 hq.1 hq.2⟩)
  rw [he, Measure.restrict_empty]

theorem originalFourPointMeasure_far_partition {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*(Q.side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*(Q.side/(2:ℝ)^n))) :
    (originalFourPointMeasure P Q μ ν).restrict U =
      ∑ z ∈ farCellPartners P μ n ×ˢ farCellPartners Q ν n,
        (fourPointChildMeasure P Q μ ν z.1 z.2).restrict U := by
  rw [originalFourPointMeasure_partition P Q μ ν n,
    PlanarFalconer.finite_measure_restrict_sum]
  simp only [PlanarFalconer.finite_measure_restrict_sum]
  rw [← Finset.sum_product (P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n)
    (Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n)
    (fun z => (fourPointChildMeasure P Q μ ν z.1 z.2).restrict U)]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hv).1⟩
  · intro z hz hbad
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
    exact fourPointChildMeasure_restrict_eq_zero P Q hP hQ μ ν n z.1 z.2 hu hv U hU hgeo hbad

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNear
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem profile_near_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a p : ℕ) (lam : ℝ) :
    (profileModelMass m N p/profileModelMass m N a)^4 *
      (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hr : (profileModelMass m N p/profileModelMass m N a)^4 =
      ((2:ℝ)^N)^(-4*(m ((p:ℝ)/N)-m ((a:ℝ)/N))) := by
    unfold profileModelMass
    rw [← Real.rpow_sub hR,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hr,← dyadic_rpow_change_base hN ((d:ℝ)*((p:ℝ)-a)),
    ← Real.rpow_add hR,← Real.rpow_add hR]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FarNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimensional gain and exact profile normalization of the far term -/

namespace Falconer

theorem far_sphere_gain (m : ℕ) {v b d₁ d₂ : ℝ}
    (h₁ : (2:ℝ)^(-b) ≤ d₁) (h₂ : (2:ℝ)^(-b) ≤ d₂) :
    ((2:ℝ)^v*d₁)^(-((m+2:ℕ):ℝ)/2)*
      ((2:ℝ)^v*d₂)^(-((m+2:ℕ):ℝ)/2) ≤
    (2:ℝ)^(-((m+2:ℕ):ℝ)*(v-b)) := by
  let p : ℝ := -((m+2:ℕ):ℝ)/2
  have hd₁ : 0 ≤ d₁ := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-b)).le.trans h₁
  have hd₂ : 0 ≤ d₂ := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-b)).le.trans h₂
  have hp : p ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)
  have hbase : (2:ℝ)^v*(2:ℝ)^(-b) = (2:ℝ)^(v-b) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
  have hle (d : ℝ) (hd : (2:ℝ)^(-b) ≤ d) :
      ((2:ℝ)^v*d)^p ≤ ((2:ℝ)^(v-b))^p := by
    apply Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by norm_num) _)
      _ hp
    rw [← hbase]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  change ((2:ℝ)^v*d₁)^p*((2:ℝ)^v*d₂)^p ≤ _
  calc
    _ ≤ ((2:ℝ)^(v-b))^p*((2:ℝ)^(v-b))^p :=
      mul_le_mul (hle d₁ h₁) (hle d₂ h₂) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (v-b)),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      dsimp [p]
      ring

theorem profile_far_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a b : ℕ) (v lam : ℝ) :
    (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N b/profileModelMass m N a)^4*
      (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b))*
      ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-2*((m ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
      (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hfreq : (2:ℝ)^((d:ℝ)*(v-a))*(2:ℝ)^(-((d:ℝ)-1)*(v-b))*
      (2:ℝ)^(-(v-b)) = (2:ℝ)^((d:ℝ)*((b:ℝ)-a)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (profileModelMass m N b/profileModelMass m N a)^4*
        ((2:ℝ)^((d:ℝ)*(v-a))*(2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b)))*
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by ring
    _ = _ := by rw [hfreq]; exact profile_near_prefactor hN d m a b lam

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FarTestedIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual far kernel is bounded on the original tested pair laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem lintegral_supported_pair_bound {d : ℕ}
    (μ ν : Measure (Space d × Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (G H : Set (Space d × Space d))
    (hG : MeasurableSet G) (hH : MeasurableSet H)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (F : ((Space d × Space d) × (Space d × Space d)) → ℂ)
    (k : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞)
    (hk : Measurable k) (C : ℝ≥0∞)
    (hb : ∀ z ∈ U, ENNReal.ofReal ‖F z‖ ≤ C*k z)
    (hs : ∀ z ∈ U, z ∉ G ×ˢ H → F z = 0) :
    (∫⁻ z in U, ENNReal.ofReal ‖F z‖ ∂μ.prod ν) ≤
      C*(∫⁻ z in U, k z ∂(μ.restrict G).prod (ν.restrict H)) := by
  have hT : MeasurableSet (G ×ˢ H) := hG.prod hH
  have he : (∫⁻ z in U, ENNReal.ofReal ‖F z‖ ∂μ.prod ν) =
      ∫⁻ z in U, (G ×ˢ H).indicator (fun z => ENNReal.ofReal ‖F z‖) z ∂μ.prod ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hU] with z hz
    by_cases ht : z ∈ G ×ˢ H
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht, hs z hz ht, norm_zero, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hT, Measure.prod_restrict,
    Measure.restrict_restrict hT, Measure.restrict_restrict hU, inter_comm (G ×ˢ H) U]
  calc
    _ ≤ ∫⁻ z in U ∩ (G ×ˢ H), C*k z ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hU.inter hT)] with z hz
      exact hb z hz.1
    _ = _ := lintegral_const_mul C hk

theorem exists_jetState_far_tested_integral (m K L J : ℕ) (hJL : 2*J ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F H : Finset PolicyDescriptor), H ⊆ F →
      ∀ (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (v b : ℝ)
        (P₁ P₂ Q₁ Q₂ : DyadicCube (m+3))
        (U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))),
      MeasurableSet U →
      (∀ z ∈ U, (2:ℝ)^(-b) ≤ dist z.1.1 z.1.2 ∧ (2:ℝ)^(-b) ≤ dist z.2.1 z.2.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.1.1 z.1.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.2.1 z.2.2) →
      (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i S A J
        ((2:ℝ)^v) Ψ z‖
        ∂((ρ.restrict P₁.carrier).prod (ρ.restrict P₂.carrier)).prod
          ((ρ.restrict Q₁.carrier).prod (ρ.restrict Q₂.carrier))) ≤
      ENNReal.ofReal (C*(B^K*A⁻¹)^4*(2:ℝ)^(-((m+2:ℕ):ℝ)*(v-b))) *
        (∫⁻ z in U, ENNReal.ofReal
          (1/(1+(2:ℝ)^v*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
          ∂(testedCellPair ρ ρ P₁ P₂ (descriptorPairTests w₀ Q ρ profile N σ J₀ (i+1) H)).prod
            (testedCellPair ρ ρ Q₁ Q₂ (descriptorPairTests w₀ Q ρ profile N σ J₀ (i+1) H))) := by
  obtain ⟨B,C,hB,hC,hkernel⟩ := exists_jetState_far_radial_kernel m K L J hJL hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F H hHF w₀ Q ρ _ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f g v b P₁ P₂ Q₁ Q₂ U hU hgeo
  apply lintegral_supported_pair_bound _ _ _ _
    (descriptorPairTests_measurable w₀ Q ρ profile N σ J₀ (i+1) H)
    (descriptorPairTests_measurable w₀ Q ρ profile N σ J₀ (i+1) H)
    U hU _ _ (by fun_prop)
  · intro z hz
    obtain ⟨h₁,h₂,hD₁,hD₂⟩ := hgeo z hz
    have hd₁ : 0 < dist z.1.1 z.1.2 := (Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₁
    have hd₂ : 0 < dist z.2.1 z.2.2 := (Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₂
    have hb := hkernel F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
      f g z.1.1 z.1.2 z.2.1 z.2.2 (normalizeToSphere w₀ (z.1.1-z.1.2))
        (normalizeToSphere w₀ (z.2.1-z.2.2)) ((2:ℝ)^v) _ _ (by positivity) hd₁ hd₂ hD₁ hD₂
    have hgain := far_sphere_gain m (v := v) h₁ h₂
    have hCb : 0 ≤ C*(B^K*A⁻¹)^4 := mul_nonneg hC (by positivity)
    have hb' := hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgain hCb) (by positivity))
    change ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i S A J
      ((2:ℝ)^v) Ψ z‖ ≤ _
    rw [← ENNReal.ofReal_mul (mul_nonneg hCb (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    simpa only [jetStateStationaryKernel, div_eq_mul_inv, one_div, one_mul, mul_assoc] using hb'
  · intro z hz hbad
    obtain ⟨h₁,h₂,_,_⟩ := hgeo z hz
    exact jetStateStationaryKernel_eq_zero_of_not_tested f g hHF w₀ Q ρ profile N σ J₀ i S A J
      (by positivity) Ψ hs z ((Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₁)
      ((Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₂) hbad

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar far kernel in the actual positive states

The one-dimensional bin estimate is applied to the two original tested
pair-distance laws. Both use the same profile normalization at the child
scale. No angular symbol is removed before this positive comparison.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem real_bin_kernel_le_max_collision (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      PlanarFalconer.binKernelConstant *
        max ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
          ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w}) := by
  have hb (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
      PlanarFalconer.binL2Norm ρ w ≤
        ((ρ.prod ρ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})^(1/2:ℝ) := by
    have h := PlanarFalconer.real_bin_collision_bound ρ hw
    rw [← PlanarFalconer.binL2Norm_mul_self] at h
    have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  apply (PlanarFalconer.real_bin_decaying_kernel_bound μ ν hw).trans
  apply mul_le_mul' le_rfl
  have hprod := mul_le_mul' (hb μ) (hb ν)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)] at hprod
  apply hprod.trans
  have hh := ENNReal.rpow_le_rpow (mul_le_mul'
    (le_max_left ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
      ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w}))
    (le_max_right ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
      ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w})))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact le_max_iff.mpr hh

 theorem positiveCollision_kernel_max {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t : ℕ)
    (X Y X' Y' : List (Fin d → Bool)) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^t*|z.1-z.2|)^2)
        ∂(testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellDistance ρ ρ (Q.descendant X') (Q.descendant Y')
          (policyTestPairs w₀ Q ρ m A N σ J i q a t))) ≤
      PlanarFalconer.binKernelConstant *
        max (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y)
          (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X' Y') := by
  let μ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  let ν := testedCellDistance ρ ρ (Q.descendant X') (Q.descendant Y')
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  let C : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a))
  have hw : 0 < 1/(2:ℝ)^t := by positivity
  have hh := real_bin_kernel_le_max_collision μ ν hw
  have he (z : ℝ × ℝ) : |z.1-z.2|/(1/(2:ℝ)^t) = (2:ℝ)^t*|z.1-z.2| := by
    simp only [one_div,div_inv_eq_mul,mul_comm]
  simp_rw [he] at hh
  have hwC : 1/(2:ℝ)^t ≤ (100*((d:ℝ)+1))/(2:ℝ)^t := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hμ : (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^t} ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} :=
    measure_mono (fun _ hz => hz.trans hwC)
  have hν : (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^t} ≤
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} :=
    measure_mono (fun _ hz => hz.trans hwC)
  have h := mul_le_mul' (show C ≤ C from le_rfl)
    (hh.trans (mul_le_mul' le_rfl (max_le_max hμ hν)))
  change C * _ ≤ _
  apply h.trans_eq
  simp only [positiveCollisionCount,← mul_max,μ,ν,C]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveSpatialKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision kernel on the original four-point measures

An additional far-cell or comparable-band restriction can be dropped
after the kernel has become nonnegative. The endpoint tests remain in
the two original pair measures throughout this comparison.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem testedCellDistance_lintegral {d : ℕ}
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (P Q P' Q' : DyadicCube d) (G H : Set (Space d × Space d))
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(testedCellDistance ρ ρ P Q G).prod (testedCellDistance ρ ρ P' Q' H)) =
    ∫⁻ z, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2)
      ∂(testedCellPair ρ ρ P Q G).prod (testedCellPair ρ ρ P' Q' H) := by
  rw [testedCellDistance,testedCellDistance,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),lintegral_map hF (by fun_prop)]
  rfl

theorem positiveCollision_spatial_kernel_max {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t : ℕ)
    (X Y X' Y' : List (Fin d → Bool))
    (S : Set ((Space d × Space d) × (Space d × Space d))) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (∫⁻ z in S, ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂(testedCellPair ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellPair ρ ρ (Q.descendant X') (Q.descendant Y')
          (policyTestPairs w₀ Q ρ m A N σ J i q a t))) ≤
      PlanarFalconer.binKernelConstant *
        max (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y)
          (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X' Y') := by
  have h := positiveCollision_kernel_max w₀ Q ρ m A N σ J i q a t X Y X' Y'
  rw [testedCellDistance_lintegral ρ _ _ _ _ _ _ _ (by fun_prop)] at h
  apply le_trans _ h
  exact mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FarPositiveSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive far kernels over the actual comparable cell pairs

The maximum ranges over the original tested distance laws.  The number
of summands is bounded by two free cell labels, not four.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem far_positive_kernel_sum_le {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ)
    (S : (List (Fin d → Bool) × List (Fin d → Bool)) →
      (List (Fin d → Bool) × List (Fin d → Bool)) →
        Set ((Space d × Space d) × (Space d × Space d))) :
    (∑ z ∈ (farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n),
      ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*m b)) *
        (∫⁻ v in S z.1 z.2,
          ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist v.1.1 v.1.2-dist v.2.1 v.2.2|)^2)
          ∂(testedCellPair ρ ρ (Q.descendant (X++z.1.1)) (Q.descendant (X++z.1.2))
            (policyTestPairs w₀ Q ρ m A N σ J i q b t)).prod
            (testedCellPair ρ ρ (Q.descendant (Y++z.2.1)) (Q.descendant (Y++z.2.2))
              (policyTestPairs w₀ Q ρ m A N σ J i q b t)))) ≤
      (((farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞) *
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ m A N σ J i q b t X Y n := by
  let T := (farCellPartners (Q.descendant X) ρ n) ×ˢ
    (farCellPartners (Q.descendant Y) ρ n)
  calc
    _ ≤ ∑ _z ∈ T, PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ m A N σ J i q b t X Y n := by
      apply Finset.sum_le_sum
      intro z hz
      exact (positiveCollision_spatial_kernel_max w₀ Q ρ m A N σ J i q b t
        (X++z.1.1) (X++z.1.2) (Y++z.2.1) (Y++z.2.2) (S z.1 z.2)).trans
        (mul_le_mul' le_rfl (Finset.le_sup (s := T) (f := fun z =>
          max (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (X++z.1.1) (X++z.1.2))
            (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (Y++z.2.1) (Y++z.2.2))) hz))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc, T]

theorem farCellPartners_regular_card {d : ℕ} {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : Regularization.RegularizedProfileData Q ρ N s lam m) (hQ : 0 < Q.side)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a) :
    (((farCellPartners (Q.descendant X) ρ (b-a)) ×ˢ
      (farCellPartners (Q.descendant Y) ρ (b-a))).card : ℝ) ≤
      ((2*(1100*(d+1))+1)^(2*d):ℕ) *
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hc := farCellPartners_pair_card (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQ X) (Q.descendant_side_pos hQ Y) ρ ρ (b-a)
  have hc' : (((farCellPartners (Q.descendant X) ρ (b-a)) ×ˢ
      (farCellPartners (Q.descendant Y) ρ (b-a))).card : ℝ) ≤
      (((2*(1100*(d+1))+1)^(2*d):ℕ):ℝ) *
        (((Q.descendant X).occupiedPaths ρ (b-a) ×ˢ
          (Q.descendant Y).occupiedPaths ρ (b-a)).card : ℝ) := by exact_mod_cast hc
  exact hc'.trans (mul_le_mul_of_nonneg_left (h.pair_count hab hb X Y hX hY)
    (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FarCollisionIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stationary far kernel on the original collision laws

The original four-point law is reassembled before the comparable-depth
partition. Only two free cell labels remain in the resulting collision bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem originalFourPoint_far_tested_bound {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hQ : 0 < Q.side) (profile : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n)))
    (K : ((Space d × Space d) × (Space d × Space d)) → ℂ) (C : ℝ≥0∞)
    (hcell : ∀ u ∈ farCellPartners (Q.descendant X) ρ n,
      ∀ v ∈ farCellPartners (Q.descendant Y) ρ n,
      (∫⁻ z in U, ENNReal.ofReal ‖K z‖ ∂fourPointChildMeasure
        (Q.descendant X) (Q.descendant Y) ρ ρ u v) ≤
      C*(∫⁻ z in U,
        ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂(testedCellPair ρ ρ (Q.descendant (X++u.1)) (Q.descendant (X++u.2))
          (policyTestPairs w₀ Q ρ profile A N σ J i q b t)).prod
          (testedCellPair ρ ρ (Q.descendant (Y++v.1)) (Q.descendant (Y++v.2))
            (policyTestPairs w₀ Q ρ profile A N σ J i q b t)))) :
    ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
      (∫⁻ z in U, ENNReal.ofReal ‖K z‖
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      C*(((farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞)*
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ profile A N σ J i q b t X Y n := by
  rw [originalFourPointMeasure_far_partition (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQ X) (Q.descendant_side_pos hQ Y) ρ ρ n U hU hgeo,
    lintegral_finsetSum_measure, Finset.mul_sum]
  calc
    _ ≤ ∑ z ∈ farCellPartners (Q.descendant X) ρ n ×ˢ
        farCellPartners (Q.descendant Y) ρ n,
      C*(ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
        (∫⁻ x in U,
          ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist x.1.1 x.1.2-dist x.2.1 x.2.2|)^2)
          ∂(testedCellPair ρ ρ (Q.descendant (X++z.1.1)) (Q.descendant (X++z.1.2))
            (policyTestPairs w₀ Q ρ profile A N σ J i q b t)).prod
            (testedCellPair ρ ρ (Q.descendant (Y++z.2.1)) (Q.descendant (Y++z.2.2))
              (policyTestPairs w₀ Q ρ profile A N σ J i q b t)))) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
      simpa only [mul_left_comm] using mul_le_mul' le_rfl (hcell z.1 hu z.2 hv)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      simpa only [mul_assoc] using mul_le_mul' (le_refl C)
        (far_positive_kernel_sum_le w₀ Q ρ profile A N σ J i q b t X Y n (fun _ _ => U))

theorem exists_jetState_far_collision_integral (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (w₀ : Sphere (m+3))
        (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) [IsFiniteMeasure ρ],
      0 < Q.side → ∀ (profile : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ)
        (J i q b t : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))),
      PlanarFalconer.policyDescriptorList A N q b t ⊆ F →
      (∀ c ∈ F, ∀ w ∈ S c, ∀ z ∈ S c, w ≠ z → descriptorMaskRadius N σ c/2 ≤ dist w z) →
      ∀ Dq Dmask E Z : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Z →
      1 ≤ 2*(E+Dq) → (∀ c ∈ F, (descriptorMaskRadius N σ c)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq)
        (X Y : List (Fin (m+3) → Bool)) (n : ℕ)
        (U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))),
      MeasurableSet U →
      (∀ z ∈ U,
        (256*(((m+3:ℕ):ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
          dist z.1.1 z.1.2 ≤ 1024*(((m+3:ℕ):ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n)) ∧
        (256*(((m+3:ℕ):ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
          dist z.2.1 z.2.2 ≤ 1024*(((m+3:ℕ):ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n))) →
      (∀ z ∈ U, (2:ℝ)^(-(b:ℝ)) ≤ dist z.1.1 z.1.2 ∧
        (2:ℝ)^(-(b:ℝ)) ≤ dist z.2.1 z.2.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^t*dist z.1.1 z.1.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^t*dist z.2.1 z.2.2) →
      ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
        (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J i S Z M
          ((2:ℝ)^t) Ψ z‖
          ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      ENNReal.ofReal (C*(B^K*Z⁻¹)^4*(2:ℝ)^(-((m+2:ℕ):ℝ)*((t:ℝ)-b))) *
        (((farCellPartners (Q.descendant X) ρ n) ×ˢ
          (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞) *
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ profile A N σ J (i+1) q b t X Y n := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_tested_integral m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F w₀ Q ρ _ hQ profile A N σ J i q b t S hHF hsep Dq Dmask E Z
    hDq hDm hZ hD hscale hE f g X Y n U hU hgeo hfreq
  apply originalFourPoint_far_tested_bound w₀ Q ρ hQ profile A N σ J (i+1) q b t
    X Y n U hU hgeo
  intro u _ v _
  simpa only [fourPointChildMeasure,Q.descendant_append,policyTestPairs,Real.rpow_natCast] using
    hbound F (PlanarFalconer.policyDescriptorList A N q b t) hHF w₀ Q ρ profile N σ J i S
      hsep Dq Dmask E Z hDq hDm hZ hD hscale hE f g t b
      ((Q.descendant X).descendant u.1) ((Q.descendant X).descendant u.2)
      ((Q.descendant Y).descendant v.1) ((Q.descendant Y).descendant v.2) U hU
      (by simpa only [Real.rpow_natCast] using hfreq)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FarProfileNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conversion from positive collision to far-shell normalization -/

namespace Falconer

theorem profile_far_collision_normalization {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a b : ℕ) (v lam : ℝ) :
    ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N a)⁻¹^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b)) /
      ((2:ℝ)^(v-b)*(profileModelMass m N b)⁻¹^4)) *
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
      ((2:ℝ)^N)^(-2*((m ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
        (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have ha : profileModelMass m N a ≠ 0 := by unfold profileModelMass; positivity
  have hb : profileModelMass m N b ≠ 0 := by unfold profileModelMass; positivity
  have hv : (2:ℝ)^(v-b) ≠ 0 := by positivity
  have hi : ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N a)⁻¹^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b)) /
      ((2:ℝ)^(v-b)*(profileModelMass m N b)⁻¹^4)) =
      (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N b/profileModelMass m N a)^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  rw [hi]
  exact profile_far_prefactor hN d m a b v lam

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FarNormalizedBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision normalization and the two-free-cell count in one far bound -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

private theorem real_scaled_bound {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (_hγ : 0 ≤ γ) {I X : ℝ≥0∞}
    (h : ENNReal.ofReal β * I ≤ ENNReal.ofReal γ * X) :
    ENNReal.ofReal α * I ≤ ENNReal.ofReal (α*γ/β) * X := by
  have hab : 0 ≤ α/β := div_nonneg hα hβ.le
  calc
    _ = ENNReal.ofReal (α/β) * (ENNReal.ofReal β * I) := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hab,div_mul_cancel₀ α hβ.ne']
    _ ≤ ENNReal.ofReal (α/β) * (ENNReal.ofReal γ * X) := mul_le_mul' le_rfl h
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hab]
      congr 2
      ring

 theorem profile_far_collision_bound {N : ℕ} (hN : 0 < N)
    (d : ℕ) (profile : ℝ → ℝ) (a b : ℕ) (v lam : ℝ)
    {C Cdim : ℝ} (hC : 0 ≤ C) (hCdim : 0 ≤ Cdim)
    {card : ℕ}
    (hcard : (card:ℝ) ≤ Cdim*((2:ℝ)^N)^(
      2*(profile ((b:ℝ)/N)-profile ((a:ℝ)/N))+4*((d:ℝ)+1)*lam))
    {I X : ℝ≥0∞}
    (h : ENNReal.ofReal ((2:ℝ)^(v-b)*(profileModelMass profile N b)⁻¹^4)*I ≤
      ENNReal.ofReal (C*(2:ℝ)^(-((d:ℝ)-1)*(v-b)))*(card:ℝ≥0∞)*X) :
    ENNReal.ofReal ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*I ≤
      ENNReal.ofReal (C*Cdim*((2:ℝ)^N)^(
        -2*((profile ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam))*X := by
  let α := (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4
  let β := (2:ℝ)^(v-b)*(profileModelMass profile N b)⁻¹^4
  let G := (2:ℝ)^(-((d:ℝ)-1)*(v-b))
  let R := ((2:ℝ)^N)^(2*(profile ((b:ℝ)/N)-profile ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β,profileModelMass]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : (card:ℝ≥0∞) ≤ ENNReal.ofReal (Cdim*R) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
  have h' : ENNReal.ofReal β*I ≤ ENNReal.ofReal (C*G*Cdim*R)*X := by
    calc
      _ ≤ ENNReal.ofReal (C*G)*(card:ℝ≥0∞)*X := h
      _ ≤ ENNReal.ofReal (C*G)*ENNReal.ofReal (Cdim*R)*X :=
        mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl
      _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hC hG)]; congr 2; ring
  have hscale := real_scaled_bound hα hβ
    (mul_nonneg (mul_nonneg (mul_nonneg hC hG) hCdim) hR) h'
  have he : α*(C*G*Cdim*R)/β = C*Cdim*((2:ℝ)^N)^(
        -2*((profile ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
    calc
      _ = C*Cdim*((α*G/β)*R) := by ring
      _ = _ := by rw [profile_far_collision_normalization hN d profile a b v lam]
  simpa only [he,α] using hscale

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_KernelL1Comparison
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing pointwise stationary remainders to the original law

Only the added error is measurable here. The stationary kernel itself
enters a nonnegative upper integral and needs no joint spatial regularity.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem profileModelMass_inv_four (profile : ℝ → ℝ) (N b : ℕ) :
    (profileModelMass profile N b)⁻¹^4 = ((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [profileModelMass,Real.rpow_neg hR.le,inv_inv,← Real.rpow_natCast,← Real.rpow_mul hR.le]
  congr 1
  ring

theorem profile_collision_scale (profile : ℝ → ℝ) (N : ℕ)
    {b t : ℕ} (hbt : b ≤ t) :
    (2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) =
      (2:ℝ)^((t:ℝ)-b)*(profileModelMass profile N b)⁻¹^4 := by
  rw [profileModelMass_inv_four,← Nat.cast_sub hbt,Real.rpow_natCast]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized comparable-band bound for the actual stationary kernel -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_far_band (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (w₀ : Sphere (m+3))
        (Q : DyadicCube (m+3)), Q.side = 1 →
      ∀ (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ) (N : ℕ) (s lam : ℝ),
      Regularization.RegularizedProfileData Q ρ N s lam profile → 0 < N →
      ∀ (A : ℕ → ℝ) (σ : ℝ) (J i q a b t : ℕ), a ≤ b → b ≤ N → b ≤ t →
      ∀ (S : PolicyDescriptor → Finset (Sphere (m+3))),
      PlanarFalconer.policyDescriptorList A N q b t ⊆ F →
      (∀ c ∈ F, ∀ w ∈ S c, ∀ z ∈ S c, w ≠ z → descriptorMaskRadius N σ c/2 ≤ dist w z) →
      ∀ Dq Dmask E Z : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Z →
      1 ≤ 2*(E+Dq) → (∀ c ∈ F, (descriptorMaskRadius N σ c)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E → (2*(E+Dq))^2 ≤ (2:ℝ)^((t:ℝ)-b) →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq)
        (X Y : List (Fin (m+3) → Bool)), X.length = a → Y.length = a →
      ∀ U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      MeasurableSet U → U ⊆ comparableLengthBand (m+3) b →
      ENNReal.ofReal ((2:ℝ)^(((m+3:ℕ):ℝ)*((t:ℝ)-a))*(profileModelMass profile N a)⁻¹^4)*
        (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ
          (fun s => profile (s/N)) N σ J i S Z M ((2:ℝ)^t) Ψ z‖
          ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      ENNReal.ofReal (C*(B^K*Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^N)^(-2*((profile ((b:ℝ)/N)-((m+3:ℕ):ℝ)/2*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((m+3:ℕ):ℝ)/2*(a:ℝ)/N))+4*(((m+3:ℕ):ℝ)+1)*lam)) *
        (PlanarFalconer.binKernelConstant *
          farCollisionMaximum w₀ Q ρ (fun s => profile (s/N)) A N σ J (i+1) q b t X Y (b-a)) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_collision_integral m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F w₀ Q hQ ρ profile N s lam hreg hN A σ J i q a b t hab hbN hbt
    S hHF hsep Dq Dmask E Z hDq hDm hZ hD hscale hE hDfreq f g X Y hX hY U hU hband
  let := hreg.probability
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hg := hbound F w₀ Q ρ hQpos (fun s => profile (s/N)) A N σ J i q b t S hHF hsep
    Dq Dmask E Z hDq hDm hZ hD hscale hE f g X Y (b-a) U hU
    (fun z hz => comparableLengthBand_descendants Q hQ X Y hX hY hab (hband hz))
    (by
      intro z hz
      obtain ⟨h₁,h₂⟩ := comparableLengthBand_dist_lower (hband hz)
      have hbase : (2:ℝ)^t*(2:ℝ)^(-(b:ℝ)) = (2:ℝ)^((t:ℝ)-b) := by
        rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
      refine ⟨h₁,h₂,?_,?_⟩
      · exact hDfreq.trans (by rw [← hbase]; exact mul_le_mul_of_nonneg_left h₁ (by positivity))
      · exact hDfreq.trans (by rw [← hbase]; exact mul_le_mul_of_nonneg_left h₂ (by positivity)))
  have hnorm : (2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) =
      (2:ℝ)^((t:ℝ)-b)*(profileModelMass profile N b)⁻¹^4 := profile_collision_scale profile N hbt
  have hd : ((m+3:ℕ):ℝ)-1 = ((m+2:ℕ):ℝ) := by push_cast; ring
  have hresult := profile_far_collision_bound hN (m+3) profile a b t lam
    (C := C*(B^K*Z⁻¹)^4) (mul_nonneg hC (pow_nonneg (mul_nonneg
      (pow_nonneg (zero_le_one.trans hB) _) (inv_nonneg.mpr hZ.le)) _))
    (Cdim := ((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)) (Nat.cast_nonneg _)
    (farCellPartners_regular_card hreg hQpos hab hbN X Y hX hY)
    (I := ∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ
      (fun s => profile (s/N)) N σ J i S Z M ((2:ℝ)^t) Ψ z‖
      ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ)
    (X := PlanarFalconer.binKernelConstant *
      farCollisionMaximum w₀ Q ρ (fun s => profile (s/N)) A N σ J (i+1) q b t X Y (b-a))
    (by simpa only [hnorm,hd,mul_assoc] using hg)
  exact hresult

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarData
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric data for the actual far branch

These are scale and descriptor conditions to be verified by the recursive
policy. They are not additional published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

theorem list_scale_mono (D : JetStateFarData m B) {C : ℝ} (hCB : C ≤ B) :
    (D.F.card:ℝ)*C*D.Dmask ≤ D.E :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCB (Nat.cast_nonneg _))
    (zero_le_one.trans D.Dmask_one)).trans D.list_scale

end JetStateFarData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarKernelDataEstimates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The proved analytic estimates on the actual far-branch data -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_far_data_stationary_band_oai (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B') (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
        (w₀ : Sphere (m+3)) (b : ℕ), b ∈ Finset.Icc (D.a+9) (D.h+6) →
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
          ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
        D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_band m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro B' hBB D f g w₀ b hb
  have hbr := Finset.mem_Icc.mp hb
  have hfreq := far_band_frequency_mono hbr.2 D.band_scale
  have hh := hbound D.F w₀ D.Q D.unit D.ρ D.profile D.N D.s D.lam D.regular D.N_pos
    D.policy D.σ D.J D.i D.q D.a b D.t (by omega) (by have := D.ht; have := D.tN; omega)
    (by have := D.ht; omega) D.masks (D.child_list b hb) D.separated
    D.Dq D.Dmask D.E D.Z D.Dq_nonneg D.Dmask_one D.Z_pos D.scale_one D.mask_scale
    (D.list_scale_mono hBB) hfreq f g D.X D.Y D.X_length D.Y_length
    (comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b)
    ((comparableFarRegion_measurable _ _ _).inter (comparableLengthBand_measurable _ _))
    inter_subset_right
  exact hh

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_far_data_stationary_band_oai := @OAI.Falconer.exists_far_data_stationary_band_oai
