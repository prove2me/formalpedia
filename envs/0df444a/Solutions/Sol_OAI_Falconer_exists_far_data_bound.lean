-- Prove2me | solution 1 for OAI.Falconer.exists_far_data_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:15:32.056517+00:00
-- url     : https://prove2.me/submissions/13429c6c-5aea-4eba-a0e2-d83ddf00e2fc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_far_data_stationary_band
import Theorems.Thm_OAI_Falconer_sphere_stationary_expansion

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

theorem noncomparable_radial_frequency {dlarge dsmall t s : ℝ}
    (hsep : 2*dsmall ≤ dlarge) (ht : |t| ≤ dsmall) (hs : s = 1 ∨ s = -1) :
    dlarge/2 ≤ |s*dlarge+t| := by
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  rcases hs with rfl | rfl
  · simp only [one_mul]
    linarith only [hsep, ht1, le_abs_self (dlarge+t)]
  · simp only [neg_one_mul]
    linarith only [hsep, ht2, neg_le_abs (-dlarge+t)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_OriginalShellIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ParentRetainedEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_ae_nonzero (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) :
    ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, Ψ (r/(2:ℝ)^v) ≠ 0 := by
  unfold sourceAngularShellMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards with r hr
  intro hz
  apply hr
  simp only [hz, zero_div, ENNReal.ofReal_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularStationaryRadialError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem complex_product_replacement_bound (A B E F : ℂ) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hE : ‖A-E‖ ≤ ε) (hF : ‖B-F‖ ≤ ε) :
    ‖A*B-E*F‖ ≤ ε*(2*C+ε) := by
  have he : ‖E‖ ≤ C+ε := by
    have ht := norm_add_le A (E-A)
    rw [add_sub_cancel,norm_sub_rev E A] at ht
    exact ht.trans (add_le_add hA hE)
  calc
    _ = ‖(A-E)*B+E*(B-F)‖ := by congr 1; ring
    _ ≤ ‖A-E‖*‖B‖+‖E‖*‖B-F‖ := by simpa only [norm_mul] using norm_add_le ((A-E)*B) (E*(B-F))
    _ ≤ ε*C+(C+ε)*ε := by gcongr
    _ = _ := by ring

theorem angular_radial_product_replacement (v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (A B E F : ℝ → ℂ) (hmA : Measurable A) (hmB : Measurable B)
    (hmE : Measurable E) (hmF : Measurable F)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hA : ∀ r, ‖A r‖ ≤ C) (hB : ∀ r, ‖B r‖ ≤ C)
    (hE : ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → ‖A r-E r‖ ≤ ε)
    (hF : ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → ‖B r-F r‖ ≤ ε) :
    ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A r*B r)) -
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (E r*F r))‖ ≤
      4*W*(ε*(2*C+ε)) := by
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hupper : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hn
    exact (not_lt_of_ge (hs t hn).2.le) ht
  let μ := sourceAngularShellMeasure v Ψ
  let : IsFiniteMeasure μ := sourceAngularShellMeasure_finite v Ψ hW hw hupper
  have hae := sourceAngularShellMeasure_ae_nonzero v Ψ hΨ
  have he : ∀ᵐ r ∂μ, ‖E r‖ ≤ C+ε := by
    filter_upwards [hae] with r hr
    have ht := norm_add_le (A r) (E r-A r)
    rw [add_sub_cancel,norm_sub_rev (E r) (A r)] at ht
    exact ht.trans (add_le_add (hA r) (hE r hr))
  have hf : ∀ᵐ r ∂μ, ‖F r‖ ≤ C+ε := by
    filter_upwards [hae] with r hr
    have ht := norm_add_le (B r) (F r-B r)
    rw [add_sub_cancel,norm_sub_rev (F r) (B r)] at ht
    exact ht.trans (add_le_add (hB r) (hF r hr))
  have hiAB : Integrable (fun r => A r*B r) μ :=
    Integrable.of_bound (hmA.mul hmB).aestronglyMeasurable (C*C)
      (Filter.Eventually.of_forall (fun r => by rw [norm_mul]; exact mul_le_mul (hA r) (hB r) (norm_nonneg _) hC))
  have hiEF : Integrable (fun r => E r*F r) μ := by
    apply Integrable.of_bound (hmE.mul hmF).aestronglyMeasurable ((C+ε)*(C+ε))
    filter_upwards [he,hf] with r her hfr
    change ‖E r*F r‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul her hfr (norm_nonneg _) (add_nonneg hC hε)
  rw [← sourceAngularShellMeasure_integral v hΨ hpos hz,
    ← sourceAngularShellMeasure_integral v hΨ hpos hz,← integral_sub hiAB hiEF]
  apply (norm_integral_le_of_norm_le_const (show ∀ᵐ r ∂μ,
    ‖A r*B r-E r*F r‖ ≤ ε*(2*C+ε) from by
      filter_upwards [hae] with r hr
      exact complex_product_replacement_bound _ _ _ _ hC hε (hA r) (hB r) (hE r hr) (hF r hr))).trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (sourceAngularShellMeasure_real_mass_le v Ψ hW hw hupper)
    (show 0 ≤ ε*(2*C+ε) by positivity)

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetRemoval
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetBound_one_le (d K : ℕ) : 1 ≤ descriptorJetBound d K :=
  (normalizedDescriptorJet_order_bound d K).choose_spec.1

theorem descriptorJetProduct_norm_le {d K : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hsep : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (horder : (∑ j ∈ F, k j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) (x : Space d) (w : Sphere d) :
    ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ (descriptorJetBound d K)^K := by
  have hA := descriptorJetBound_one_le d K
  have hbound := (normalizedDescriptorJet_order_bound d K).choose_spec.2
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, (descriptorJetBound d K)^(k j) := by
      apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = (descriptorJetBound d K)^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k _
    _ ≤ (descriptorJetBound d K)^K := pow_le_pow_right₀ hA horder

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the finite stationary remainders

These are the exact scale calculations in `osc:stationary`. The ratio
`A^2 / Λ` pays for each extra stationary term. The remaining `d+2`
derivatives are absorbed using `A ≤ R^2`. No stationary-phase estimate is
assumed here.
-/

namespace Falconer

theorem stationary_remainder_ratio (J d : ℕ) (A Λ : ℝ) :
    (Λ⁻¹)^J * A^(2*J+d+2) = (A^2/Λ)^J * A^(d+2) := by
  rw [show 2*J+d+2 = 2*J+(d+2) by omega, pow_add, pow_mul, div_pow, div_eq_mul_inv]
  ring

theorem stationary_remainder_scale (J d : ℕ) {R A Λ κ : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hΛ : 0 < Λ) (hupper : A ≤ R^2)
    (hratio : A^2/Λ ≤ R^(-κ)) :
    (Λ⁻¹)^J * A^(2*J+d+2) ≤ R^(-κ*(J:ℝ)+2*(d+2)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [stationary_remainder_ratio]
  calc
    _ ≤ (R^(-κ))^J * (R^2)^(d+2) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hratio J)
        (pow_le_pow_left₀ hA hupper (d+2)) (by positivity) (by positivity)
    _ = R^(-κ*(J:ℝ)+2*(d+2)) := by
      rw [← Real.rpow_mul_natCast hRp.le, ← pow_mul,
        ← Real.rpow_natCast, ← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

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

 theorem normalizedAmbientDescriptorJet_sphere {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x w : ℂ) =
      normalizedDescriptorJet Q ρ m N σ J i b S k v x w := rfl

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_FactorizedAngularState
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem multiplier_bound (f : DescriptorJetSymbol n K L F D) {A : ℝ} (hA : 0 < A)
    (x : Space (n+2)) (w : Sphere (n+2)) : ‖f.multiplier A x w‖ ≤ A⁻¹ := by
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    _ ≤ (1*A⁻¹)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_nonneg.mpr hA.le))
      (f.angular_control.bound x w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem value_norm_le (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x : Space (n+2)) (w : Sphere (n+2)) :
    ‖f.value Q ρ m N σ J i S A x w‖ ≤ ((descriptorJetBound (n+2) K)^K)*A⁻¹ := by
  rw [value,norm_mul]
  exact mul_le_mul
    (descriptorJetProduct_norm_le Q ρ m N σ J i F id S
      (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)
      hsep f.order_le (fun b _ _ => (f.jet b).norm_vectors) x w)
    (f.multiplier_bound hA x w) (norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)

end DescriptorJetSymbol
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

theorem sphere_phase_norm {d : ℕ} (Λ : ℝ) (e w : Sphere d) :
    ‖Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
    sub_zero,Real.exp_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual products of two spherical oscillations

The leading expression keeps both signs at each stationary pole. Its
product therefore contains the four radial phases used in the comparable
far reduction. The error uses only norm bounds, never derivatives of a
stationary remainder.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem sphere_stationary_expansion_unscaled
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖sphereOscillation Λ e (fun w => B w)-stationarySphereApprox m J Λ B e‖ ≤
        A*Λ^(-(J : ℝ)-((m+2 : ℕ) : ℝ)/2)*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hAb⟩ := sphere_stationary_expansion hgnomonic hquadratic m J hJ
  refine ⟨A,hA,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let q : ℂ := ((Λ^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)
  let S := Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e+
    star (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ (antipodalConjugate B) e)
  have hqp : q*p = 1 := by
    dsimp only [p,q]
    rw [← Complex.ofReal_mul,← Real.rpow_add hΛp,neg_add_cancel,Real.rpow_zero,Complex.ofReal_one]
  have he : sphereOscillation Λ e (fun w => B w)-stationarySphereApprox m J Λ B e =
      q*(p*sphereOscillation Λ e (fun w => B w)-S) := by
    rw [mul_sub,← mul_assoc,hqp,one_mul]
    rfl
  rw [he,norm_mul]
  have hq : ‖q‖ = Λ^(-(((m+2 : ℕ) : ℝ)/2)) := by
    dsimp only [q]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hΛp _)]
  rw [hq]
  apply (mul_le_mul_of_nonneg_left (hAb e B hB C D hC hD hb Λ hΛ)
    (Real.rpow_pos_of_pos hΛp _).le).trans_eq
  calc
    _ = A*(Λ^(-(((m+2 : ℕ) : ℝ)/2))*Λ^(-(J : ℝ)))*C*D^(2*J+(m+2)+1) := by ring
    _ = _ := by
      rw [← Real.rpow_add hΛp,
        show -(((m+2 : ℕ) : ℝ)/2) + -(J : ℝ) = -(J : ℝ)-((m+2 : ℕ) : ℝ)/2 by ring]

theorem sphereOscillation_norm_le_of_bound {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (B : Sphere d → ℂ) {C : ℝ} (hB : ∀ w, ‖B w‖ ≤ C) :
    ‖sphereOscillation Λ e B‖ ≤ C*(sphereMeasure d).real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simpa only [norm_mul,sphere_phase_norm,one_mul] using hB w

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

 theorem ambient_sphere (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    f.ambient Q ρ m N σ J i S A x w = f.value Q ρ m N σ J i S A x w := by
  simp only [ambient,value,multiplier,Complex.ofReal_prod,
    normalizedAmbientDescriptorJet_sphere,descriptorJetProduct,id_eq]
  ring

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

 theorem pairAmbient_smooth (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y : Space (n+2)) :
    ContDiff ℝ ∞ (f.pairAmbient Q ρ m N σ J i S A x y) :=
  (f.ambient_smooth Q ρ m N σ J i S A x).mul
    (Complex.conjCLE.contDiff.comp (f.ambient_smooth Q ρ m N σ J i S A y))

 theorem pairAmbient_sphere (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y : Space (n+2)) (w : Sphere (n+2)) :
    f.pairAmbient Q ρ m N σ J i S A x y w =
      f.value Q ρ m N σ J i S A x w*star (f.value Q ρ m N σ J i S A y w) := by
  simp only [pairAmbient,ambient_sphere]

end DescriptorJetSymbol
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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SignedRadialKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SingleStationaryRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One stationary sphere against an unexpanded small displacement

Only the large sphere is expanded. The second displacement remains an
arbitrary scalar projection, bounded by the smaller displacement length.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem singleSignedRadial_derivatives (m j n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D Λ : ℝ, 0 ≤ C → 1 ≤ D → 0 < Λ → D^2 ≤ Λ →
      (∀ t ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ∀ (e : Sphere (m+3)) (ε : Bool),
      ContDiff ℝ ∞ (singleSignedRadialCoefficient m j Ψ B e Λ ε) ∧
      tsupport (singleSignedRadialCoefficient m j Ψ B e Λ ε) ⊆ Icc (1/4:ℝ) 4 ∧
      ∀ t ≤ n, ∀ s, ‖iteratedDeriv t (singleSignedRadialCoefficient m j Ψ B e Λ ε) s‖ ≤
        H*C*Λ^(-((m+2:ℕ):ℝ)/2) := by
  obtain ⟨H,hH,hcoeff⟩ := signedStationaryCoefficient_bound m j
  obtain ⟨P,hP,hprofile⟩ := PlanarFalconer.radialStationaryProfile_derivatives hΨ hs
    (-((m+2:ℕ):ℝ)/2-(j:ℝ)) n
  refine ⟨H*P,mul_nonneg hH hP,?_⟩
  intro B hB C D Λ hC hD hΛ hDΛ hb e ε
  refine ⟨contDiff_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (PlanarFalconer.radialStationaryProfile_tsupport hs _),?_⟩
  intro t ht s
  change ‖iteratedDeriv t (fun s =>
    (((Λ^(-((m+2:ℕ):ℝ)/2):ℝ):ℂ)*signedStationaryCoefficient m j Λ B e ε)*
      PlanarFalconer.radialStationaryProfile Ψ _ s) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hΛ _)]
  calc
    _ ≤ (Λ^(-((m+2:ℕ):ℝ)/2)*(H*C))*P := mul_le_mul
      (mul_le_mul_of_nonneg_left (hcoeff B hB C D Λ hC hD hΛ hDΛ hb e ε)
        (Real.rpow_nonneg hΛ.le _)) (hprofile t ht s) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hΛ.le _) (mul_nonneg hH hC))
    _ = _ := by ring

theorem singleSignedRadial_noncomparable (m j n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small t : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
      (∀ k ≤ 2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (e : Sphere (m+3)) (ε : Bool),
      ‖PlanarFalconer.radialPhaseIntegral
        (singleSignedRadialCoefficient m j Ψ B e (R*large) ε)
        (R*(stationarySign ε*large+t))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^n := by
  obtain ⟨H,hH,hder⟩ := singleSignedRadial_derivatives m j n hΨ hs
  refine ⟨H*(15/4),by positivity,?_⟩
  intro B hB C D R large small t hC hD hR hl hsep ht hDΛ hb e ε
  obtain ⟨ha,hsa,hba⟩ := hder B hB C D (R*large) hC hD (mul_pos hR hl) hDΛ hb e ε
  have hfreq : R*large/2 ≤ |R*(stationarySign ε*large+t)| := by
    rw [abs_mul,abs_of_pos hR]
    have hx := mul_le_mul_of_nonneg_left
      (PlanarFalconer.noncomparable_radial_frequency hsep ht (stationarySign_cases ε)) hR.le
    linarith
  have hpos : 0 < R*large/2 := by positivity
  have hne : R*(stationarySign ε*large+t) ≠ 0 := abs_pos.mp (hpos.trans_le hfreq)
  have h := PlanarFalconer.radialPhaseIntegral_nonzero ha hsa (by norm_num) hne n (hba n le_rfl)
  apply h.trans
  have he : H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)*((4:ℝ)-1/4) =
      (H*(15/4))*C*(R*large)^(-((m+2:ℕ):ℝ)/2) := by ring
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos n)
    (pow_le_pow_left₀ hpos.le hfreq n)

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SingleSphereRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial decay of one stationary sphere with an exact scalar phase -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem singleStationaryPole_radial (m j : ℕ) (Ψ : ℝ → ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d s : ℝ} (hR : 0 < R) (hd : 0 < d) (hs : 0 < s) (t : ℝ) (ε : Bool) :
    (Ψ s:ℂ)*stationaryPoleTerm m j (R*s*d) B e ε*stationaryPhase (R*s*t) =
      stationaryPhase ((R*(stationarySign ε*d+t))*s)*
        singleSignedRadialCoefficient m j Ψ B e (R*d) ε s := by
  let p : ℝ := ((m+2:ℕ):ℝ)/2
  have hpow : (R*s*d)^(-p) = (R*d)^(-p)*s^(-p) := by
    rw [show R*s*d = (R*d)*s by ring,Real.mul_rpow (mul_pos hR hd).le hs.le]
  have hpowers : s^(-p)*(s^j)⁻¹ = s^(-p-(j:ℝ)) := by
    rw [← Real.rpow_natCast s j,← Real.rpow_neg hs.le,← Real.rpow_add hs]
    congr 1
  have hphase : stationaryPhase (stationarySign ε*(R*s*d))*stationaryPhase (R*s*t) =
      stationaryPhase ((R*(stationarySign ε*d+t))*s) := by
    rw [stationaryPhase_mul]
    congr 1
    ring
  simp only [stationaryPoleTerm,neg_div]
  change (Ψ s:ℂ)*((((R*s*d)^(-p):ℝ):ℂ)*
    stationaryPhase (stationarySign ε*(R*s*d))*signedStationaryCoefficient m j (R*s*d) B e ε)*
    stationaryPhase (R*s*t) = _
  rw [hpow,signedStationaryCoefficient_scale]
  have halgebra : (Ψ s:ℂ)*((((R*d)^(-p)*s^(-p):ℝ):ℂ)*
      stationaryPhase (stationarySign ε*(R*s*d))*
      (((s^j)⁻¹:ℝ)*signedStationaryCoefficient m j (R*d) B e ε))*stationaryPhase (R*s*t) =
      (stationaryPhase (stationarySign ε*(R*s*d))*stationaryPhase (R*s*t))*
        ((R*d)^(-p):ℝ)*signedStationaryCoefficient m j (R*d) B e ε*
        ((Ψ s*(s^(-p)*(s^j)⁻¹):ℝ):ℂ) := by
    push_cast
    ring
  rw [halgebra,hphase,hpowers]
  dsimp only [singleSignedRadialCoefficient,PlanarFalconer.radialStationaryProfile,p]
  push_cast
  ring_nf

theorem singleSignedRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m j : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3)) (Λ ξ : ℝ) (ε : Bool) :
    Integrable (fun s : ℝ => stationaryPhase (ξ*s)*
      singleSignedRadialCoefficient m j Ψ B e Λ ε s) := by
  have hc : HasCompactSupport
      (PlanarFalconer.radialStationaryProfile Ψ (-((m+2:ℕ):ℝ)/2-(j:ℝ))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (PlanarFalconer.radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (singleSignedRadialCoefficient m j Ψ B e Λ ε) :=
    continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by unfold stationaryPhase; fun_prop :
    Continuous (fun s : ℝ => stationaryPhase (ξ*s))).mul hcont).integrable_of_hasCompactSupport
      hc.mul_left.mul_left

theorem single_sphere_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (t : ℝ) :
    R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d) B e*
      stationaryPhase (r*t)) =
    ∑ ε : Bool, ∑ j ∈ Finset.range J,
      PlanarFalconer.radialPhaseIntegral (singleSignedRadialCoefficient m j Ψ B e (R*d) ε)
        (R*(stationarySign ε*d+t)) := by
  let H := fun (ε : Bool) (j : ℕ) (s : ℝ) =>
    stationaryPhase ((R*(stationarySign ε*d+t))*s)*
      singleSignedRadialCoefficient m j Ψ B e (R*d) ε s
  have hi (ε : Bool) (j : ℕ) : Integrable (H ε j) :=
    singleSignedRadial_integrable hΨ hsupp m j B e (R*d) _ ε
  have he (s : ℝ) : (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e*
      stationaryPhase (R*s*t) = ∑ ε : Bool, ∑ j ∈ Finset.range J, H ε j s := by
    by_cases hs : 0 < s
    · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd)]
      conv_lhs => lhs; rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ε _
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact singleStationaryPole_radial m j Ψ B e hR hd hs t ε
    · have hz : Ψ s = 0 := by
        by_contra hn
        have hsp := (hsupp s hn).1
        linarith
      simp only [hz,Complex.ofReal_zero,zero_mul,H,singleSignedRadialCoefficient,
        PlanarFalconer.radialStationaryProfile,mul_zero,Finset.sum_const_zero]
  calc
    _ = ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e*stationaryPhase (R*s*t) := by
      have h := Measure.integral_comp_mul_left
        (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*d) B e*stationaryPhase (r*t)) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
        abs_of_pos (inv_pos.mpr hR)] using h.symm
    _ = ∫ s : ℝ, ∑ ε : Bool, ∑ j ∈ Finset.range J, H ε j s := by simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ => hi ε j))]
      apply Finset.sum_congr rfl
      intro ε _
      rw [integral_finsetSum _ (fun j _ => hi ε j)]
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards with s
      dsimp [H,stationaryPhase,PlanarFalconer.radialPhaseIntegral]
      congr 2
      push_cast
      ring

theorem single_sphere_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small t : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
      (∀ k ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ e : Sphere (m+3),
      ‖R⁻¹ • (∫ r : ℝ, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*
        stationaryPhase (r*t))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
  choose H hH hbound using fun j => singleSignedRadial_noncomparable m j q hΨ hs
  let Htotal := ∑ _ε : Bool, ∑ j ∈ Finset.range J, H j
  refine ⟨Htotal,Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun j _ => hH j)),?_⟩
  intro B hB C D R large small t hC hD hR hl hsep ht hscale hb e
  rw [single_sphere_radial_integral hΨ hs m J B e hR hl t]
  calc
    _ ≤ ∑ _ε : Bool, ∑ j ∈ Finset.range J,
        H j*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ε _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      exact hbound j B hB C D R large small t hC hD hR hl hsep ht hscale
        (fun k hk => hb k (hk.trans (Nat.mul_le_mul_left 2 (Nat.le_of_lt (Finset.mem_range.mp hj))))) e ε
    _ = _ := by simp only [Htotal,Finset.sum_mul,Finset.sum_div]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_RetainedSmallSphere
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smaller sphere remains an exact integral

No derivatives of the smaller amplitude are used. Its original value is
retained through Fubini, and only its absolute bound is used afterward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem single_profile_sum {Ψ : ℝ → ℝ}
    (hsupp : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (s : ℝ) :
    (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e =
      ∑ ε : Bool, ∑ j ∈ Finset.range J,
        stationaryPhase ((R*(stationarySign ε*d))*s)*
          singleSignedRadialCoefficient m j Ψ B e (R*d) ε s := by
  by_cases hs : 0 < s
  · rw [stationarySphereApprox_pole_sum m J (mul_pos (mul_pos hR hs) hd),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := singleStationaryPole_radial m j Ψ B e hR hd hs 0 ε
    simpa only [mul_zero,add_zero,stationaryPhase,Complex.ofReal_zero,mul_zero,
      Complex.exp_zero,mul_one] using h
  · have hz : Ψ s = 0 := by
      by_contra hn
      have hp := (hsupp s hn).1
      linarith
    simp only [hz,Complex.ofReal_zero,zero_mul,singleSignedRadialCoefficient,
      PlanarFalconer.radialStationaryProfile,mul_zero,Finset.sum_const_zero]

theorem stationary_profile_regular {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J : ℕ) (B : Space (m+3) → ℂ) (e : Sphere (m+3))
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) :
    Measurable (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) ∧
      Integrable (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) := by
  have he : (fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*d) B e) =
      fun s => ∑ ε : Bool, ∑ j ∈ Finset.range J,
        stationaryPhase ((R*(stationarySign ε*d))*s)*
          singleSignedRadialCoefficient m j Ψ B e (R*d) ε s :=
    funext (single_profile_sum hs m J B e hR hd)
  rw [he]
  constructor
  · apply Finset.measurable_sum _
    intro ε _
    apply Finset.measurable_sum _
    intro j _
    apply Continuous.measurable
    apply Continuous.mul
    · unfold stationaryPhase
      fun_prop
    · exact continuous_const.mul (PlanarFalconer.radialStationaryProfile_contDiff hΨ hs _).continuous
  · exact integrable_finsetSum _ (fun ε _ => integrable_finsetSum _ (fun j _ =>
      singleSignedRadial_integrable hΨ hs m j B e (R*d) _ ε))

private theorem radial_sphere_swap {d : ℕ} (F : ℝ → ℂ)
    (hFm : Measurable F) (hFi : Integrable F) (G : Sphere d → ℂ)
    (hG : Measurable G) {C : ℝ} (hGC : ∀ w, ‖G w‖ ≤ C)
    (T : ℝ) (e : Sphere d) :
    (∫ s : ℝ, F s*sphereOscillation (T*s) e G) =
      ∫ w : Sphere d, G w*(∫ s : ℝ,
        F s*stationaryPhase (s*(T*inner ℝ (w : Space d) (e : Space d)))) ∂sphereMeasure d := by
  let H := fun p : ℝ × Sphere d => F p.1*
    (Complex.exp (Complex.I*((T*p.1 : ℝ):ℂ)*(inner ℝ (p.2 : Space d) (e : Space d):ℂ))*G p.2)
  have hm : Measurable H := by
    apply Measurable.mul
    · exact hFm.comp measurable_fst
    · apply Measurable.mul
      · fun_prop
      · exact hG.comp measurable_snd
  have hi : Integrable H (volume.prod (sphereMeasure d)) := by
    apply ((hFi.norm.comp_fst (sphereMeasure d)).mul_const C).mono' hm.aestronglyMeasurable
    filter_upwards with p
    have hphase : ‖Complex.exp
        (Complex.I*((T*p.1 : ℝ):ℂ)*(inner ℝ (p.2 : Space d) (e : Space d):ℂ))‖ = 1 :=
      sphere_phase_norm (T*p.1) e p.2
    dsimp only [H]
    rw [norm_mul,norm_mul,hphase,one_mul]
    exact mul_le_mul_of_nonneg_left (hGC p.2) (norm_nonneg _)
  calc
    _ = ∫ s : ℝ, ∫ w : Sphere d, H (s,w) ∂sphereMeasure d := by
      simp only [sphereOscillation,H,integral_const_mul]
    _ = ∫ w : Sphere d, (∫ s : ℝ, H (s,w)) ∂sphereMeasure d :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      have he : Complex.exp (Complex.I*((T*s : ℝ):ℂ)*
          (inner ℝ (w : Space d) (e : Space d):ℂ)) =
          stationaryPhase (s*(T*inner ℝ (w : Space d) (e : Space d))) := by
        unfold stationaryPhase
        congr 1
        push_cast
        ring
      dsimp only [H]
      rw [he]
      ring

theorem single_sphere_retained_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (m J q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D R large small E : ℝ, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
      0 ≤ small → 2*small ≤ large → D^2 ≤ R*large →
      (∀ k ≤ 2*J, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (e f : Sphere (m+3)) (G : Sphere (m+3) → ℂ), Measurable G →
      (∀ w, ‖G w‖ ≤ E) →
      ‖∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J (R*s*large) B e*
        sphereOscillation (R*s*small) f G‖ ≤
      H*C*E*(sphereMeasure (m+3)).real univ*
        (R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
  obtain ⟨H,hH,hbound⟩ := single_sphere_radial_bound hΨ hs m J q
  refine ⟨H,hH,?_⟩
  intro B hB C D R large small E hC hD hR hl hsmall hsep hscale hb e f G hG hGE
  let F := fun s => (Ψ s:ℂ)*stationarySphereApprox m J (R*s*large) B e
  have hF := stationary_profile_regular hΨ hs m J B e hR hl
  have heq : (fun s => F s*sphereOscillation (R*s*small) f G) =
      fun s => F s*sphereOscillation ((R*small)*s) f G := by
    funext s
    rw [show R*s*small = (R*small)*s by ring]
  change ‖∫ s, F s*sphereOscillation (R*s*small) f G‖ ≤ _
  rw [heq,radial_sphere_swap F hF.1 hF.2 G hG hGE (R*small) f]
  have hbphase (w : Sphere (m+3)) :
      ‖∫ s, F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3))))‖ ≤
        H*C*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
    let t := small*inner ℝ (w : Space (m+3)) (f : Space (m+3))
    have ht : |t| ≤ small := by
      dsimp only [t]
      rw [abs_mul,abs_of_nonneg hsmall]
      calc
        _ ≤ small*1 := mul_le_mul_of_nonneg_left
          (by simpa only [sphere_norm,mul_one] using abs_real_inner_le_norm (w : Space (m+3)) (f : Space (m+3))) hsmall
        _ = small := mul_one _
    have h := hbound B hB C D R large small t hC hD hR hl hsep ht hscale hb e
    have hchange := Measure.integral_comp_mul_left
      (fun r : ℝ => (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*stationaryPhase (r*t)) R
    have hid : (R⁻¹ • ∫ r, (Ψ (r/R):ℂ)*stationarySphereApprox m J (r*large) B e*stationaryPhase (r*t)) =
        ∫ s, F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3)))) := by
      have hp : (fun s => (Ψ ((R*s)/R):ℂ)*stationarySphereApprox m J (R*s*large) B e*
          stationaryPhase ((R*s)*t)) =
          fun s => F s*stationaryPhase (s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3)))) := by
        funext s
        rw [mul_div_cancel_left₀ _ hR.ne']
        dsimp only [F,t]
        rw [show R*s*(small*inner ℝ (w : Space (m+3)) (f : Space (m+3))) =
          s*((R*small)*inner ℝ (w : Space (m+3)) (f : Space (m+3))) by ring]
      simpa only [abs_of_pos hR,abs_of_pos (inv_pos.mpr hR),hp] using hchange.symm
    rwa [hid] at h
  have hfinal := norm_integral_le_of_norm_le_const (μ := sphereMeasure (m+3))
    (Filter.Eventually.of_forall fun w => (norm_mul (G w) _).le.trans
      (mul_le_mul (hGE w) (hbphase w) (norm_nonneg _)
        ((norm_nonneg (G w)).trans (hGE w))))
  apply hfinal.trans_eq
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereFrequency
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable frequency parameters in the exact spherical expressions -/

namespace Falconer
open MeasureTheory

theorem sphereOscillation_frequency_measurable {d : ℕ} (e : Sphere d)
    (B : Sphere d → ℂ) (hB : Measurable B) :
    Measurable (fun r : ℝ => sphereOscillation r e B) := by
  have h : Measurable (fun z : ℝ × Sphere d =>
      Complex.exp (Complex.I*(z.1:ℂ)*
        (inner ℝ (z.2:Space d) (e:Space d):ℂ))*B z.2) := by
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem stationarySphereApprox_frequency_measurable (m J : ℕ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    Measurable (fun r : ℝ => stationarySphereApprox m J r B e) := by
  unfold stationarySphereApprox directStationarySum
  fun_prop

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

 theorem exists_jetState_far_sphere_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m₀ J K L : ℕ) (hJ : 1 ≤ J) (hL : 2*J+(m₀+2)+1 ≤ L) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J₀ i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m₀+1) K L F Dq) (x y : Space (m₀+3))
        (e : Sphere (m₀+3)) (Λ : ℝ), 1 ≤ Λ →
      ‖sphereOscillation Λ e (fun w => f.value Q ρ m N σ J₀ i S A x w*
            star (f.value Q ρ m N σ J₀ i S A y w))-
          stationarySphereApprox m₀ J Λ (f.pairAmbient Q ρ m N σ J₀ i S A x y) e‖ ≤
        C*Λ^(-(J:ℝ)-((m₀+2:ℕ):ℝ)/2)*(B^K*A⁻¹)^2*
          (2*(E+Dq))^(2*J+(m₀+2)+1) := by
  obtain ⟨B,hB,hbound⟩ := exists_descriptorJetSymbol_pair_budget (m₀+1) K L
  obtain ⟨C,hC,hstationary⟩ := sphere_stationary_expansion_unscaled hgnomonic hquadratic m₀ J hJ
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ m N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE f x y e Λ hΛ
  have hb (j : ℕ) (hj : j ≤ 2*J+(m₀+2)+1) (w : Sphere (m₀+3)) :=
    hbound F Q ρ m N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE f x y j (hj.trans hL) w
  have h := hstationary e (f.pairAmbient Q ρ m N σ J₀ i S A x y)
    (f.pairAmbient_smooth Q ρ m N σ J₀ i S A x y) ((B^K*A⁻¹)^2) (2*(E+Dq))
    (sq_nonneg _) hD hb Λ hΛ
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarRemainder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Power-saving remainders for the exact far-state amplitudes -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem stationary_sphere_remainder_scale (m J : ℕ) {R D Λ κ : ℝ}
    (hR : 1 ≤ R) (hD : 0 ≤ D) (hΛ : 1 ≤ Λ) (hupper : D ≤ R^2)
    (hratio : D^2/Λ ≤ R^(-κ)) :
    Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1) ≤
      R^(-κ*(J:ℝ)+2*(m+3)) := by
  have hp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hs := stationary_remainder_scale J (m+1) hR hD hp hupper hratio
  have hd : Λ^(-((m+2:ℕ):ℝ)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))
  have hJpow : Λ^(-(J:ℝ)) = (Λ⁻¹)^J := by
    rw [Real.rpow_neg hp.le, Real.rpow_natCast, inv_pow]
  have he : Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1) =
      Λ^(-((m+2:ℕ):ℝ)/2)*((Λ⁻¹)^J*D^(2*J+(m+1)+2)) := by
    rw [show -(J:ℝ)-((m+2:ℕ):ℝ)/2 = -(J:ℝ)+(-((m+2:ℕ):ℝ)/2) by ring,
      Real.rpow_add hp, hJpow,
      show 2*J+(m+2)+1 = 2*J+(m+1)+2 by omega]
    ring
  rw [he]
  have hexp : -κ*(J:ℝ)+2*(((m+1:ℕ):ℝ)+2) = -κ*(J:ℝ)+2*((m:ℝ)+3) := by
    push_cast
    ring
  rw [hexp] at hs
  exact (mul_le_mul_of_nonneg_right hd (by positivity)).trans (by simpa only [one_mul] using hs)

theorem exists_jetState_far_sphere_power
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J K L : ℕ) (hJ : 1 ≤ J) (hL : 2*J+(m+2)+1 ≤ L) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J₀ i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (x y : Space (m+3))
        (e : Sphere (m+3)) (R Λ κ : ℝ), 1 ≤ R → 1 ≤ Λ →
      2*(E+Dq) ≤ R^2 → (2*(E+Dq))^2/Λ ≤ R^(-κ) →
      ‖sphereOscillation Λ e (fun w => f.value Q ρ profile N σ J₀ i S A x w*
            star (f.value Q ρ profile N σ J₀ i S A y w))-
          stationarySphereApprox m J Λ (f.pairAmbient Q ρ profile N σ J₀ i S A x y) e‖ ≤
        C*(B^K*A⁻¹)^2*R^(-κ*(J:ℝ)+2*(m+3)) := by
  obtain ⟨B,C,hB,hC,h⟩ := exists_jetState_far_sphere_expansion hgnomonic hquadratic m J K L hJ hL
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f x y e R Λ κ hR hΛ hupper hratio
  have hraw := h F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f x y e Λ hΛ
  have hsmall := stationary_sphere_remainder_scale m J hR (zero_le_one.trans hD)
    hΛ hupper hratio
  apply hraw.trans
  calc
    _ = C*(B^K*A⁻¹)^2*(Λ^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*(2*(E+Dq))^(2*J+(m+2)+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC (sq_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NoncomparableSphereKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual noncomparable two-sphere kernel

The small sphere is never expanded. Only the large sphere incurs a
stationary remainder, and its bound uses the two existing published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem noncomparable_leading_decay_mono (m q : ℕ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    y^(-((m+2:ℕ):ℝ)/2)/(y/2)^q ≤ x^(-((m+2:ℕ):ℝ)/2)/(x/2)^q := by
  have hy : 0 < y := hx.trans_le hxy
  have hp : -((m+2:ℕ):ℝ)/2 ≤ 0 := by
    have hn : 0 ≤ ((m+2:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ x^(-((m+2:ℕ):ℝ)/2)/(y/2)^q := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hx hxy hp) (pow_nonneg (by positivity) _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _)
      (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)

theorem exists_noncomparable_sphere_kernel
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J q : ℕ) (hJ : 1 ≤ J) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ H S : ℝ, 0 ≤ H ∧ 0 ≤ S ∧
      ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (G : Sphere (m+3) → ℂ), Measurable G →
      ∀ E : ℝ, 0 ≤ E → (∀ w, ‖G w‖ ≤ E) →
      ∀ (e f : Sphere (m+3)) (v large small base κ : ℝ),
      0 < large → 0 ≤ small → 2*small ≤ large → 1 ≤ base →
      D^2 ≤ (2:ℝ)^v*large → D ≤ base^2 →
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        1 ≤ r*large ∧ D^2/(r*large) ≤ base^(-κ)) →
      let ε := S*C*base^(-κ*(J:ℝ)+2*(m+3))
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*large) e (fun w => B w)*sphereOscillation (r*small) f G)‖ ≤
        H*C*E*(sphereMeasure (m+3)).real univ*
          ((2:ℝ)^v*large)^(-((m+2:ℕ):ℝ)/2)/((2:ℝ)^v*large/2)^q +
        4*W*(ε*(2*(max C E*(sphereMeasure (m+3)).real univ)+ε)) := by
  obtain ⟨H,hH,hleading⟩ := single_sphere_retained_bound hΨ hs m J q
  obtain ⟨S,hS,hstationary⟩ := sphere_stationary_expansion_unscaled hgnomonic hquadratic m J hJ
  refine ⟨H,S,hH,hS,?_⟩
  intro B hB C D hC hD hb G hG E hE hGE e f v large small base κ
    hl hsmall hsep hbase hlead hDbase hregime
  let ε := S*C*base^(-κ*(J:ℝ)+2*(m+3))
  let A₀ := fun r => sphereOscillation (r*large) e (fun w => B w)
  let B₀ := fun r => sphereOscillation (r*small) f G
  let A₁ := fun r => stationarySphereApprox m J (r*large) B e
  let C₀ := max C E*(sphereMeasure (m+3)).real univ
  have hC₀ : 0 ≤ C₀ := mul_nonneg (hC.trans (le_max_left _ _)) measureReal_nonneg
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hBm : Measurable (fun w : Sphere (m+3) => B w) :=
    hB.continuous.measurable.comp continuous_subtype_val.measurable
  have hmA : Measurable A₀ := (sphereOscillation_frequency_measurable e _ hBm).comp (by fun_prop)
  have hmB : Measurable B₀ := (sphereOscillation_frequency_measurable f G hG).comp (by fun_prop)
  have hmA₁ : Measurable A₁ := (stationarySphereApprox_frequency_measurable m J B e).comp (by fun_prop)
  have hBbound (w : Sphere (m+3)) : ‖B w‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb 0 (by omega) w
  have hAbound (r : ℝ) : ‖A₀ r‖ ≤ C₀ :=
    (sphereOscillation_norm_le_of_bound _ _ _ hBbound).trans
      (mul_le_mul_of_nonneg_right (le_max_left C E) measureReal_nonneg)
  have hB₀bound (r : ℝ) : ‖B₀ r‖ ≤ C₀ :=
    (sphereOscillation_norm_le_of_bound _ _ _ hGE).trans
      (mul_le_mul_of_nonneg_right (le_max_right C E) measureReal_nonneg)
  have herror (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) : ‖A₀ r-A₁ r‖ ≤ ε := by
    obtain ⟨hΛ,hscale⟩ := hregime r hr
    have hraw := hstationary e B hB C D hC hD hb (r*large) hΛ
    have hp := stationary_sphere_remainder_scale m J hbase (zero_le_one.trans hD) hΛ hDbase hscale
    apply hraw.trans
    calc
      _ = (S*C)*((r*large)^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1)) := by ring
      _ ≤ ε := mul_le_mul_of_nonneg_left hp (mul_nonneg hS hC)
  have hreplace := PlanarFalconer.angular_radial_product_replacement v hΨ.continuous.measurable
    hpos hs hW hΨW A₀ B₀ A₁ B₀ hmA hmB hmA₁ hmB hC₀ hε hAbound hB₀bound
    herror (fun r _ => by simpa using hε)
  have hleadBound := hleading B hB C D ((2:ℝ)^v) large small E hC hD
    (Real.rpow_pos_of_pos (by norm_num) _) hl hsmall hsep hlead
    (fun k hk => hb k (by omega)) e f G hG hGE
  have hscale : ((2:ℝ)^v)⁻¹ •
      (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r)) =
      ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J ((2:ℝ)^v*s*large) B e*
        sphereOscillation ((2:ℝ)^v*s*small) f G := by
    have h := Measure.integral_comp_mul_left
      (fun r : ℝ => Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r)) ((2:ℝ)^v)
    have hR : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
    simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
      abs_of_pos (inv_pos.mpr hR),A₁,B₀,Complex.real_smul,mul_assoc] using h.symm
  have hsum : ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₀ r*B₀ r))‖ ≤
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r))‖ +
        4*W*(ε*(2*C₀+ε)) := by
    let X := ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₀ r*B₀ r))
    let Y := ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r))
    have htriangle : ‖X‖ ≤ ‖Y‖+‖X-Y‖ := by
      calc
        _ = ‖Y+(X-Y)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    exact htriangle.trans (add_le_add le_rfl hreplace)
  rw [hscale] at hsum
  have htotal := hsum.trans (add_le_add hleadBound le_rfl)
  simpa only [A₀,B₀,Complex.real_smul,mul_assoc,ε,C₀] using htotal

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DisplacementDepth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar dyadic selection for comparable positive displacements

The arithmetic is independent of dimension, angular energy and distance-set
estimates.
-/

namespace PlanarFalconer
open Set Metric

 theorem exists_displacement_depth {d : ℝ} (hd : 0 < d) :
    ∃ n : ℤ, (2:ℝ)^(-(n:ℝ)-1) < d ∧ d ≤ (2:ℝ)^(-(n:ℝ)) := by
  obtain ⟨m,hm⟩ := exists_mem_Ioc_zpow hd (by norm_num : (1:ℝ) < 2)
  refine ⟨-(m+1),?_,?_⟩
  · have he : -((-(m+1):ℤ):ℝ)-1 = (m:ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.1
  · have he : -((-(m+1):ℤ):ℝ) = ((m+1:ℤ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.2

 theorem comparable_displacement_depth {d₁ d₂ : ℝ} {a h : ℕ}
    (hupper : max d₁ d₂ ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hfar : 16*(2:ℝ)^(-(h:ℝ)) < max d₁ d₂)
    (hc₁ : max d₁ d₂ ≤ 2*d₁) (hc₂ : max d₁ d₂ ≤ 2*d₂) :
    ∃ b : ℕ, a+9 ≤ b ∧ b ≤ h+5 ∧
      (256*(2:ℝ)^(-(b:ℝ)) < d₁ ∧ d₁ ≤ 1024*(2:ℝ)^(-(b:ℝ))) ∧
      (256*(2:ℝ)^(-(b:ℝ)) < d₂ ∧ d₂ ≤ 1024*(2:ℝ)^(-(b:ℝ))) := by
  have hd : 0 < max d₁ d₂ := (by positivity : 0 < 16*(2:ℝ)^(-(h:ℝ))).trans hfar
  obtain ⟨n,hnlo,hnhi⟩ := exists_displacement_depth hd
  have haexp : (2:ℝ)^(-(n:ℝ)-1) < (2:ℝ)^(1-(a:ℝ)) := by
    have he : (2:ℝ)^(1-(a:ℝ)) = 2*(2:ℝ)^(-(a:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_one]
    rw [he]
    exact hnlo.trans_le hupper
  have haR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp haexp
  have hhExp : (2:ℝ)^(4-(h:ℝ)) < (2:ℝ)^(-(n:ℝ)) := by
    have he : (2:ℝ)^(4-(h:ℝ)) = 16*(2:ℝ)^(-(h:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    exact hfar.trans_le hnhi
  have hhR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hhExp
  have haZ : (a:ℤ)-2 < n := by exact_mod_cast (show (a:ℝ)-2 < (n:ℝ) by linarith)
  have hhZ : n < (h:ℤ)-4 := by exact_mod_cast (show (n:ℝ) < (h:ℝ)-4 by linarith)
  have hb0 : 0 ≤ n+10 := by omega
  let b := (n+10).toNat
  have hbZ : (b:ℤ) = n+10 := Int.toNat_of_nonneg hb0
  have hbR : (b:ℝ) = (n:ℝ)+10 := by exact_mod_cast hbZ
  have hpow : (2:ℝ)^(-(n:ℝ)) = 1024*(2:ℝ)^(-(b:ℝ)) := by
    rw [hbR,show -(n:ℝ) = 10+(-((n:ℝ)+10)) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hhalf : (2:ℝ)^(-(n:ℝ)-1) = 512*(2:ℝ)^(-(b:ℝ)) := by
    rw [hbR,show -(n:ℝ)-1 = 9+(-((n:ℝ)+10)) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [hpow] at hnhi
  rw [hhalf] at hnlo
  refine ⟨b,?_,?_,?_,?_⟩
  · omega
  · omega
  · exact ⟨by linarith, (le_max_left _ _).trans hnhi⟩
  · exact ⟨by linarith, (le_max_right _ _).trans hnhi⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarRebin
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common dyadic depth for the two comparable far displacements

The scalar depth-selection argument applies to arbitrary displacements
and ambient dimensions.
-/

namespace Falconer

theorem comparable_displacement_depth_dimensional (d : ℕ)
    {d₁ d₂ : ℝ} {a h : ℕ}
    (hupper : max d₁ d₂ ≤ 2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)))
    (hfar : 8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max d₁ d₂)
    (hc₁ : max d₁ d₂ ≤ 2*d₁) (hc₂ : max d₁ d₂ ≤ 2*d₂) :
    ∃ b : ℕ, a+9 ≤ b ∧ b ≤ h+6 ∧
      (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < d₁ ∧
        d₁ ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) ∧
      (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < d₂ ∧
        d₂ ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  have he : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) =
      max d₁ d₂/((d:ℝ)+1) := max_div_div_right hd.le _ _
  have hu : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
    rw [he]
    apply (div_le_iff₀ hd).mpr
    nlinarith [hupper]
  have hs : 16*(2:ℝ)^(-((h+1:ℕ):ℝ)) <
      max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) := by
    rw [he]
    have hp : (2:ℝ)^(-((h+1:ℕ):ℝ)) = (2:ℝ)^(-(h:ℝ))/2 := by
      rw [Nat.cast_add,Nat.cast_one,neg_add,Real.rpow_add (by norm_num)]
      norm_num [div_eq_mul_inv]
    rw [hp]
    apply (lt_div_iff₀ hd).mpr
    nlinarith [hfar]
  have hc₁' : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(d₁/((d:ℝ)+1)) := by
    rw [he]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc₁ hd.le
  have hc₂' : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(d₂/((d:ℝ)+1)) := by
    rw [he]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc₂ hd.le
  obtain ⟨b,hba,hbh,hb₁,hb₂⟩ :=
    PlanarFalconer.comparable_displacement_depth hu hs hc₁' hc₂'
  refine ⟨b,hba,by omega,?_,?_⟩
  · constructor
    · have hh := (lt_div_iff₀ hd).mp hb₁.1
      nlinarith [hh]
    · have hh := (div_le_iff₀ hd).mp hb₁.2
      nlinarith [hh]
  · constructor
    · have hh := (lt_div_iff₀ hd).mp hb₂.1
      nlinarith [hh]
    · have hh := (div_le_iff₀ hd).mp hb₂.2
      nlinarith [hh]

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

theorem comparableFarRegion_covered (d a h : ℕ)
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableFarRegion d a h) :
    ∃ b ∈ Finset.Icc (a+9) (h+6), z ∈ comparableLengthBand d b := by
  obtain ⟨b,hba,hbh,h₁,h₂⟩ := comparable_displacement_depth_dimensional d hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact ⟨b,Finset.mem_Icc.mpr ⟨hba,hbh⟩,h₁,h₂⟩

theorem lintegral_comparable_bands_le (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞)
    {U : Set ((Space d × Space d) × (Space d × Space d))}
    (hU : U ⊆ comparableFarRegion d a h) :
    (∫⁻ z in U, F z ∂μ) ≤ ∑ b ∈ Finset.Icc (a+9) (h+6),
      ∫⁻ z in U ∩ comparableLengthBand d b, F z ∂μ := by
  let B := Finset.Icc (a+9) (h+6)
  have hcover : U ⊆ ⋃ b : B, U ∩ comparableLengthBand d b.1 := by
    intro z hz
    obtain ⟨b,hb,hzb⟩ := comparableFarRegion_covered d a h (hU hz)
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,hz,hzb⟩
  calc
    _ ≤ ∫⁻ z in ⋃ b : B, U ∩ comparableLengthBand d b.1, F z ∂μ :=
      lintegral_mono' (Measure.restrict_mono_set μ hcover) (fun _ => le_rfl)
    _ ≤ ∑' b : B, ∫⁻ z in U ∩ comparableLengthBand d b.1, F z ∂μ :=
      lintegral_iUnion_le _ _
    _ = _ := by rw [tsum_fintype]; exact Finset.sum_attach B (fun b => ∫⁻ z in U ∩ comparableLengthBand d b, F z ∂μ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NoncomparableKernelScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform powers for noncomparable radial kernels

The radial integration-by-parts order and the stationary expansion order
remain explicit. These scalar estimates convert their two different errors
to one prescribed power of the ambient scale.
-/

namespace Falconer

theorem noncomparable_leading_decay_eq (m q : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q =
      (2:ℝ)^q*Λ^(-((m+2:ℕ):ℝ)/2-(q:ℝ)) := by
  rw [show -((m+2:ℕ):ℝ)/2-(q:ℝ) =
    -((m+2:ℕ):ℝ)/2+(-(q:ℝ)) by ring,
    Real.rpow_add hΛ, Real.rpow_neg hΛ.le, Real.rpow_natCast, div_pow]
  field_simp

theorem noncomparable_leading_scale (m q : ℕ) {R Λ κ : ℝ}
    (hR : 0 < R) (hΛ : R^κ ≤ Λ) :
    Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q ≤
      (2:ℝ)^q*R^(-κ*(((m+2:ℕ):ℝ)/2+(q:ℝ))) := by
  have hp : 0 < R^κ := Real.rpow_pos_of_pos hR _
  have h := noncomparable_leading_decay_mono m q hp hΛ
  rw [noncomparable_leading_decay_eq m q hp] at h
  apply h.trans_eq
  congr 1
  rw [← Real.rpow_mul hR.le]
  congr 1
  ring

theorem noncomparable_stationary_error_scale {R exponent loss W S C M : ℝ}
    (hR : 1 ≤ R) (hloss : 0 ≤ loss) (hexponent : exponent ≤ -loss)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    4*W*((S*C*R^exponent)*(2*M+S*C*R^exponent)) ≤
      (4*W*S*C*(2*M+S*C))*R^(-loss) := by
  have hpow : R^exponent ≤ R^(-loss) := Real.rpow_le_rpow_of_exponent_le hR hexponent
  have hunit : R^(-loss) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (neg_nonpos.mpr hloss)
  have hSC : 0 ≤ S*C := mul_nonneg hS hC
  have he : S*C*R^exponent ≤ S*C*R^(-loss) :=
    mul_le_mul_of_nonneg_left hpow hSC
  have heunit : S*C*R^exponent ≤ S*C :=
    he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hSC)
  calc
    _ ≤ 4*W*((S*C*R^(-loss))*(2*M+S*C)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul he (add_le_add le_rfl heunit) (by positivity) (by positivity))
        (by positivity)
    _ = _ := by ring

theorem noncomparable_kernel_scale {m J q : ℕ} {R Λ κ loss H W S C E M : ℝ}
    (hR : 1 ≤ R) (hΛ : R^κ ≤ Λ) (hloss : 0 ≤ loss)
    (hleading : loss ≤ κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)))
    (hexponent : -κ*(J:ℝ)+2*(m+3) ≤ -loss)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hM : 0 ≤ M) :
    H*C*E*M*Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q +
        4*W*((S*C*R^(-κ*(J:ℝ)+2*(m+3)))*
          (2*(max C E*M)+S*C*R^(-κ*(J:ℝ)+2*(m+3)))) ≤
      (H*C*E*M*(2:ℝ)^q + 4*W*S*C*(2*(max C E*M)+S*C))*R^(-loss) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hc : 0 ≤ H*C*E*M := by positivity
  have hdecay := noncomparable_leading_scale m q hRpos hΛ
  have hpower : R^(-κ*(((m+2:ℕ):ℝ)/2+(q:ℝ))) ≤ R^(-loss) :=
    Real.rpow_le_rpow_of_exponent_le hR (by simpa only [neg_mul] using neg_le_neg hleading)
  have hleadingBound : H*C*E*M*Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q ≤
      (H*C*E*M*(2:ℝ)^q)*R^(-loss) := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hdecay hc).trans
      (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hpower
        (mul_nonneg hc (pow_nonneg (by norm_num) q))))
  have herror := noncomparable_stationary_error_scale (M := max C E*M)
    hR hloss hexponent hW hS hC (mul_nonneg (hC.trans (le_max_left C E)) hM)
  calc
    _ ≤ _ := add_le_add hleadingBound herror
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateNoncomparableFull
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Noncomparable decay for the original two descriptor-state spheres -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_noncomparable_full_kernel
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J q : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B H S : ℝ, 1 ≤ B ∧ 0 ≤ H ∧ 0 ≤ S ∧
      ∀ (F G : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A A' : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A → 0 < A' →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
        (x x' y y' : Space (m+3)) (e e' : Sphere (m+3))
        (v large small base κ : ℝ),
      0 < large → 0 ≤ small → 2*small ≤ large → 1 ≤ base →
      (2*(E+Dq))^2 ≤ (2:ℝ)^v*large → 2*(E+Dq) ≤ base^2 →
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        1 ≤ r*large ∧ (2*(E+Dq))^2/(r*large) ≤ base^(-κ)) →
      let C₁ := (B^K*A⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*A'⁻¹)^2
      let ε := S*C₁*base^(-κ*(J:ℝ)+2*(m+3))
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*large) e (fun w => f.value Q ρ profile N σ J₀ i T A x w*
          star (f.value Q ρ profile N σ J₀ i T A x' w))*
        sphereOscillation (r*small) e' (fun w => g.value Q ρ profile N σ J₀ i T A' y w*
          star (g.value Q ρ profile N σ J₀ i T A' y' w)))‖ ≤
        H*C₁*C₂*(sphereMeasure (m+3)).real univ*
          ((2:ℝ)^v*large)^(-((m+2:ℕ):ℝ)/2)/((2:ℝ)^v*large/2)^q +
        4*W*(ε*(2*(max C₁ C₂*(sphereMeasure (m+3)).real univ)+ε)) := by
  obtain ⟨B,hB,hbudget⟩ := exists_descriptorJetSymbol_pair_budget (m+1) K L
  obtain ⟨H,S,hH,hS,hkernel⟩ := exists_noncomparable_sphere_kernel
    hgnomonic hquadratic m J q hJ hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E A A' hDq hDm hA hA' hD
    hscale hE f g x x' y y' e e' v large small base κ hl hsmall hsep hbase hlead hDbase hregime
  have hder (k : ℕ) (hk : k ≤ 2*J+(m+2)+1) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hscale hE f x x' k
      (hk.trans hJL) w
  have hsmallBound (w : Sphere (m+3)) :
      ‖g.pairAmbient Q ρ profile N σ J₀ i T A' y y' w‖ ≤
        ((descriptorJetBound (m+3) K)^K*A'⁻¹)^2 := by
    rw [g.pairAmbient_sphere,norm_mul,norm_star,pow_two]
    exact mul_le_mul (g.value_norm_le Q ρ profile N σ J₀ i T hG hA' y w)
      (g.value_norm_le Q ρ profile N σ J₀ i T hG hA' y' w) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
        (inv_nonneg.mpr hA'.le))
  have h := hkernel (f.pairAmbient Q ρ profile N σ J₀ i T A x x')
    (f.pairAmbient_smooth Q ρ profile N σ J₀ i T A x x') _ _ (sq_nonneg _) hD hder
    (fun w => g.pairAmbient Q ρ profile N σ J₀ i T A' y y' w)
    ((g.pairAmbient_smooth Q ρ profile N σ J₀ i T A' y y').continuous.measurable.comp
      continuous_subtype_val.measurable) _ (sq_nonneg _) hsmallBound
    e e' v large small base κ hl hsmall hsep hbase hlead hDbase hregime
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NoncomparableOriginalIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The noncomparable contribution on the original four-point law -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem jetStateOriginalKernel_eq_volume {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (T : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag v : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hzero : ∀ s ≤ 0, Ψ s = 0)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) :
    jetStateOriginalKernel f g w₀ Q ρ profile N σ J i T Af Ag v Ψ z =
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*dist z.1.1 z.1.2) (normalizeToSphere w₀ (z.1.1-z.1.2))
          (fun w => f.value Q ρ profile N σ J i T Af z.1.1 w *
            star (f.value Q ρ profile N σ J i T Af z.1.2 w)) *
        sphereOscillation (r*dist z.2.1 z.2.2) (normalizeToSphere w₀ (z.2.1-z.2.2))
          (fun w => g.value Q ρ profile N σ J i T Ag z.2.1 w *
            star (g.value Q ρ profile N σ J i T Ag z.2.2 w))) := by
  rw [jetStateOriginalKernel,PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero]
  simp only [Complex.real_smul,mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NoncomparableOriginalPointwise
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise noncomparable decay before nonnegative integration -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ENNReal
open PlanarFalconer (PolicyDescriptor)

theorem jetStateOriginalKernel_swap {m K L : ℕ} {F G : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (T : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag v : ℝ) (Ψ : ℝ → ℝ)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) :
    jetStateOriginalKernel g f w₀ Q ρ profile N σ J i T Ag Af v Ψ (z.2,z.1) =
      jetStateOriginalKernel f g w₀ Q ρ profile N σ J i T Af Ag v Ψ z := by
  unfold jetStateOriginalKernel
  apply integral_congr_ae
  filter_upwards with r
  exact mul_comm _ _

theorem exists_jetState_noncomparable_original_pointwise
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J q : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B H S : ℝ, 1 ≤ B ∧ 0 ≤ H ∧ 0 ≤ S ∧
      ∀ (F G : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E Af Ag : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Af → 0 < Ag →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
        (w₀ : Sphere (m+3)) (v base κ loss : ℝ),
      1 ≤ base → 0 ≤ loss → loss ≤ κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -κ*(J:ℝ)+2*(m+3) ≤ -loss → 2*(E+Dq) ≤ base^2 →
      ∀ z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)),
      0 < dist z.1.1 z.1.2 → 2*dist z.2.1 z.2.2 ≤ dist z.1.1 z.1.2 →
      (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.1.1 z.1.2 →
      base^κ ≤ (2:ℝ)^v*dist z.1.1 z.1.2 →
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) →
      let C₁ := (B^K*Af⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*Ag⁻¹)^2
      let M := (sphereMeasure (m+3)).real univ
      ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T Af Ag v Ψ z‖ ≤
        (H*C₁*C₂*M*(2:ℝ)^q + 4*W*S*C₁*(2*(max C₁ C₂*M)+S*C₁))*base^(-loss) := by
  obtain ⟨B,H,S,hB,hH,hS,hkernel⟩ := exists_jetState_noncomparable_full_kernel
    hgnomonic hquadratic m K L J q hJ hJL hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E Af Ag hDq hDm hAf hAg hD
    hscale hE f g w₀ v base κ loss hbase hloss hlead hexp hupper z hl hsep hDlarge hfreq hr
  have hzero (s : ℝ) (h : s ≤ 0) : Ψ s = 0 := by
    by_contra hn
    have hp := (hs s hn).1
    linarith
  rw [jetStateOriginalKernel_eq_volume f g w₀ Q ρ profile N σ J₀ i T Af Ag v
    hΨ.continuous.measurable hpos hzero z]
  have hp := hkernel F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E Af Ag
    hDq hDm hAf hAg hD hscale hE f g z.1.1 z.1.2 z.2.1 z.2.2
    (normalizeToSphere w₀ (z.1.1-z.1.2)) (normalizeToSphere w₀ (z.2.1-z.2.2))
    v _ _ base κ hl dist_nonneg hsep hbase hDlarge hupper hr
  exact hp.trans (noncomparable_kernel_scale hbase hfreq hloss hlead hexp hH hW hS
    (sq_nonneg _) (sq_nonneg _) measureReal_nonneg)

theorem lintegral_norm_restrict_le_of_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {U : Set X} (hU : MeasurableSet U) (f : X → ℂ) {C : ℝ}
    (hbound : ∀ x ∈ U, ‖f x‖ ≤ C) :
    (∫⁻ x in U, ENNReal.ofReal ‖f x‖ ∂μ) ≤ ENNReal.ofReal C*μ U := by
  calc
    _ ≤ ∫⁻ _x in U, ENNReal.ofReal C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FarOriginalSupport
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Far-label elimination under a positive original-law bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem farDisplacementRegion_measurable (d a h : ℕ) :
    MeasurableSet (farDisplacementRegion d a h) := by
  have hm : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)) := by fun_prop
  exact (measurableSet_le hm measurable_const).inter
    (measurableSet_lt measurable_const hm)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarRegionSplit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two noncomparable pieces and finite comparable bands -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

theorem leftNoncomparableFar_measurable (d a h : ℕ) :
    MeasurableSet (leftNoncomparableFar d a h) := by
  apply (farDisplacementRegion_measurable d a h).inter
  exact measurableSet_lt
    (show Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      2*dist z.2.1 z.2.2) by fun_prop)
    (by fun_prop)

theorem rightNoncomparableFar_measurable (d a h : ℕ) :
    MeasurableSet (rightNoncomparableFar d a h) := by
  apply (farDisplacementRegion_measurable d a h).inter
  exact measurableSet_lt
    (show Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
      2*dist z.1.1 z.1.2) by fun_prop)
    (by fun_prop)

theorem farDisplacementRegion_subset_split (d a h : ℕ) :
    farDisplacementRegion d a h ⊆
      (leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h) ∪ comparableFarRegion d a h := by
  intro z hz
  by_cases hl : 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2
  · exact Or.inl (Or.inl ⟨hz,hl⟩)
  by_cases hr : 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2
  · exact Or.inl (Or.inr ⟨hz,hr⟩)
  apply Or.inr
  refine ⟨hz.1,hz.2,max_le ?_ (le_of_not_gt hr),max_le (le_of_not_gt hl) ?_⟩
  · have hd : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
    linarith
  · have hd : 0 ≤ dist z.2.1 z.2.2 := dist_nonneg
    linarith

theorem lintegral_far_split_bands (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∫⁻ z in farDisplacementRegion d a h, F z ∂μ) ≤
      (∫⁻ z in leftNoncomparableFar d a h, F z ∂μ) +
      (∫⁻ z in rightNoncomparableFar d a h, F z ∂μ) +
      ∑ b ∈ Finset.Icc (a+9) (h+6),
        ∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b, F z ∂μ := by
  calc
    _ ≤ ∫⁻ z in (leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h) ∪
        comparableFarRegion d a h, F z ∂μ :=
      lintegral_mono' (Measure.restrict_mono_set μ (farDisplacementRegion_subset_split d a h))
        (fun _ => le_rfl)
    _ ≤ (∫⁻ z in leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h, F z ∂μ) +
        ∫⁻ z in comparableFarRegion d a h, F z ∂μ := lintegral_union_le _ _ _
    _ ≤ _ := add_le_add (lintegral_union_le _ _ _)
      (lintegral_comparable_bands_le d a h μ F (subset_refl _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarRegionScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform shell regimes throughout the actual far region -/

namespace Falconer
open Set MeasureTheory

 theorem shell_regime_of_lower_distance {Ψ : ℝ → ℝ}
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    (v D base κ ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : ℓ ≤ d)
    (hfreq : 1 ≤ ((2:ℝ)^v/4)*ℓ)
    (hscale : D^2/(((2:ℝ)^v/4)*ℓ) ≤ base^(-κ)) :
    ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 → 1 ≤ r*d ∧ D^2/(r*d) ≤ base^(-κ) := by
  intro r hr
  have h2 : 0 < (2:ℝ)^v := by positivity
  have hr0 : (2:ℝ)^v/4 < r := by
    have hh := (lt_div_iff₀ h2).mp (hs _ hr).1
    linarith
  have hmin : 0 < ((2:ℝ)^v/4)*ℓ := mul_pos (by positivity) hℓ
  have hlower : ((2:ℝ)^v/4)*ℓ ≤ r*d :=
    mul_le_mul hr0.le hd hℓ.le (by linarith)
  exact ⟨hfreq.trans hlower,
    (div_le_div_of_nonneg_left (sq_nonneg D) hmin hlower).trans hscale⟩

 theorem comparableFarRegion_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ comparableFarRegion d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.1.1 z.1.2 ∧
      4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.2.1 z.2.2 := by
  constructor <;> linarith [hz.2.1,hz.2.2.1,hz.2.2.2]

 theorem leftNoncomparableFar_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ leftNoncomparableFar d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.1.1 z.1.2 := by
  have hsep : 2*dist z.2.1 z.2.2 < dist z.1.1 z.1.2 := hz.2
  have hnonneg : 0 ≤ dist z.2.1 z.2.2 := dist_nonneg
  have he : max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) = dist z.1.1 z.1.2 :=
    max_eq_left (by linarith)
  have hh := hz.1.2
  rw [he] at hh
  have hp : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by positivity
  linarith

 theorem rightNoncomparableFar_lower {d a h : ℕ}
    {z : (Space d × Space d) × (Space d × Space d)}
    (hz : z ∈ rightNoncomparableFar d a h) :
    4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ≤ dist z.2.1 z.2.2 := by
  have hsep : 2*dist z.1.1 z.1.2 < dist z.2.1 z.2.2 := hz.2
  have hnonneg : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
  have he : max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) = dist z.2.1 z.2.2 :=
    max_eq_right (by linarith)
  have hh := hz.1.2
  rw [he] at hh
  have hp : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by positivity
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NoncomparableCommonBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common normalization for both original noncomparable factors -/

namespace Falconer

theorem noncomparable_coefficient_common {H W S M c₁ c₂ u v : ℝ}
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₁u : c₁ ≤ u) (h₂u : c₂ ≤ u) :
    H*c₁*c₂*M*v+4*W*S*c₁*(2*(max c₁ c₂*M)+S*c₁) ≤
      (H*M*v+4*W*S*(2*M+S))*u^2 := by
  have hm := max_le h₁u h₂u
  calc
    _ ≤ H*u*u*M*v+4*W*S*u*(2*(u*M)+S*u) := by gcongr
    _ = _ := by ring

 theorem normalized_jet_bound_mono {B C A : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C)
    (hA : 0 < A) (K p : ℕ) : (B^K*A⁻¹)^p ≤ (C^K*A⁻¹)^p :=
  pow_le_pow_left₀ (mul_nonneg (pow_nonneg hB _) (inv_nonneg.mpr hA.le))
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hBC K) (inv_nonneg.mpr hA.le)) p

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OriginalStationaryReplacement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial replacement of the original two-sphere kernel

Both endpoint amplitudes are the original recursive symbols. The estimate
is pointwise in all four endpoints, so its norm can subsequently be
integrated without any spatial measurability assertion for stationary jets.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem state_pair_sphere_measurable {m K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (T : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x y : Space (m+3)) :
    Measurable (fun w : Sphere (m+3) => f.value Q ρ profile N σ J i T A x w *
      star (f.value Q ρ profile N σ J i T A y w)) := by
  have hm : Measurable (fun w : Sphere (m+3) =>
      f.pairAmbient Q ρ profile N σ J i T A x y (w : Space (m+3))) :=
    (f.pairAmbient_smooth Q ρ profile N σ J i T A x y).continuous.measurable.comp
      continuous_subtype_val.measurable
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using hm

private theorem state_pair_sphere_bound {m K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (T : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x y : Space (m+3)) (r : ℝ) (e : Sphere (m+3)) :
    ‖sphereOscillation r e (fun w => f.value Q ρ profile N σ J i T A x w *
      star (f.value Q ρ profile N σ J i T A y w))‖ ≤
      ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ := by
  apply sphereOscillation_norm_le_of_bound
  intro w
  rw [norm_mul,norm_star,pow_two]
  exact mul_le_mul (f.value_norm_le Q ρ profile N σ J i T hF hA x w)
    (f.value_norm_le Q ρ profile N σ J i T hF hA y w) (norm_nonneg _)
    (mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
      (inv_nonneg.mpr hA.le))

theorem exists_jetState_original_stationary_replacement
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (w₀ : Sphere (m+3))
        (v base κ : ℝ), 1 ≤ base → 2*(E+Dq) ≤ base^2 →
      ∀ z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)),
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        (1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) ∧
        (1 ≤ r*dist z.2.1 z.2.2 ∧ (2*(E+Dq))^2/(r*dist z.2.1 z.2.2) ≤ base^(-κ))) →
      let ε := C*(B^K*A⁻¹)^2*base^(-κ*(J:ℝ)+2*(m+3))
      let M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ
      ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T A A v Ψ z -
        jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i T A J ((2:ℝ)^v) Ψ z‖ ≤
        4*W*(ε*(2*M+ε)) := by
  obtain ⟨B,C,hB,hC,hpower⟩ := exists_jetState_far_sphere_power
    hgnomonic hquadratic m J K L hJ hJL
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
    f g w₀ v base κ hbase hupper z hregime
  let e := normalizeToSphere w₀ (z.1.1-z.1.2)
  let e' := normalizeToSphere w₀ (z.2.1-z.2.2)
  let Af : ℝ → ℂ := fun r => sphereOscillation (r*dist z.1.1 z.1.2) e
    (fun w => f.value Q ρ profile N σ J₀ i T A z.1.1 w *
      star (f.value Q ρ profile N σ J₀ i T A z.1.2 w))
  let Ag : ℝ → ℂ := fun r => sphereOscillation (r*dist z.2.1 z.2.2) e'
    (fun w => g.value Q ρ profile N σ J₀ i T A z.2.1 w *
      star (g.value Q ρ profile N σ J₀ i T A z.2.2 w))
  let Pf : ℝ → ℂ := fun r => stationarySphereApprox m J (r*dist z.1.1 z.1.2)
    (f.pairAmbient Q ρ profile N σ J₀ i T A z.1.1 z.1.2) e
  let Pg : ℝ → ℂ := fun r => stationarySphereApprox m J (r*dist z.2.1 z.2.2)
    (g.pairAmbient Q ρ profile N σ J₀ i T A z.2.1 z.2.2) e'
  let ε := C*(B^K*A⁻¹)^2*base^(-κ*(J:ℝ)+2*(m+3))
  let M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg _) measureReal_nonneg
  have hfm := state_pair_sphere_measurable f Q ρ profile N σ J₀ i T A z.1.1 z.1.2
  have hgm := state_pair_sphere_measurable g Q ρ profile N σ J₀ i T A z.2.1 z.2.2
  have hAf : Measurable Af := (sphereOscillation_frequency_measurable e _
    hfm).comp (by fun_prop)
  have hAg : Measurable Ag := (sphereOscillation_frequency_measurable e' _
    hgm).comp (by fun_prop)
  have hPf : Measurable Pf := (stationarySphereApprox_frequency_measurable m J _ e).comp (by fun_prop)
  have hPg : Measurable Pg := (stationarySphereApprox_frequency_measurable m J _ e').comp (by fun_prop)
  have herrorf (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :=
    hpower F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
      f z.1.1 z.1.2 e base (r*dist z.1.1 z.1.2) κ hbase (hregime r hr).1.1
      hupper (hregime r hr).1.2
  have herrorg (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :=
    hpower F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
      g z.2.1 z.2.2 e' base (r*dist z.2.1 z.2.2) κ hbase (hregime r hr).2.1
      hupper (hregime r hr).2.2
  have h := PlanarFalconer.angular_radial_product_replacement v hΨ hpos hs hW hΨW
    Af Ag Pf Pg hAf hAg hPf hPg (C := M) (ε := ε) hM hε
    (fun r => state_pair_sphere_bound f Q ρ profile N σ J₀ i T hF hA _ _ _ _)
    (fun r => state_pair_sphere_bound g Q ρ profile N σ J₀ i T hF hA _ _ _ _)
    herrorf herrorg
  have hzero (s : ℝ) (hz : s ≤ 0) : Ψ s = 0 := by
    by_contra hn
    have hp := (hs s hn).1
    linarith
  rw [jetStateOriginalKernel_eq_volume f g w₀ Q ρ profile N σ J₀ i T A A v hΨ hpos hzero z]
  simpa only [Af,Ag,Pf,Pg,e,e',ε,M,jetStateStationaryKernel,Complex.real_smul,mul_assoc] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OriginalStationaryPower
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform power loss for the actual radial replacement

The constant and derivative scale are selected before the descriptor list.
The four endpoint normalization factors remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_original_stationary_power
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (w₀ : Sphere (m+3))
        (v base κ loss : ℝ), 1 ≤ base → 0 ≤ loss →
      -κ*(J:ℝ)+2*(m+3) ≤ -loss → 2*(E+Dq) ≤ base^2 →
      ∀ z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)),
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        (1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) ∧
        (1 ≤ r*dist z.2.1 z.2.2 ∧ (2*(E+Dq))^2/(r*dist z.2.1 z.2.2) ≤ base^(-κ))) →
      ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T A A v Ψ z -
        jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i T A J ((2:ℝ)^v) Ψ z‖ ≤
        C*(B^K*A⁻¹)^4*base^(-loss) := by
  obtain ⟨B₀,C₀,hB₀,hC₀,hreplace⟩ := exists_jetState_original_stationary_replacement
    hgnomonic hquadratic m K L J hJ hJL hΨ hpos hs hW hΨW
  let B := max B₀ (descriptorJetBound (m+3) K)
  let C := 4*W*C₀*(2*(sphereMeasure (m+3)).real univ+C₀)
  have hB : 1 ≤ B := hB₀.trans (le_max_left _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
    f g w₀ v base κ loss hbase hloss hexp hupper z hregime
  have hE₀ : (F.card:ℝ)*B₀*Dmask ≤ E := by
    apply le_trans _ hE
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left B₀ _) (Nat.cast_nonneg _))
      (zero_le_one.trans hDm)
  have hp := hreplace F Q ρ profile N σ J₀ i T hF Dq Dmask E A
    hDq hDm hA hD hscale hE₀ f g w₀ v base κ hbase hupper z hregime
  have hi : 0 ≤ A⁻¹ := inv_nonneg.mpr hA.le
  have hB₀pos : 0 ≤ B₀ := zero_le_one.trans hB₀
  have hJpos : 0 ≤ descriptorJetBound (m+3) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hpow₀ : (B₀^K*A⁻¹)^2 ≤ (B^K*A⁻¹)^2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hB₀pos _) hi)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB₀pos (le_max_left _ _) _) hi) 2
  have hpowJ : ((descriptorJetBound (m+3) K)^K*A⁻¹)^2 ≤ (B^K*A⁻¹)^2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hJpos _) hi)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hJpos (le_max_right _ _) _) hi) 2
  have herr := noncomparable_stationary_error_scale
    (S := C₀) (C := (B₀^K*A⁻¹)^2)
    (M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)
    hbase hloss hexp hW hC₀ (sq_nonneg _) (by positivity)
  have hpoly : 4*W*C₀*(B₀^K*A⁻¹)^2*
      (2*(((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)+
        C₀*(B₀^K*A⁻¹)^2) ≤ C*(B^K*A⁻¹)^4 := by
    calc
      _ ≤ 4*W*C₀*(B^K*A⁻¹)^2*
          (2*((B^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)+C₀*(B^K*A⁻¹)^2) := by
        gcongr
      _ = _ := by dsimp [C]; ring
  exact hp.trans (herr.trans (mul_le_mul_of_nonneg_right hpoly (by positivity)))

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

theorem lintegral_norm_replacement {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {U : Set X} (hU : MeasurableSet U)
    (f g : X → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ x ∈ U, ‖f x-g x‖ ≤ ε) :
    (∫⁻ x in U, ENNReal.ofReal ‖f x‖ ∂μ) ≤
      (∫⁻ x in U, ENNReal.ofReal ‖g x‖ ∂μ) + ENNReal.ofReal ε * μ U := by
  calc
    _ ≤ ∫⁻ x in U, ENNReal.ofReal ‖g x‖ + ENNReal.ofReal ε ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      rw [← ENNReal.ofReal_add (norm_nonneg _) hε]
      apply ENNReal.ofReal_le_ofReal
      calc
        ‖f x‖ = ‖g x+(f x-g x)‖ := by congr 1; ring
        _ ≤ ‖g x‖+‖f x-g x‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl (herror x hx)
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,Measure.restrict_apply_univ]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarData
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
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

theorem minimumLength_pos (D : JetStateFarData m B) : 0 < farMinimumLength (m+3) D.h := by
  unfold farMinimumLength
  positivity

theorem base_one (D : JetStateFarData m B) : 1 ≤ (2:ℝ)^D.N := one_le_pow₀ (by norm_num)

theorem list_scale_mono (D : JetStateFarData m B) {C : ℝ} (hCB : C ≤ B) :
    (D.F.card:ℝ)*C*D.Dmask ≤ D.E :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCB (Nat.cast_nonneg _))
    (zero_le_one.trans D.Dmask_one)).trans D.list_scale

theorem collisionTerm_mono (D : JetStateFarData m B) (w₀ : Sphere (m+3))
    {C C' : ℝ} (hC : C ≤ C') (b : ℕ) :
    D.collisionTerm w₀ C b ≤ D.collisionTerm w₀ C' b := by
  unfold collisionTerm
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (by positivity)

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

 theorem exists_far_data_replacement
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B'), -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
        (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      z ∈ comparableFarRegion (m+3) D.a D.h →
      ‖D.kernel f g w₀ Ψ z-D.stationaryKernel f g w₀ M Ψ z‖ ≤
        C*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_original_stationary_power hgnomonic hquadratic
    m K L M hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,hB,hC,?_⟩
  intro B' hBB D horder f g w₀ z hz
  obtain ⟨hd₁,hd₂⟩ := comparableFarRegion_lower hz
  have hregime (d : ℝ) (hd : farMinimumLength (m+3) D.h ≤ d) :=
    shell_regime_of_lower_distance hs (D.t:ℝ) (2*(D.E+D.Dq)) ((2:ℝ)^D.N) D.κ
      (farMinimumLength (m+3) D.h) d D.minimumLength_pos hd
      (by simpa only [Real.rpow_natCast] using D.shell_one)
      (by simpa only [Real.rpow_natCast] using D.shell_scale)
  simpa only [JetStateFarData.kernel,JetStateFarData.stationaryKernel,Real.rpow_natCast] using
    hbound D.F D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.separated
    D.Dq D.Dmask D.E D.Z D.Dq_nonneg D.Dmask_one D.Z_pos D.scale_one D.mask_scale
    (D.list_scale_mono hBB) f g w₀ D.t ((2:ℝ)^D.N) D.κ D.loss D.base_one D.loss_nonneg horder
    D.scale_upper z (fun r hr => ⟨hregime _ hd₁ r hr,hregime _ hd₂ r hr⟩)

 theorem exists_far_data_noncomparable
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B H S : ℝ, 1 ≤ B ∧ 0 ≤ H ∧ 0 ≤ S ∧ ∀ B' : ℝ, B ≤ B' →
      ∀ (D : JetStateFarData m B'), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
        (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      z ∈ leftNoncomparableFar (m+3) D.a D.h ∪ rightNoncomparableFar (m+3) D.a D.h →
      let C₁ := (B^K*D.Z⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*D.Z⁻¹)^2
      let V := (sphereMeasure (m+3)).real univ
      ‖D.kernel f g w₀ Ψ z‖ ≤
        (H*C₁*C₂*V*(2:ℝ)^q+4*W*S*C₁*(2*(max C₁ C₂*V)+S*C₁))*((2:ℝ)^D.N)^(-D.loss) := by
  obtain ⟨B,H,S,hB,hH,hS,hbound⟩ := exists_jetState_noncomparable_original_pointwise
    hgnomonic hquadratic m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro B' hBB D hloss horder f g w₀ z hz
  have apply_bound (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq)
      (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))
      (hd : farMinimumLength (m+3) D.h ≤ dist z.1.1 z.1.2)
      (hsep : 2*dist z.2.1 z.2.2 ≤ dist z.1.1 z.1.2) :=
    hbound D.F D.F D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks
      D.separated D.separated D.Dq D.Dmask D.E D.Z D.Z D.Dq_nonneg D.Dmask_one
      D.Z_pos D.Z_pos D.scale_one D.mask_scale (D.list_scale_mono hBB) f g w₀
      D.t ((2:ℝ)^D.N) D.κ D.loss D.base_one D.loss_nonneg hloss horder D.scale_upper z
      (D.minimumLength_pos.trans_le hd) hsep
      (by simpa only [Real.rpow_natCast] using (D.large_scale.trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2:ℝ)^D.t))))
      (by simpa only [Real.rpow_natCast] using (D.large_frequency.trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2:ℝ)^D.t))))
      (shell_regime_of_lower_distance hs D.t (2*(D.E+D.Dq)) ((2:ℝ)^D.N) D.κ
        (farMinimumLength (m+3) D.h) _ D.minimumLength_pos hd
        (by simpa only [Real.rpow_natCast] using D.shell_one)
        (by simpa only [Real.rpow_natCast] using D.shell_scale))
  rcases hz with hz | hz
  · exact apply_bound f g z (leftNoncomparableFar_lower hz) hz.2.le
  · have hh := apply_bound g f (z.2,z.1) (rightNoncomparableFar_lower hz) hz.2.le
    simpa only [JetStateFarData.kernel,jetStateOriginalKernel_swap] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FarIntegralAssembly
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual far regions with a uniform replacement error -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem far_integral_assembly (d a h : ℕ)
    (μ : Measure ((Space d × Space d) × (Space d × Space d)))
    (f g : ((Space d × Space d) × (Space d × Space d)) → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnc : ∀ z ∈ leftNoncomparableFar d a h ∪ rightNoncomparableFar d a h, ‖f z‖ ≤ ε)
    (herr : ∀ z ∈ comparableFarRegion d a h, ‖f z-g z‖ ≤ ε) :
    (∫⁻ z in farDisplacementRegion d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      (∑ b ∈ Finset.Icc (a+9) (h+6),
        ∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
          ENNReal.ofReal ‖g z‖ ∂μ) +
      (2+((Finset.Icc (a+9) (h+6)).card:ℝ≥0∞))*ENNReal.ofReal ε*μ univ := by
  have hl : (∫⁻ z in leftNoncomparableFar d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_restrict_le_of_bound μ (leftNoncomparableFar_measurable d a h)
      f (fun z hz => hnc z (Or.inl hz))).trans
      (mul_le_mul' le_rfl (measure_mono (subset_univ _)))
  have hr : (∫⁻ z in rightNoncomparableFar d a h, ENNReal.ofReal ‖f z‖ ∂μ) ≤
      ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_restrict_le_of_bound μ (rightNoncomparableFar_measurable d a h)
      f (fun z hz => hnc z (Or.inr hz))).trans
      (mul_le_mul' le_rfl (measure_mono (subset_univ _)))
  have hb (b : ℕ) :
      (∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
        ENNReal.ofReal ‖f z‖ ∂μ) ≤
      (∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
        ENNReal.ofReal ‖g z‖ ∂μ) + ENNReal.ofReal ε*μ univ :=
    (lintegral_norm_replacement μ
      ((comparableFarRegion_measurable d a h).inter (comparableLengthBand_measurable d b))
      f g hε (fun z hz => herr z hz.1)).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl (measure_mono (subset_univ _))))
  apply (lintegral_far_split_bands d a h μ (fun z => ENNReal.ofReal ‖f z‖)).trans
  calc
    _ ≤ ENNReal.ofReal ε*μ univ+ENNReal.ofReal ε*μ univ+
        ∑ b ∈ Finset.Icc (a+9) (h+6),
          ((∫⁻ z in comparableFarRegion d a h ∩ comparableLengthBand d b,
            ENNReal.ofReal ‖g z‖ ∂μ)+ENNReal.ofReal ε*μ univ) :=
      add_le_add (add_le_add hl hr) (Finset.sum_le_sum (fun b _ => hb b))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarDataBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete conditional far estimate on the exact original state class -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

 theorem exists_far_data_bound_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in farDisplacementRegion (m+3) D.a D.h,
          ENNReal.ofReal ‖D.kernel f g w₀ Ψ z‖ ∂D.originalMeasure) ≤
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        ENNReal.ofReal D.prefactor *
          (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
          ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ := by
  obtain ⟨B₁,C₁,hB₁,hC₁,hstationary⟩ := exists_far_data_stationary_band m K L M (by omega) hΨ hs
  obtain ⟨B₂,C₂,hB₂,hC₂,hreplace⟩ := exists_far_data_replacement hgnomonic hquadratic
    m K L M hM hML hΨ.continuous.measurable hpos hs hW hΨW
  obtain ⟨B₃,H,S,hB₃,hH,hS,hnoncomp⟩ := exists_far_data_noncomparable hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  let B := max (max B₁ B₂) (max B₃ (descriptorJetBound (m+3) K))
  let V := (sphereMeasure (m+3)).real univ
  let Cnc := H*V*(2:ℝ)^q+4*W*S*(2*V+S)
  let Cerr := max Cnc C₂
  have hB₁B : B₁ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB₂B : B₂ ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hB₃B : B₃ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBB : descriptorJetBound (m+3) K ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hCnc : 0 ≤ Cnc := by dsimp [Cnc,V]; positivity
  have hCerr : 0 ≤ Cerr := hCnc.trans (le_max_left _ _)
  refine ⟨B,C₁,Cerr,hB₁.trans hB₁B,hC₁,hCerr,?_⟩
  intro D hloss horder f g w₀
  let ε := Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hnc : ∀ z ∈ leftNoncomparableFar (m+3) D.a D.h ∪
      rightNoncomparableFar (m+3) D.a D.h, ‖D.kernel f g w₀ Ψ z‖ ≤ ε := by
    intro z hz
    have ht := hnoncomp B hB₃B D hloss horder f g w₀ z hz
    have hc := noncomparable_coefficient_common hH hW hS
      (show 0 ≤ V from measureReal_nonneg)
      (sq_nonneg (B₃^K*D.Z⁻¹)) (sq_nonneg ((descriptorJetBound (m+3) K)^K*D.Z⁻¹))
      (sq_nonneg (B^K*D.Z⁻¹)) (show 0 ≤ (2:ℝ)^q by positivity)
      (normalized_jet_bound_mono (zero_le_one.trans hB₃) hB₃B D.Z_pos K 2)
      (normalized_jet_bound_mono (zero_le_one.trans (descriptorJetBound_one_le _ _)) hBB D.Z_pos K 2)
    have hc' := hc.trans_eq (show
        (H*V*(2:ℝ)^q+4*W*S*(2*V+S))*((B^K*D.Z⁻¹)^2)^2 =
          Cnc*(B^K*D.Z⁻¹)^4 by dsimp [Cnc]; ring)
    exact ht.trans ((mul_le_mul_of_nonneg_right hc' (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cnc C₂) (by positivity)) (by positivity)))
  have herr : ∀ z ∈ comparableFarRegion (m+3) D.a D.h,
      ‖D.kernel f g w₀ Ψ z-D.stationaryKernel f g w₀ M Ψ z‖ ≤ ε := by
    intro z hz
    apply (hreplace B hB₂B D horder f g w₀ z hz).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (le_max_right Cnc C₂)
      (normalized_jet_bound_mono (zero_le_one.trans hB₂) hB₂B D.Z_pos K 4)
      (by positivity) hCerr
  have hsband (b : ℕ) (hb : b ∈ Finset.Icc (D.a+9) (D.h+6)) :
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in comparableFarRegion (m+3) D.a D.h ∩ comparableLengthBand (m+3) b,
          ENNReal.ofReal ‖D.stationaryKernel f g w₀ M Ψ z‖ ∂D.originalMeasure) ≤
        D.collisionTerm w₀ (C₁*(B^K*D.Z⁻¹)^4) b :=
    (hstationary B hB₁B D f g w₀ b hb).trans
      (D.collisionTerm_mono w₀
        (mul_le_mul_of_nonneg_left (normalized_jet_bound_mono (zero_le_one.trans hB₁)
          hB₁B D.Z_pos K 4) hC₁) b)
  have hf := far_integral_assembly (m+3) D.a D.h D.originalMeasure
    (D.kernel f g w₀ Ψ) (D.stationaryKernel f g w₀ M Ψ) hε hnc herr
  apply (mul_le_mul' (le_refl (ENNReal.ofReal D.prefactor)) hf).trans
  rw [mul_add,Finset.mul_sum]
  apply add_le_add
  · exact Finset.sum_le_sum hsband
  · exact le_of_eq (by dsimp [ε]; ring)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_far_data_bound_oai := @OAI.Falconer.exists_far_data_bound_oai
