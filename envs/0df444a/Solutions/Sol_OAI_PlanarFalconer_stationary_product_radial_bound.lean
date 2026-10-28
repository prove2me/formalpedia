-- Prove2me | solution 1 for OAI.PlanarFalconer.stationary_product_radial_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:10:34.520908+00:00
-- url     : https://prove2.me/submissions/ca357019-8cc3-4d40-9467-687753d726c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem cost_nonneg (p : AngularDifferentialExpr) : 0 ≤ p.cost := by
  induction p with
  | term c k => exact norm_nonneg c
  | add p q hp hq => exact add_nonneg hp hq
  | comp p q hp hq => exact mul_nonneg hp hq

theorem smooth_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem apply_contDiff (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (p.apply f) := by
  induction p generalizing f with
  | term c k => exact contDiff_const.mul (smooth_iteratedDeriv hf k)
  | add p q hp hq => exact (hp hf).add (hq hf)
  | comp p q hp hq => exact hp (hq hf)

theorem iteratedDeriv_iterated (m k : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m+k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem sum_apply (ps : List AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (sum ps).apply f x = (ps.map (fun p => p.apply f x)).sum := by
  induction ps with
  | nil => simp [sum, apply]
  | cons p ps ih => simp [sum, apply, ih]

theorem sum_order_le (ps : List AngularDifferentialExpr) (n : ℕ)
    (h : ∀ p ∈ ps, p.order ≤ n) : (sum ps).order ≤ n := by
  induction ps with
  | nil => exact Nat.zero_le n
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem smooth_finite {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (WithTop.coe_le_coe.mpr (show (m:ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem derivative_bound (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+p.order, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+p.order)) := by
  induction p generalizing f C m with
  | term c k =>
    simp only [apply, cost, order, iteratedDeriv_const_mul_field, iteratedDeriv_iterated,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (hb (m+k) le_rfl) (norm_nonneg c)
  | add p q hp hq =>
    have hpord : m+p.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_left _ _) _
    have hqord : m+q.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_right _ _) _
    have hp' := hp hf hC m (fun k hk => hb k (hk.trans hpord))
    have hq' := hq hf hC m (fun k hk => hb k (hk.trans hqord))
    change ‖iteratedDeriv m (fun y => p.apply f y + q.apply f y) x‖ ≤ _
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) m x)
      (smooth_finite (q.apply_contDiff hf) m x)]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ p.cost * (C*D^(m+max p.order q.order)) +
          q.cost * (C*D^(m+max p.order q.order)) := add_le_add
        (hp'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpord) hC) p.cost_nonneg))
        (hq'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hqord) hC) q.cost_nonneg))
      _ = _ := by simp only [cost, order]; ring
  | comp p q hp hq =>
    have hCq : 0 ≤ q.cost*C*D^q.order := by
      exact mul_nonneg (mul_nonneg q.cost_nonneg hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hbq : ∀ k ≤ m+p.order,
        ‖iteratedDeriv k (q.apply f) x‖ ≤ (q.cost*C*D^q.order)*D^k := by
      intro k hk
      have h := hq hf hC k (fun l hl => hb l (by
        simp only [order]; omega))
      apply h.trans_eq
      rw [pow_add]
      ring
    have h := hp (q.apply_contDiff hf) hCq m hbq
    apply h.trans_eq
    simp only [cost, order, pow_add]
    ring

theorem derivative_bound_of_order_le (p : AngularDifferentialExpr) {n : ℕ}
    (hn : p.order ≤ n) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+n)) := by
  have hm := Nat.add_le_add_left hn m
  exact (p.derivative_bound hf hC hD m x (fun k hk => hb k (hk.trans hm))).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hm) hC) p.cost_nonneg)

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMomentBounds
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
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactStationaryAmplitude
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
    (s := Icc a b) (C := C) (by simp) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_LinearNonstationary
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_LinearRadialDecay
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularRadialKernel
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem extendedStationaryInverse_zero : extendedStationaryInverse 0 = 0 := by
  rw [extendedStationaryInverse_eq (by norm_num)]
  simp [stationarySineInverse]

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

 theorem stationaryAmplitude_jet (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (stationaryAmplitude f) 0 = stationaryJet n f := by
  have hw : ContDiff ℝ ∞ (fun u => (stationaryWeight u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff
  have hfn : ContDiffAt ℝ n (f ∘ extendedStationaryInverse) 0 :=
    ((hf.comp extendedStationaryInverse_contDiff).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hwn : ContDiffAt ℝ n (fun u => (stationaryWeight u : ℂ)) 0 :=
    (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change iteratedDeriv n (fun u => (stationaryWeight u : ℂ) *
    (f ∘ extendedStationaryInverse) u) 0 = _
  rw [iteratedDeriv_fun_mul hwn hfn]
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt
    extendedStationaryInverse_contDiff.contDiffAt
      (WithTop.coe_le_coe.mpr (show ((n-k:ℕ):ℕ∞) ≤ ⊤ from le_top))]
  simp only [extendedStationaryInverse_zero,Complex.real_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleDirectCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem fresnelCoefficient_half {Λ : ℝ} (hΛ : 0 < Λ) :
    fresnelCoefficient (Λ/2) = ((Λ^(-1/2:ℝ):ℝ):ℂ) *
      ((Real.sqrt (2*Real.pi):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  have hp : (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
    rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
    ring
  simp only [fresnelCoefficient,hp,Complex.ofReal_mul]
  ring

 theorem quadratic_coefficient_normalization (k : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (d : ℂ) :
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹*d) =
    ((Λ⁻¹:ℝ):ℂ)^k * (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^k*d := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΛ' : (Λ:ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have he : (((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹) =
      ((Λ⁻¹:ℝ):ℂ)*(-Complex.I/2) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  calc
    _ = (((k.factorial:ℝ)⁻¹:ℝ):ℂ) *
        ((((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹)^k) * d := by
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_pow,inv_pow,pow_mul]
      ring
    _ = _ := by rw [he,mul_pow]; ring

 theorem stationary_expansion_direct_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ =
      ((Λ^(-1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f 0 := by
  rw [fresnelCoefficient_half hΛ,stationaryDerivativeExpansion,mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_normalization j hΛ,stationaryAmplitude_jet (2*j) hf]
  simp only [directStationaryOperator,add_zero]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryOppositePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_iteratedDeriv_conj {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => conj (f x)) = fun x => conj (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt (x := x)
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    change HasDerivAt (fun y => conj (iteratedDeriv n f y))
      (conj (deriv (iteratedDeriv n f) x)) x at hh
    simpa only [iteratedDeriv_succ] using hh.deriv

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*directStationaryOperator j f 0) +
      conj (Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*
          directStationaryOperator j (fun θ => conj (f (θ+Real.pi))) 0)) := by
  have hfs : ContDiff ℝ ∞ (fun θ => conj (f (θ+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  unfold fullCircleStationaryExpansion
  rw [stationary_expansion_direct_operators hΛ hf,stationary_expansion_direct_operators hΛ hfs]
  simp only [mul_assoc]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem angularFiniteSum_apply {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (angularFiniteSum s p).apply f x = ∑ a ∈ s, (p a).apply f x := by
  simp [angularFiniteSum, AngularDifferentialExpr.sum_apply, List.map_map,
    Finset.sum_map_toList, Function.comp_def]

theorem angularFiniteSum_order {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (n : ℕ) (h : ∀ a ∈ s, (p a).order ≤ n) :
    (angularFiniteSum s p).order ≤ n := by
  apply AngularDifferentialExpr.sum_order_le
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact h a (Finset.mem_toList.mp ha)

theorem stationaryJetExpr_order (n : ℕ) : (stationaryJetExpr n).order ≤ n := by
  apply angularFiniteSum_order
  intro k hk
  apply angularFiniteSum_order
  intro c _
  exact stationaryJet_order hk c

theorem stationaryJetExpr_apply (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (stationaryJetExpr n).apply f x = stationaryJet n (fun u => f (u+x)) := by
  simp only [stationaryJetExpr, angularFiniteSum_apply, AngularDifferentialExpr.apply,
    stationaryJet, iteratedDeriv_comp_add_const, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

theorem directStationaryExpr_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (directStationaryExpr j).apply f x = directStationaryOperator j f x := by
  simp [directStationaryExpr, AngularDifferentialExpr.apply, stationaryJetExpr_apply,
    directStationaryOperator, stationaryLeadingConstant]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_NormalizedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem directStationaryOperator_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖directStationaryOperator j f θ‖ ≤ (directStationaryExpr j).cost*C*D^(2*j) := by
  have hh := (directStationaryExpr j).derivative_bound_of_order_le (directStationaryExpr_order j)
    hf hC hD 0 θ (by simpa only [zero_add] using hb)
  simpa only [iteratedDeriv_zero,zero_add,directStationaryExpr_apply,mul_assoc] using hh

theorem normalizedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (j : ℕ) (θ : ℝ) (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖normalizedStationaryJet j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  have hp : (D^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hΛ).mpr hscale)
  have hcost := (directStationaryExpr j).cost_nonneg
  calc
    _ = (Λ⁻¹)^j*‖directStationaryOperator j f θ‖ := by
      simp only [normalizedStationaryJet,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hΛ)]
    _ ≤ (Λ⁻¹)^j*((directStationaryExpr j).cost*C*D^(2*j)) :=
      mul_le_mul_of_nonneg_left (directStationaryOperator_bound hf hC hD j θ hb) (by positivity)
    _ = ((directStationaryExpr j).cost*C)*(D^2/Λ)^j := by
      rw [div_pow,pow_mul]
      ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg hcost hC)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RadialStationaryProfile
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

 theorem signedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (plus : Bool) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ∀ t, ‖iteratedDeriv k f t‖ ≤ C*D^k) :
    ‖signedStationaryJet plus j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  cases plus
  · simp only [signedStationaryJet,Bool.false_eq_true,↓reduceIte,Complex.norm_conj]
    have hfs : ContDiff ℝ ∞ (fun t => f (t+Real.pi)) := hf.comp (contDiff_id.add contDiff_const)
    apply normalizedStationaryJet_bound (Complex.conjCLE.contDiff.comp hfs) hC hD hΛ hscale
    intro k hk
    change ‖iteratedDeriv k (fun t => conj (f (t+Real.pi))) θ‖ ≤ _
    rw [complex_iteratedDeriv_conj hfs,Complex.norm_conj,iteratedDeriv_comp_add_const]
    exact hb k hk _
  · simp only [signedStationaryJet,↓reduceIte]
    exact normalizedStationaryJet_bound hf hC hD hΛ hscale j θ (fun k hk => hb k hk θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem signedStationaryRadial_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j k n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D A B : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < A → 0 < B →
    D^2 ≤ A → D^2 ≤ B → ∀ plus₁ plus₂ : Bool, ∀ θ φ : ℝ,
    (∀ l ≤ 2*j, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    (∀ l ≤ 2*k, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
    ContDiff ℝ ∞ (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B) ∧
    tsupport (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B) ⊆ Icc (1/4:ℝ) 4 ∧
    ∀ l ≤ n, ∀ s, ‖iteratedDeriv l (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B) s‖ ≤
      H*C*E*(A^(-1/2:ℝ)*B^(-1/2:ℝ)) := by
  obtain ⟨P,hP,hp⟩ := radialStationaryProfile_derivatives hΨ hs (-((j:ℝ)+(k:ℝ)+1)) n
  let H := P*(directStationaryExpr j).cost*(directStationaryExpr k).cost
  have hj := (directStationaryExpr j).cost_nonneg
  have hk := (directStationaryExpr k).cost_nonneg
  refine ⟨H,by dsimp [H]; positivity,?_⟩
  intro f g hf hg C E D A B hC hE hD hA hB hDA hDB plus₁ plus₂ θ φ hbf hbg
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro l hl s
  change ‖iteratedDeriv l (fun t =>
    (((A^(-1/2:ℝ)*B^(-1/2:ℝ):ℝ):ℂ) *
      (signedStationaryJet plus₁ j f θ A * signedStationaryJet plus₂ k g φ B)) *
        radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1)) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hA _),abs_of_pos (Real.rpow_pos_of_pos hB _)]
  have hfj := signedStationaryJet_bound hf hC hD hA hDA plus₁ j θ hbf
  have hgk := signedStationaryJet_bound hg hE hD hB hDB plus₂ k φ hbg
  calc
    _ ≤ (A^(-1/2:ℝ)*B^(-1/2:ℝ))*
        (((directStationaryExpr j).cost*C)*((directStationaryExpr k).cost*E))*P := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul hfj hgk (norm_nonneg _) (mul_nonneg hj hC))
          (by positivity)) (hp l hl s) (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [H]; ring

 theorem signedStationaryRadial_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j k : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
    D^2 ≤ R*d₁ → D^2 ≤ R*d₂ → ∀ plus₁ plus₂ : Bool, ∀ θ φ s₁ s₂ : ℝ,
    (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
    (∀ l ≤ 2*j, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    (∀ l ≤ 2*k, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
    ‖radialPhaseIntegral (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ (R*d₁) (R*d₂))
      (R*(s₁*d₁+s₂*d₂))‖ ≤
      H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
  obtain ⟨H,hH,hh⟩ := signedStationaryRadial_derivatives hΨ hs j k 2
  refine ⟨15*H,by positivity,?_⟩
  intro f g hf hg C E D R d₁ d₂ hC hE hD hR h1 h2 hDA hDB plus₁ plus₂ θ φ s₁ s₂ hs1 hs2 hbf hbg
  obtain ⟨ha,hsa,hba⟩ := hh hf hg hC hE hD (mul_pos hR h1) (mul_pos hR h2)
    hDA hDB plus₁ plus₂ θ φ hbf hbg
  have hb0 := hba 0 (by omega)
  simp only [iteratedDeriv_zero] at hb0
  have hx := angular_radial_kernel_bound ha hsa (C := H*C*E)
    (by positivity) (by positivity) hR.le h1.le h2.le hs1 hs2 hb0 (hba 2 le_rfl)
  apply hx.trans_eq
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryRadialScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationary_radial_power (j k : ℕ) {s : ℝ} (hs : 0 < s) :
    (s^(-1/2:ℝ)*s^(-1/2:ℝ)) * ((s⁻¹)^j*(s⁻¹)^k) = s^(-((j:ℝ)+(k:ℝ)+1)) := by
  rw [← Real.rpow_add hs]
  have hj : (s⁻¹)^j = s^(-(j:ℝ)) := by rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  have hk : (s⁻¹)^k = s^(-(k:ℝ)) := by rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  rw [hj,hk,← Real.rpow_add hs,← Real.rpow_add hs]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_signed {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm true j f Λ) +
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm false j f Λ) := by
  rw [fullCircleStationaryExpansion_operators hΛ hf]
  simp only [signedStationaryTerm,stationarySign,signedStationaryJet,normalizedStationaryJet,
    ↓reduceIte,Bool.false_eq_true,one_mul,neg_one_mul,
    map_mul,map_sum,map_pow,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_neg,Finset.mul_sum,mul_assoc]
  simp [neg_mul,mul_neg]

 theorem signedStationaryJet_scale (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ A s : ℝ) :
    signedStationaryJet plus j f θ (A*s) = ((s⁻¹:ℝ):ℂ)^j * signedStationaryJet plus j f θ A := by
  cases plus <;> simp only [signedStationaryJet,normalizedStationaryJet,↓reduceIte,
    Bool.false_eq_true,mul_inv_rev,Complex.ofReal_mul,mul_pow,map_mul,map_pow,Complex.conj_ofReal]
  all_goals ring

 theorem signedStationaryRadialCoefficient_eq (Ψ : ℝ → ℝ) (plus₁ plus₂ : Bool)
    (j k : ℕ) (f g : ℝ → ℂ) (θ φ : ℝ) {A B s : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) :
    signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B s =
      (Ψ s : ℂ) * (((A*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus₁ j f θ (A*s) *
        (((B*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus₂ k g φ (B*s) := by
  have hp := congrArg (fun t : ℝ => (t:ℂ)) (stationary_radial_power j k hs)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv] at hp
  simp only [signedStationaryRadialCoefficient,radialStationaryProfile,
    signedStationaryJet_scale,Real.mul_rpow hA.le hs.le,Real.mul_rpow hB.le hs.le,
    Complex.ofReal_mul,Complex.ofReal_inv]
  rw [← hp]
  ring

 theorem signedStationaryTerm_product (Ψ : ℝ → ℝ) (plus₁ plus₂ : Bool)
    (j k : ℕ) (f g : ℝ → ℂ) {R d₁ d₂ s : ℝ}
    (hR : 0 < R) (h1 : 0 < d₁) (h2 : 0 < d₂) (hs : 0 < s) :
    (Ψ s : ℂ) * signedStationaryTerm plus₁ j f (R*d₁*s) *
      signedStationaryTerm plus₂ k g (R*d₂*s) =
      Complex.exp (Complex.I*((R*(stationarySign plus₁*d₁+stationarySign plus₂*d₂):ℝ):ℂ)*(s:ℂ)) *
        signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g 0 0 (R*d₁) (R*d₂) s := by
  rw [signedStationaryRadialCoefficient_eq Ψ plus₁ plus₂ j k f g 0 0
    (mul_pos hR h1) (mul_pos hR h2) hs]
  have he : Complex.exp (Complex.I*((stationarySign plus₁*(R*d₁*s):ℝ):ℂ)) *
      Complex.exp (Complex.I*((stationarySign plus₂*(R*d₂*s):ℝ):ℂ)) =
      Complex.exp (Complex.I*((R*(stationarySign plus₁*d₁+stationarySign plus₂*d₂):ℝ):ℂ)*(s:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold signedStationaryTerm
  rw [← he]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem fullCircleStationaryExpansion_sum {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      ∑ p ∈ stationarySignedIndices n, signedStationaryTerm p.1 p.2 f Λ := by
  rw [fullCircleStationaryExpansion_signed hΛ hf]
  simp [stationarySignedIndices,Finset.sum_product,add_comm]

theorem signedStationaryRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (plus₁ plus₂ : Bool) (j k : ℕ) (f g : ℝ → ℂ) (θ φ A B ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ))*
      signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B s) := by
  have hc : HasCompactSupport (radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (signedStationaryRadialCoefficient Ψ plus₁ plus₂ j k f g θ φ A B) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  exact (((by fun_prop : Continuous (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ)))).mul hcont)).integrable_of_hasCompactSupport hc.mul_left.mul_left

theorem stationary_product_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) {R d₁ d₂ : ℝ} (hR : 0 < R) (h1 : 0 < d₁) (h2 : 0 < d₂) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
      (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n)) =
      ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n,
        radialPhaseIntegral (signedStationaryRadialCoefficient Ψ p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂))
          (R*(stationarySign p.1*d₁+stationarySign q.1*d₂)) := by
  let H := fun (p q : Bool × ℕ) (s : ℝ) => Complex.exp
    (Complex.I*((R*(stationarySign p.1*d₁+stationarySign q.1*d₂):ℝ):ℂ)*(s:ℂ))*
      signedStationaryRadialCoefficient Ψ p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂) s
  have he (s : ℝ) : Ψ s •
      (fullCircleStationaryExpansion (R*s*d₁) f n * fullCircleStationaryExpansion (R*s*d₂) g n) =
      ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p q s := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,signedStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity),
        fullCircleStationaryExpansion_sum hg (by positivity)]
      simp only [Complex.real_smul,Finset.mul_sum,Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simpa only [H,mul_assoc,mul_right_comm R s] using
        signedStationaryTerm_product Ψ p.1 q.1 p.2 q.2 f g hR h1 h2 hsp
  have hi (p q : Bool × ℕ) : Integrable (H p q) :=
    signedStationaryRadial_integrable hΨ hs p.1 q.1 p.2 q.2 f g 0 0 (R*d₁) (R*d₂) _
  calc
    _ = ∫ s : ℝ, Ψ s •
        (fullCircleStationaryExpansion (R*s*d₁) f n * fullCircleStationaryExpansion (R*s*d₂) g n) := by
      have hh := Measure.integral_comp_mul_left
        (fun r : ℝ => Ψ (r/R) •
          (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n)) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p q s := by
      simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_finsetSum _ (fun q _ => hi p q)]
      rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryProductKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem stationary_product_radial_bound_oai {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
    D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
      (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n))‖ ≤
      H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
  choose H hH hb using fun j k => signedStationaryRadial_kernel hΨ hs j k
  let Htot := ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p.2 q.2
  refine ⟨Htot,Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => hH p.2 q.2)),?_⟩
  intro f g hf hg C E D R d₁ d₂ hC hE hD hR h1 h2 hDA hDB hbf hbg
  rw [stationary_product_radial_integral hΨ hs hf hg n hR h1 h2]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n,
        H p.2 q.2*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      have hj : p.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      have hk : q.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hq).2)
      exact hb p.2 q.2 hf hg hC hE hD hR h1 h2 hDA hDB p.1 q.1 0 0
        (stationarySign p.1) (stationarySign q.1)
        (by cases p.1 <;> simp [stationarySign]) (by cases q.1 <;> simp [stationarySign])
        (fun l hl => hbf l (hl.trans (Nat.mul_le_mul_left 2 hj)))
        (fun l hl => hbg l (hl.trans (Nat.mul_le_mul_left 2 hk)))
    _ = _ := by simp only [Htot,Finset.sum_mul,Finset.sum_div]

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.stationary_product_radial_bound_oai := @OAI.PlanarFalconer.stationary_product_radial_bound_oai
