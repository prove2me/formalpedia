-- Prove2me | solution 1 for MasulloRH.finite_prime_shell_mellin_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:44:34.795462+00:00
-- url     : https://prove2.me/submissions/d724d281-d680-416a-af2e-7dbd94052469

import Theorems.Thm_MasulloRH_corrected_prime_shell_mellin_limits
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

namespace MasulloRH

theorem exists_bound_iteratedDerivWithin_two {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, a < b → ∀ x : ℝ,
      |iteratedDerivWithin 2 ψ (Set.uIcc a b) x| ≤ M := by
  have hd : HasCompactSupport (iteratedDeriv 2 ψ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc.deriv.deriv
  obtain ⟨M, hM⟩ := (ContDiff.continuous_iteratedDeriv' 2 hψ).bounded_above_of_compact_support hd
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM₀, fun a b hab x ↦ ?_⟩
  rw [Set.uIcc_of_le hab.le]
  by_cases hx : x ∈ Set.Icc a b
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hψ.contDiffAt hx]
    exact hM x
  · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
      (by rwa [closure_Icc]), abs_zero]
    exact hM₀

end MasulloRH

open MeasureTheory Set Filter
open scoped Topology

noncomputable def sieveLattice (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)

private theorem sieve_trap_bound (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (R : ℝ) (hR : 0<R)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0) (hmean : (∫ x : ℝ, ψ x) = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ b : ℝ, 0 < b → ∀ x : ℝ, |iteratedDerivWithin 2 ψ (uIcc 0 b) x| ≤ M)
    (t : ℝ) (ht : 0<t) : |sieveLattice ψ t| ≤ M*(R+t)*t/12 := by
  let N : ℕ := ⌈R/t⌉₊
  have hN : 0<N := Nat.ceil_pos.mpr (div_pos hR ht)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hn0 := hn.ne'
  have hNt : R ≤ (N:ℝ)*t := (div_le_iff₀ ht).mp (Nat.le_ceil _)
  have hNt' : (N:ℝ)*t < R+t := by
    have hc : (N:ℝ) < R/t+1 := Nat.ceil_lt_add_one (div_nonneg hR.le ht.le)
    calc
      _ < (R/t+1)*t := (mul_lt_mul_of_pos_right hc ht)
      _ = _ := by field_simp
  have hb : 0 < (N:ℝ)*t := mul_pos hn ht
  have hsum : sieveLattice ψ t = ∑ k ∈ Finset.range (N-1), ψ (((k:ℝ)+1)*t) := by
    apply tsum_eq_sum
    intro n hn'
    apply hvan
    right
    apply hNt.trans
    apply mul_le_mul_of_nonneg_right _ ht.le
    have : N ≤ n+1 := by have := mt Finset.mem_range.mpr hn'; omega
    exact_mod_cast this
  have hint : (∫ x in (0:ℝ)..((N:ℝ)*t), ψ x) = 0 := by
    rw [intervalIntegral.integral_of_le hb.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hmean
    · intro x hx
      apply hvan
      by_cases hp : 0<x
      · right
        exact hNt.trans (by by_contra! h'; exact hx ⟨hp,h'.le⟩)
      · exact Or.inl (le_of_not_gt hp)
  have htr : trapezoidal_integral ψ N 0 ((N:ℝ)*t) = t*sieveLattice ψ t := by
    unfold trapezoidal_integral
    rw [hvan 0 (Or.inl le_rfl),hvan _ (Or.inr hNt),hsum]
    simp only [sub_zero, add_zero, zero_div, zero_add]
    have hratio : (N:ℝ)*t/N=t := by field_simp
    rw [hratio]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    field_simp
  have he := trapezoidal_error_le_of_c2 (a:=0) (b:=(N:ℝ)*t)
    hψ.contDiffOn (hder _ hb) hN
  rw [trapezoidal_error,htr,hint,sub_zero,abs_mul,abs_of_pos ht,sub_zero,abs_of_pos hb] at he
  have hr : ((N:ℝ)*t)^3*M/(12*(N:ℝ)^2) = ((N:ℝ)*t)*M*t^2/12 := by field_simp
  rw [hr] at he
  have htdiv : t*|sieveLattice ψ t| ≤ t*(M*(R+t)*t/12) := by
    apply he.trans
    have hcmp := mul_le_mul_of_nonneg_right hNt'.le (mul_nonneg hM (sq_nonneg t))
    linarith only [show ((N:ℝ)*t)*M*t^2 ≤ M*(R+t)*t*t by linarith only [hcmp]]
  exact le_of_mul_le_mul_left htdiv ht

private lemma sieve_measurable (ψ : ℝ → ℝ) (hψ : Continuous ψ) : Measurable (sieveLattice ψ) := by
  apply Measurable.tsum
  intro n
  exact (hψ.comp (continuous_const.mul continuous_id)).measurable

private lemma sieve_vanishes (ψ : ℝ → ℝ) (R : ℝ) (hR : 0<R)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0) (t : ℝ) (ht : R≤t) :
    sieveLattice ψ t = 0 := by
  unfold sieveLattice
  convert tsum_zero (α:=ℝ) (β:=ℕ) using 1
  congr
  funext n
  apply hvan _ ∘ Or.inr
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn ((hR.le.trans ht))]

private lemma sieve_log_of_bound (F : ℝ → ℝ) (hm : Measurable F) (R C : ℝ)
    (hbound : ∀ t, 0<t → t≤R → |F t| ≤ C*t) (hzero : ∀ t, R≤t → F t=0) :
    IntegrableOn (fun t : ℝ => F t/t) (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => F t/t) := hm.div measurable_id
  have hnear : IntegrableOn (fun t : ℝ => F t/t) (Ioc 0 R) := by
    apply (integrableOn_const (μ:=volume) (s:=Ioc 0 R) (C:=C) (by simp [Real.volume_Ioc])).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs,abs_div,abs_of_pos ht.1]
    exact (div_le_iff₀ ht.1).mpr (hbound t ht.1 ht.2)
  have hfar : IntegrableOn (fun t : ℝ => F t/t) (Ioi R) := by
    have he : EqOn (fun t : ℝ => F t/t) (fun _ => 0) (Ioi R) := by
      intro t ht; simp [hzero t (le_of_lt ht)]
    exact (integrableOn_congr_fun he measurableSet_Ioi).mpr (by simp)
  apply (hnear.union hfar).mono_set
  intro t ht
  by_cases h : t≤R
  · exact Or.inl ⟨ht,h⟩
  · exact Or.inr (lt_of_not_ge h)

open Complex Set MeasureTheory

theorem sieve_mellin_of_bound (F : ℝ → ℝ) (hm : Measurable F) (R C : ℝ) (hR : 0<R)
    (hC : 0≤C) (hsmall : ∀ t, 0<t → t≤R → |F t|≤C*t)
    (hzero : ∀ t, R≤t → F t=0) (s : ℂ) (hs : 0≤s.re) :
    MellinConvergent (fun t => (F t:ℂ)) s := by
  let M := C * R^s.re
  have hM : 0 ≤ M := mul_nonneg hC (Real.rpow_nonneg hR.le _)
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ => M)) := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const (ne_of_lt measure_Ioo_lt_top)
  change IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1) * (F t:ℂ)) (Ioi 0)
  apply hi.integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (0:ℝ)) measurableSet_Ioi] with t ht
  have ht0 : 0<t := ht
  by_cases h : t<R
  · rw [Set.indicator_of_mem (show t∈Ioo 0 R from ⟨ht0,h⟩)]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,Complex.norm_real,Real.norm_eq_abs,sub_re,one_re]
    have hpow : t^(s.re-1) * t = t^s.re := by
      conv_lhs => rhs; rw [← Real.rpow_one t]
      rw [←Real.rpow_add ht0]; congr 1; ring
    calc t^(s.re-1) * |F t| ≤ t^(s.re-1)*(C*t) :=
          mul_le_mul_of_nonneg_left (hsmall t ht0 h.le) (Real.rpow_nonneg ht0.le _)
         _ = C*t^s.re := by rw [← hpow]; ring
         _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le h.le hs) hC
  · rw [Set.indicator_of_notMem (fun he : t ∈ Ioo 0 R => h he.2), hzero t (le_of_not_gt h)]
    simp

open Filter Set MeasureTheory Asymptotics
open scoped Topology

theorem MasulloRH.smooth_lattice_sum_mellin_convergence
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hcomp : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0) :
    (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) =O[𝓝[>] 0] (fun t : ℝ => t) ∧
    IntegrableOn (fun t : ℝ => (∑' n : ℕ, ψ (((n:ℝ)+1)*t)) / t) (Ioi 0) ∧
    ∀ s : ℂ, 0 ≤ s.re →
      MellinConvergent (fun t : ℝ => ((∑' n : ℕ, ψ (((n:ℝ)+1)*t)) : ℂ)) s := by
  obtain ⟨M,hM,hd⟩ := MasulloRH.exists_bound_iteratedDerivWithin_two hψ hcomp
  let C := M*(R+R)/12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmean' : (∫ x : ℝ, ψ x) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ)) (f:=ψ)]
    · exact hmean
    · intro x hx; exact hvan x (Or.inl (le_of_not_gt hx))
  have hzero := sieve_vanishes ψ R hR hvan
  have hsmall (t : ℝ) (ht : 0<t) (hr : t≤R) : |sieveLattice ψ t| ≤ C*t := by
    apply (sieve_trap_bound ψ hψ R hR hvan hmean' M hM (hd 0) t ht).trans
    have hmul := mul_nonneg (mul_nonneg hM (sub_nonneg.mpr hr)) ht.le
    dsimp [C]
    nlinarith only [hmul]
  refine ⟨IsBigO.of_bound C ?_, sieve_log_of_bound _ (sieve_measurable ψ hψ.continuous) R C hsmall hzero, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0<t := ht
    change |sieveLattice ψ t| ≤ C*|t|
    rw [abs_of_pos ht']
    by_cases h : t ≤ R
    · exact hsmall t ht' h
    · rw [hzero t (le_of_not_ge h), abs_zero]; positivity
  · simpa only [sieveLattice, Complex.ofReal_tsum] using
      sieve_mellin_of_bound _ (sieve_measurable ψ hψ.continuous) R C hR hC hsmall hzero

open Complex MeasureTheory Set ENNReal
open scoped ENNReal

private lemma muntz_weighted_dilation_norm (ψ : ℝ → ℂ) (s : ℂ) (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, ‖(t:ℂ)^(s-1) * ψ (b*t)‖) =
      b^(-s.re) * ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^(s-1) * ψ t‖ := by
  let g (t : ℝ) := ‖(t:ℂ)^(s-1) * ψ t‖
  calc
    _ = ∫ t : ℝ in Ioi 0, b^(1-s.re) * g (b*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only [g]
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hb ht0), sub_re, one_re,
        Real.mul_rpow hb.le ht0.le]
      have he : b^(1-s.re)*b^(s.re-1)=1 := by
        rw [← Real.rpow_add hb]; ring_nf; exact Real.rpow_zero b
      calc _ = (b^(1-s.re)*b^(s.re-1))*(t^(s.re-1)*‖ψ (b*t)‖) := by rw [he,one_mul]
           _ = _ := by ring
    _ = b^(1-s.re) * (b⁻¹ * ∫ t : ℝ in Ioi 0, g t) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hb,mul_zero,smul_eq_mul]
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_neg_one b, ← Real.rpow_add hb]
      congr 2; ring

private lemma muntz_tsum_integrable_of_summable_norm_integrals {F : ℕ → ℝ → ℂ}
    {ν : Measure ℝ} (hF : ∀ j, Integrable (F j) ν) (h : Summable (fun j => ∫ t, ‖F j t‖ ∂ν)) :
    Integrable (fun t => ∑' j, F j t) ν := by
  refine ⟨AEStronglyMeasurable.tsum (fun j => (hF j).aestronglyMeasurable),?_⟩
  have hlam (j : ℕ) : ∫⁻ t, ‖F j t‖ₑ ∂ν = ‖∫ t, ‖F j t‖ ∂ν‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF j).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F j t)))]
    simp only [coe_nnnorm]
  have hfin : (∑' j, ∫⁻ t, ‖F j t‖ₑ ∂ν) ≠ ⊤ := by
    rw [funext hlam]; exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 h.abs)
  change (∫⁻ t, ‖∑' j, F j t‖ₑ ∂ν) < ⊤
  calc _ ≤ ∫⁻ t, ∑' j, ‖F j t‖ₑ ∂ν := lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
       _ = ∑' j, ∫⁻ t, ‖F j t‖ₑ ∂ν := lintegral_tsum fun j => (hF j).aestronglyMeasurable.enorm
       _ < ⊤ := hfin.lt_top

/-- Mellin transform of the sum over all positive integer dilations on its half-plane
of absolute convergence. The first component supplies integrability of the full sum. -/
theorem MasulloAudit.hasMellin_nat_dilation_sum (f : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (hf : MellinConvergent f s) :
    HasMellin (fun t : ℝ => ∑' j : ℕ, f (((j:ℝ)+1)*t)) s (riemannZeta s * mellin f s) := by
  let D (j : ℕ) : ℝ := j+1
  have hD (j : ℕ) : 0 < D j := by dsimp [D]; positivity
  let F (j : ℕ) (t : ℝ) := (t:ℂ)^(s-1) * f (D j*t)
  let ν := volume.restrict (Ioi (0:ℝ))
  have hF (j : ℕ) : Integrable (F j) ν := (MellinConvergent.comp_mul_left (hD j)).mpr hf
  have hsD : Summable (fun j : ℕ => (D j)^(-s.re)) := by
    have hp := (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [D, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have hN : Summable (fun j => ∫ t, ‖F j t‖ ∂ν) := by
    let L := ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^(s-1) * f t‖
    have hi (j : ℕ) : (∫ t, ‖F j t‖ ∂ν) = (D j)^(-s.re)*L :=
      muntz_weighted_dilation_norm f s (D j) (hD j)
    simp_rw [hi]
    exact hsD.mul_right L
  have hpoint (t : ℝ) : (t:ℂ)^(s-1) * (∑' j : ℕ, f (D j*t)) = ∑' j : ℕ, F j t :=
    tsum_mul_left.symm
  constructor
  · change Integrable (fun t : ℝ => (t:ℂ)^(s-1) * (∑' j : ℕ, f (D j*t))) ν
    simp_rw [hpoint]
    exact muntz_tsum_integrable_of_summable_norm_integrals hF hN
  · change (∫ t : ℝ, (t:ℂ)^(s-1) * (∑' j : ℕ, f (D j*t)) ∂ν) = _
    simp_rw [hpoint]
    rw [← integral_tsum_of_summable_integral_norm hF hN]
    have hline (j : ℕ) : (∫ t, F j t ∂ν) = (1 / ((j:ℂ)+1)^s) * mellin f s := by
      have hpow : ((D j:ℝ):ℂ)^(-s) = 1 / ((j:ℂ)+1)^s := by
        simp [D,Complex.cpow_neg]
      simpa only [mellin,smul_eq_mul,hpow] using mellin_comp_mul_left f s (hD j)
    simp_rw [hline]
    rw [tsum_mul_right, ← zeta_eq_tsum_one_div_nat_add_one_cpow hs]

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

private theorem muntz_continue (A B : ℂ → ℂ)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.re})
    (hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.re})
    (hr : ∀ z : ℂ, 1 < z.re → A z = riemannZeta z * B z)
    (s : ℂ) (h0 : 0<s.re) (h1 : s.re<1) :
    A s = riemannZeta s * B s := by
  let j : ℝ := if 0 ≤ s.im then 1 else -1
  have hj : j*j=1 := by dsimp [j]; split_ifs <;> norm_num
  have hjs : 0 ≤ j*s.im := by dsimp [j]; split_ifs <;> simp_all; linarith
  let L : ℂ →L[ℝ] ℝ := reCLM - j • imCLM
  have hL (z : ℂ) : L z = z.re - j*z.im := by rfl
  let U : Set ℂ := {z | 0<z.re} ∩ {z | L z < 1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt L.continuous continuous_const)
  have hconv : Convex ℝ U :=
    (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0).inter (convex_halfSpace_lt L.toLinearMap.isLinear 1)
  have hne (z : ℂ) (hz : z ∈ U) : z ≠ 1 := by
    rintro rfl
    have h := hz.2
    change L 1 < 1 at h
    simp [hL] at h
  have hA' : AnalyticOnNhd ℂ A U := (hA.mono fun _ h => h.1).analyticOnNhd hU
  have hB' : AnalyticOnNhd ℂ (fun z => riemannZeta z*B z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_riemannZeta (hne z hz)).differentiableWithinAt.mul ((hB z hz.1).mono fun _ h => h.1)
  let p : ℂ := ⟨2,2*j⟩
  have hp : p ∈ U := by
    refine ⟨by norm_num [p],?_⟩
    change L p < 1
    rw [hL]
    change (2:ℝ)-j*(2*j)<1
    nlinarith
  have he : A =ᶠ[𝓝 p] (fun z => riemannZeta z*B z) := by
    have hp' : p ∈ {z : ℂ | 1<z.re} := by norm_num [p]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp'] with z hz
    exact hr z hz
  apply hA'.eqOn_of_preconnected_of_eventuallyEq hB' hconv.isPreconnected hp he
  refine ⟨h0,?_⟩
  change L s < 1
  rw [hL]
  linarith

private lemma muntz_holomorphic (f : ℝ → ℂ)
    (hI : IntegrableOn f (Ioi 0)) (htop : ∀ᶠ t : ℝ in atTop, f t=0)
    (hbot : f =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ))) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent f s) ∧
      DifferentiableOn ℂ (mellin f) {s : ℂ | 0 < s.re} := by
  have hdec (a : ℝ) : f =O[atTop] (fun t : ℝ => t^(-a)) :=
    (isBigO_zero _ _).congr' (htop.mono fun _ h => h.symm) Filter.EventuallyEq.rfl
  have hbd : f =O[𝓝[>] 0] (fun t : ℝ => t^(-(0:ℝ))) := by simpa using hbot
  constructor
  · intro s hs
    exact mellinConvergent_of_isBigO_rpow hI.locallyIntegrableOn (hdec (s.re+1))
      (by linarith) hbd hs
  · intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hI.locallyIntegrableOn (hdec (s.re+1))
      (by linarith) hbd hs).differentiableWithinAt

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

private lemma smooth_test_mellin_data (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (R : ℝ) (hcut : ∀ t : ℝ, R≤t → ψ t=0) :
    (∀ s : ℂ, 0<s.re → MellinConvergent (fun t=> (ψ t:ℂ)) s) ∧
    DifferentiableOn ℂ (mellin (fun t=> (ψ t:ℂ))) {z : ℂ | 0<z.re} := by
  apply muntz_holomorphic
  · exact (hψ.continuous.integrable_of_hasCompactSupport hc).ofReal.integrableOn
  · filter_upwards [eventually_ge_atTop R] with t ht
    simp [hcut t ht]
  · have hlim : Tendsto (fun t : ℝ => (ψ t:ℂ)) (𝓝[>] 0) (𝓝 (ψ 0:ℂ)) :=
      (Complex.continuous_ofReal.comp hψ.continuous).continuousAt.continuousWithinAt
    exact hlim.isBigO_one ℝ

theorem MasulloRH.smooth_compact_mellinConvergent (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (R : ℝ) (hcut : ∀ t : ℝ, R≤t → ψ t=0)
    (s : ℂ) (h0 : 0 < s.re) : MellinConvergent (fun t=> (ψ t:ℂ)) s :=
  (smooth_test_mellin_data ψ hψ hc R hcut).1 s h0

theorem MasulloRH.muntz_smooth_positive_lattice
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (fun t : ℝ => ∑' n : ℕ, (ψ (((n:ℝ)+1)*t):ℂ)) s
      (riemannZeta s * mellin (fun t : ℝ => (ψ t:ℂ)) s) := by
  let f (t : ℝ) : ℂ := ψ t
  let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t):ℂ)
  have hFeq (t : ℝ) : F t = (sieveLattice ψ t : ℂ) := (Complex.ofReal_tsum _).symm
  have htrap := MasulloRH.smooth_lattice_sum_mellin_convergence ψ hψ hc R hR hvan hmean
  have hI : IntegrableOn F (Ioi 0) := by
    have hz := htrap.2.2 1 (by norm_num)
    simpa only [MellinConvergent, sub_self, cpow_zero, one_smul,F] using hz
  have hFtop : ∀ᶠ t : ℝ in atTop, F t=0 := by
    filter_upwards [eventually_ge_atTop R] with t ht
    rw [hFeq, sieve_vanishes ψ R hR hvan t ht]
    simp
  have hFbot : F =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) := by
    have hreal := htrap.1.trans ((continuous_id.continuousAt.continuousWithinAt
      (x:=(0:ℝ)) (s:=Ioi 0)).tendsto.isBigO_one ℝ)
    have hcast : (fun t : ℝ => (sieveLattice ψ t : ℂ)) =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) :=
      Complex.isBigO_ofReal_left.mpr hreal
    exact hcast.congr' (.of_forall (fun t => (hFeq t).symm)) Filter.EventuallyEq.rfl
  obtain ⟨hFconv,hFA⟩ := muntz_holomorphic F hI hFtop hFbot
  have hdata := smooth_test_mellin_data ψ hψ hc R (fun t ht => hvan t (Or.inr ht))
  have hright (z : ℂ) (hz : 1<z.re) : mellin F z = riemannZeta z*mellin f z :=
    (MasulloAudit.hasMellin_nat_dilation_sum f z hz (hdata.1 z (by linarith))).2
  exact ⟨hFconv s h0,muntz_continue (mellin F) (mellin f) hFA hdata.2 hright s h0 h1⟩

open Finset

theorem MasulloRH.finite_shell_calibration_aux {p B : ℕ} (hp : p.Prime) (hB : p ≤ B)
    {a : ℝ} (ha : 0 < a) {Z U S : ℂ} (hZ : Z ≠ 0)
    (hfin : S = (((∏ l ∈ (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p),
      (1 - (l:ℝ)^(-a)) : ℝ) : ℂ) * (((p:ℝ)^(-a) : ℝ) : ℂ) * (Z * U))) :
    let W : ℂ := Z * (((∏ l ∈ (range (B+1)).filter Nat.Prime,
      (1 - (l:ℝ)^(-a)) : ℝ) : ℂ))
    W ≠ 0 ∧ S / W = U / (((p:ℝ)^a-1 : ℝ) : ℂ) := by
  intro W
  let P := (range (B+1)).filter Nat.Prime
  let Q := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
  have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
  have hQ : P.erase p = Q := by
    ext l
    simp only [P,Q,mem_erase,mem_filter]
    tauto
  have hprod : (∏ l ∈ P, (1-(l:ℝ)^(-a))) =
      (1-(p:ℝ)^(-a)) * ∏ l ∈ Q, (1-(l:ℝ)^(-a)) := by
    rw [← hQ]
    exact (Finset.mul_prod_erase P (fun l : ℕ => (1-(l:ℝ)^(-a))) hpP).symm
  have hFac (l : ℕ) (hl : l.Prime) : 0 < 1-(l:ℝ)^(-a) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hl.one_lt) (neg_neg_of_pos ha))
  have hqPos : 0 < ∏ l ∈ Q, (1-(l:ℝ)^(-a)) :=
    Finset.prod_pos fun l hl => hFac l (mem_filter.mp hl).2.1
  have hq0 : (((∏ l ∈ Q, (1-(l:ℝ)^(-a)) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hqPos.ne'
  have hp1 : 1 < (p:ℝ)^a := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) ha
  have hP0 : 0 < ∏ l ∈ P, (1-(l:ℝ)^(-a)) := Finset.prod_pos fun l hl => hFac l (mem_filter.mp hl).2
  have hW : W ≠ 0 := mul_ne_zero hZ (by exact_mod_cast hP0.ne')
  refine ⟨hW, ?_⟩
  apply (div_eq_div_iff hW (by exact_mod_cast (sub_ne_zero.mpr hp1.ne'))).mpr
  change S * _ = U * (Z * ((∏ l ∈ P, (1-(l:ℝ)^(-a)) : ℝ) : ℂ))
  rw [hprod,hfin]
  change (((∏ l ∈ Q, (1-(l:ℝ)^(-a)) : ℝ) : ℂ) * _ * _) * _ = _
  push_cast
  rw [Real.rpow_neg (by positivity : 0 ≤ (p:ℝ))]
  push_cast
  have hp0 : (((p:ℝ)^a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (p:ℝ)^a ≠ 0)
  field_simp

open Finset Set MeasureTheory

theorem MasulloRH.normalize_sieve_from_muntz (p B : ℕ) (hp : p.Prime) (hB : p ≤ B)
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ (a:ℂ))
    (hsum : ∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ψ (((n:ℝ)+1)*t)))
    (hF : MellinConvergent (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) (a:ℂ))
    (hM : mellin (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) (a:ℂ) =
         riemannZeta (a:ℂ) * mellin ψ (a:ℂ)) :
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
    let G (t : ℝ) := ∑ U ∈ Q.powerset,
      (-1:ℂ)^U.card * F (((p:ℝ)*∏ l ∈ U, (l:ℝ))*t)
    let W : ℂ := riemannZeta (a:ℂ) * (((∏ l ∈ (range (B+1)).filter Nat.Prime,
      (1-(l:ℝ)^(-a)) : ℝ):ℂ))
    W ≠ 0 ∧ mellin G (a:ℂ) / W = mellin ψ (a:ℂ) / (((p:ℝ)^a-1 : ℝ):ℂ) := by
  intro F Q G W
  have hv := (MasulloRH.corrected_prime_shell_mellin_limits p hp a ha ha₁.le ψ hψ ⟨hsum,hF⟩).1 B
  have hval := hv.2
  change mellin G (a:ℂ) = _ at hval
  change mellin F (a:ℂ) = _ at hM
  change mellin G (a:ℂ) = _ * (_ * mellin F (a:ℂ)) at hval
  rw [hM] at hval
  have hz : riemannZeta (a:ℂ) ≠ 0 := by
    apply zeta_ne_zero_of_mem_strip_of_abs_im_le_two
    · simpa using ha
    · simpa using ha₁
    · simp
  exact MasulloRH.finite_shell_calibration_aux hp hB ha hz (by simpa only [mul_assoc] using hval)

open Finset Set Filter MeasureTheory Asymptotics
open scoped Topology

theorem solution
    (p B : ℕ) (hp : p.Prime) (hpB : p ≤ B) (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, x ≤ r ∨ R ≤ x → u x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), u x) = 0) :
    let ψ : ℝ → ℂ := fun t => (u t : ℂ)
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
    let G (t : ℝ) := ∑ U ∈ Q.powerset,
      (-1:ℂ)^U.card * F (((p:ℝ)*∏ l ∈ U, (l:ℝ))*t)
    let W : ℂ := riemannZeta (a:ℂ) * (((∏ l ∈ (range (B+1)).filter Nat.Prime,
      (1-(l:ℝ)^(-a)) : ℝ):ℂ))
    W ≠ 0 ∧ mellin G (a:ℂ) / W = mellin ψ (a:ℂ) / (((p:ℝ)^a-1 : ℝ):ℂ) := by
  intro ψ F Q G W
  have hu₀ (x : ℝ) (h : x≤0 ∨ R≤x) : u x = 0 :=
    hsupp x (h.imp (fun h' => h'.trans hr.le) id)
  have hm := MasulloRH.muntz_smooth_positive_lattice u hu hc R hR hu₀ hmean (a:ℂ)
      (by simpa using ha) (by simpa using ha₁)
  have hψcont : Continuous ψ := Complex.continuous_ofReal.comp hu.continuous
  have hψ : MellinConvergent ψ (a:ℂ) := by
    apply mellinConvergent_of_isBigO_rpow (a:=a+1) (b:=0) (hψcont.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop R] with x hx
      simp [ψ, hsupp x (Or.inr hx)]
    · simp
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hr)] with x hx
      simp [ψ, hsupp x (Or.inl (le_of_lt hx))]
    · simpa using ha
  have hsum (t : ℝ) (ht : 0 < t) : Summable (fun n : ℕ => ψ (((n:ℝ)+1)*t)) := by
    obtain ⟨N,hN⟩ := exists_nat_ge (R/t)
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hnN : N≤n := by simpa using hn
    have hn' : R/t ≤ (n:ℝ)+1 := hN.trans (by exact_mod_cast (by omega : N≤n+1))
    simp [ψ, hsupp _ (Or.inr ((div_le_iff₀ ht).mp hn'))]
  exact MasulloRH.normalize_sieve_from_muntz p B hp hpB a ha ha₁ ψ hψ hsum hm.1 hm.2
