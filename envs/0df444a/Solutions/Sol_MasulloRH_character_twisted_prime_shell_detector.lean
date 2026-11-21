-- Prove2me | solution 1 for MasulloRH.character_twisted_prime_shell_detector
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:24:26.451573+00:00
-- url     : https://prove2.me/submissions/a69eed4e-c2b7-4cd7-8816-c740b9aec7be

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
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

section
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

open Filter Set Complex MeasureTheory Asymptotics
open scoped Topology

private theorem twist_continue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (A B : ℂ → ℂ)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.re})
    (hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.re})
    (hr : ∀ z : ℂ, 1 < z.re → A z = χ.LFunction z * B z)
    (s : ℂ) (h0 : 0<s.re) (h1 : s.re<1) :
    A s = χ.LFunction s * B s := by
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
  have hB' : AnalyticOnNhd ℂ (fun z => χ.LFunction z*B z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (χ.differentiableAt_LFunction z (Or.inl (hne z hz))).differentiableWithinAt.mul ((hB z hz.1).mono fun _ h => h.1)
  let p : ℂ := ⟨2,2*j⟩
  have hp : p ∈ U := by
    refine ⟨by norm_num [p],?_⟩
    change L p < 1
    rw [hL]
    change (2:ℝ)-j*(2*j)<1
    nlinarith
  have he : A =ᶠ[𝓝 p] (fun z => χ.LFunction z*B z) := by
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

open Complex MeasureTheory Set ENNReal
open scoped ENNReal

private lemma twist_muntz_dilation_norm (ψ : ℝ → ℂ) (s : ℂ) (b : ℝ) (hb : 0 < b) :
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

private lemma twist_muntz_tsum_integrable_of_summable_norm_integrals {F : ℕ → ℝ → ℂ}
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

theorem MasulloRH.hasMellin_dirichlet_dilation_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (f : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (hf : MellinConvergent f s) :
    HasMellin (fun t : ℝ => ∑' j : ℕ, χ (j + 1 : ℕ) * f (((j:ℝ)+1)*t))
      s (χ.LFunction s * mellin f s) := by
  let D (j : ℕ) : ℝ := j+1
  have hD (j : ℕ) : 0 < D j := by dsimp [D]; positivity
  let w (j : ℕ) : ℂ := χ (j+1 : ℕ)
  let U (j : ℕ) (t : ℝ) := (t:ℂ)^(s-1) * f (D j*t)
  let F (j : ℕ) (t : ℝ) := w j * U j t
  let ν := volume.restrict (Ioi (0:ℝ))
  have hU (j : ℕ) : Integrable (U j) ν := (MellinConvergent.comp_mul_left (hD j)).mpr hf
  have hF (j : ℕ) : Integrable (F j) ν := (hU j).const_mul _
  have hsD : Summable (fun j : ℕ => (D j)^(-s.re)) := by
    have hp := (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [D, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have hN : Summable (fun j => ∫ t, ‖F j t‖ ∂ν) := by
    let L := ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^(s-1) * f t‖
    have hi (j : ℕ) : (∫ t, ‖U j t‖ ∂ν) = (D j)^(-s.re)*L :=
      twist_muntz_dilation_norm f s (D j) (hD j)
    apply (hsD.mul_right L).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    intro j
    rw [← hi j]
    simp only [F, norm_mul, integral_const_mul]
    exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) (χ.norm_le_one _)
  have hpoint (t : ℝ) : (t:ℂ)^(s-1) * (∑' j : ℕ, w j * f (D j*t)) = ∑' j : ℕ, F j t := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp only [F,U]
    ring
  constructor
  · change Integrable (fun t : ℝ => (t:ℂ)^(s-1) * (∑' j : ℕ, w j * f (D j*t))) ν
    simp_rw [hpoint]
    exact twist_muntz_tsum_integrable_of_summable_norm_integrals hF hN
  · change (∫ t : ℝ, (t:ℂ)^(s-1) * (∑' j : ℕ, w j * f (D j*t)) ∂ν) = _
    simp_rw [hpoint]
    rw [← integral_tsum_of_summable_integral_norm hF hN]
    have hline0 (j : ℕ) : (∫ t, U j t ∂ν) = (1 / ((j:ℂ)+1)^s) * mellin f s := by
      have hpow : ((D j:ℝ):ℂ)^(-s) = 1 / ((j:ℂ)+1)^s := by simp [D,Complex.cpow_neg]
      simpa only [mellin,smul_eq_mul,hpow] using mellin_comp_mul_left f s (hD j)
    have hline (j : ℕ) : (∫ t, F j t ∂ν) =
        LSeries.term (fun n : ℕ => χ n) s (j+1) * mellin f s := by
      rw [show (∫ t, F j t ∂ν) = w j * (∫ t, U j t ∂ν) from integral_const_mul _ _, hline0]
      simp only [LSeries.term_of_ne_zero (Nat.succ_ne_zero j), Nat.cast_succ, w]
      ring
    simp_rw [hline]
    rw [tsum_mul_right, χ.LFunction_eq_LSeries hs, LSeries]
    have hser : Summable (LSeries.term (fun n : ℕ => χ n) s) :=
      χ.LSeriesSummable_of_one_lt_re hs
    rw [hser.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]

open Filter Set Finset MeasureTheory Asymptotics
open scoped Topology

namespace TwistedSieve

private lemma block_sum (f : ℕ → ℂ) (q K : ℕ) :
    ∑ n ∈ range (q*K), f n = ∑ k ∈ range K, ∑ r ∈ range q, f (q*k+r) := by
  induction K with
  | zero => simp
  | succ K h => rw [Nat.mul_succ,sum_range_add, sum_range_succ, h]

noncomputable def lattice {q : ℕ} (χ : DirichletCharacter ℂ q) (ψ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, χ (n+1:ℕ) * (ψ (((n:ℝ)+1)*t) : ℂ)

private lemma lattice_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    Measurable (lattice χ ψ) := by
  apply Measurable.tsum
  intro n
  exact (continuous_const.mul (Complex.continuous_ofReal.comp (hψ.comp (continuous_const.mul continuous_id)))).measurable

private lemma lattice_vanishes {q : ℕ} (χ : DirichletCharacter ℂ q) (ψ : ℝ → ℝ)
    (R : ℝ) (hR : 0<R) (hcut : ∀ t, R≤t → ψ t=0) (t : ℝ) (ht : R≤t) :
    lattice χ ψ t=0 := by
  unfold lattice
  convert tsum_zero (α:=ℂ) (β:=ℕ) using 1
  congr
  funext n
  have h : R ≤ ((n:ℝ)+1)*t := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (hR.le.trans ht)]
  simp [hcut _ h]

private lemma smooth_global_lipschitz (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, |ψ x-ψ y| ≤ L*|x-y| := by
  obtain ⟨L,hL⟩ := hc.deriv.exists_bound_of_continuous
    (hψ.continuous_deriv (by norm_num))
  have h0 := (norm_nonneg _).trans (hL 0)
  have lip : LipschitzWith ⟨L,h0⟩ ψ := lipschitzWith_of_nnnorm_deriv_le
    (hψ.differentiable (by norm_num)) (fun x => hL x)
  refine ⟨L,h0,?_⟩
  intro x y
  have hh := lip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at hh
  exact hh

private lemma bounded_twisted_lattice {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : ℝ → ℝ) (R : ℝ) (hR : 0<R) (hcut : ∀ t, R≤t → ψ t=0)
    (L D : ℝ) (hL : 0≤L) (hlip : ∀ x y : ℝ, |ψ x-ψ y| ≤ L*|x-y|)
    (hb : ∀ y : ℝ, 0<y → y≤(q:ℝ)*R → |∑' k : ℕ, ψ (((k:ℝ)+1)*y)| ≤ D) :
    ∃ C : ℝ, ∀ t : ℝ, 0<t → t≤R → ‖lattice χ ψ t‖ ≤ C := by
  have hq : 0 < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  refine ⟨(q:ℝ)*(D+L*(R+q*R)),?_⟩
  intro t ht htr
  let y : ℝ := (q:ℝ)*t
  have hy : 0<y := mul_pos hq ht
  have hyR : y ≤ (q:ℝ)*R := mul_le_mul_of_nonneg_left htr hq.le
  let K : ℕ := ⌈R/y⌉₊
  have hK : R ≤ (K:ℝ)*y := (div_le_iff₀ hy).mp (Nat.le_ceil _)
  have hK' : (K:ℝ)*y ≤ R + q*R := by
    calc _ ≤ (R/y + 1)*y := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg hR.le hy.le)).le hy.le
         _ = R+y := by field_simp
         _ ≤ _ := by linarith
  let v (r k : ℕ) := ψ (((q:ℝ)*k+r+1)*t)
  let w (k : ℕ) := ψ (((k:ℝ)+1)*y)
  have hw : (∑ k ∈ range K, w k) = ∑' k : ℕ, ψ (((k:ℝ)+1)*y) := by
    symm
    apply tsum_eq_sum
    intro k hk
    have hk' : K ≤ k := by simpa using hk
    apply hcut
    exact hK.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : K≤k+1)) hy.le)
  have hrow (r : ℕ) (hr : r ∈ range q) :
      ‖∑ k ∈ range K, (v r k : ℂ)‖ ≤ D + L*(R+q*R) := by
    have hr' : (r:ℝ)+1 ≤ q := by exact_mod_cast (mem_range.mp hr)
    have hd (k : ℕ) : |v r k-w k| ≤ L*y := by
      refine (hlip _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      have he : ((q:ℝ)*k+r+1)*t-((k:ℝ)+1)*y = -(((q:ℝ)-(r+1))*t) := by dsimp [y];ring
      rw [he, abs_neg, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hr') ht.le)]
      exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α:=ℝ) r]) ht.le
    have hdiff : |∑ k ∈ range K, (v r k - w k)| ≤ L*(R+q*R) := by
      calc
        _ ≤ ∑ k ∈ range K, L*y := by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le_of_le (range K) (f:=fun k : ℕ => v r k-w k) (fun k _ => (hd k : ‖v r k-w k‖ ≤ L*y)))
        _ = L*((K:ℝ)*y) := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hK' hL
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have he : (∑ k ∈ range K, v r k) =
        (∑ k ∈ range K, w k) + ∑ k ∈ range K, (v r k-w k) := by
      rw [sum_sub_distrib];ring
    rw [he]
    exact (abs_add_le ..).trans (add_le_add (hw ▸ hb y hy hyR) hdiff)
  have htrunc : lattice χ ψ t = ∑ n ∈ range (q*K), χ (n+1:ℕ) * (ψ (((n:ℝ)+1)*t) : ℂ) := by
    apply tsum_eq_sum
    intro n hn
    have hn' : q*K ≤ n := by simpa using hn
    have hrt : R ≤ ((n:ℝ)+1)*t := by
      have ha : (q:ℝ)*K ≤ n := by exact_mod_cast hn'
      calc _ ≤ (K:ℝ)*y := hK
           _ = ((q:ℝ)*K)*t := by dsimp [y];ring
           _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) ht.le
    simp [hcut _ hrt]
  rw [htrunc,block_sum,Finset.sum_comm]
  have he (r k : ℕ) : χ (q*k+r+1:ℕ) * (ψ ((((q*k+r:ℕ):ℝ)+1)*t) : ℂ) =
      χ (r+1:ℕ) * (v r k : ℂ) := by simp [v]
  simp_rw [he, ← Finset.mul_sum]
  calc _ ≤ ∑ r ∈ range q, (D+L*(R+q*R)) := by
           apply norm_sum_le_of_le
           intro r hr
           rw [norm_mul]
           exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans (by simpa using hrow r hr)
       _ = _ := by simp;ring
end TwistedSieve

open MeasureTheory Set Filter Finset Complex Asymptotics
open scoped Topology

namespace TwistedSieve

private lemma integrable_sieve {q : ℕ} (χ : DirichletCharacter ℂ q) (ψ : ℝ → ℝ)
    (hf : Continuous ψ) (R C : ℝ) (hz : ∀ t, R≤t → lattice χ ψ t=0)
    (hb : ∀ t, 0<t → t≤R → ‖lattice χ ψ t‖ ≤ C) :
    IntegrableOn (lattice χ ψ) (Ioi 0) := by
  have hnear : IntegrableOn (lattice χ ψ) (Ioc 0 R) := by
    apply (integrableOn_const (μ:=volume) (s:=Ioc 0 R) (C:=C) (by simp [Real.volume_Ioc])).mono'
      (lattice_measurable χ ψ hf).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht.1 ht.2
  have hfar : IntegrableOn (lattice χ ψ) (Ioi R) := by
    apply (integrableOn_congr_fun (g:=fun _ : ℝ => (0:ℂ)) _ measurableSet_Ioi).mpr (by simp)
    exact fun t ht => hz t (le_of_lt ht)
  apply (hnear.union hfar).mono_set
  intro t ht
  by_cases h : t≤R
  · exact Or.inl ⟨ht,h⟩
  · exact Or.inr (lt_of_not_ge h)

theorem character_lattice_muntz {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    HasMellin (lattice χ ψ) s (χ.LFunction s * mellin (fun t : ℝ => (ψ t:ℂ)) s) := by
  have hq : 0 < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨M,hM,hd⟩ := MasulloRH.exists_bound_iteratedDerivWithin_two hψ hc
  obtain ⟨L,hL,hl⟩ := smooth_global_lipschitz ψ hψ hc
  have hmean' : (∫ x : ℝ, ψ x) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ)) (f:=ψ)]
    · exact hmean
    · intro x hx; exact hvan x (Or.inl (le_of_not_gt hx))
  let D := M*(R+q*R)*(q*R)/12
  have hb (y : ℝ) (hy : 0<y) (hyr : y≤(q:ℝ)*R) :
      |∑' k : ℕ, ψ (((k:ℝ)+1)*y)| ≤ D := by
    apply (sieve_trap_bound ψ hψ R hR hvan hmean' M hM (hd 0) y hy).trans
    unfold D
    gcongr
  have hcut (t : ℝ) (ht : R≤t) := hvan t (Or.inr ht)
  obtain ⟨C,hC⟩ := bounded_twisted_lattice χ ψ R hR hcut L D hL hl hb
  have hz := lattice_vanishes χ ψ R hR hcut
  have hI := integrable_sieve χ ψ hψ.continuous R C hz hC
  have htop : ∀ᶠ t : ℝ in atTop, lattice χ ψ t=0 := (eventually_ge_atTop R).mono (fun t => hz t)
  have hbot : lattice χ ψ =O[𝓝[>] 0] (fun _ : ℝ => (1:ℝ)) := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with t ht hr
    simpa using (hC t ht hr.le)
  obtain ⟨hFm,hFA⟩ := muntz_holomorphic (lattice χ ψ) hI htop hbot
  have hdata := smooth_test_mellin_data ψ hψ hc R hcut
  have hre (z : ℂ) (hz : 1<z.re) :
      mellin (lattice χ ψ) z = χ.LFunction z * mellin (fun t : ℝ => (ψ t:ℂ)) z :=
    (MasulloRH.hasMellin_dirichlet_dilation_sum χ _ z hz (hdata.1 z (by linarith))).2
  exact ⟨hFm s h0,twist_continue χ _ _ hFA hdata.2 hre s h0 h1⟩

end TwistedSieve
end

section
open Complex MeasureTheory
open scoped BigOperators

private theorem twist_euler_dilates {ι : Type*} (T : Finset ι)
    (d : ι → ℕ) (c : ι → ℂ) (F : ℝ → ℂ) (s : ℂ) (hF : MellinConvergent F s)
    (hd : ∀ i ∈ T, 0 < d i) :
    HasMellin (fun t : ℝ => ∑ i ∈ T, c i * F ((d i : ℝ)*t)) s
      ((∑ i ∈ T, c i * ((d i : ℂ)^(-s))) * mellin F s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | @insert i T hi ih =>
    have hdi : 0 < (d i : ℝ) := Nat.cast_pos.mpr (hd i (Finset.mem_insert_self _ _))
    have htail := ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))
    have hscale := hasMellin_const_smul ((MellinConvergent.comp_mul_left hdi).mpr hF) (c i)
    have hscale' : HasMellin (fun t : ℝ => c i * F ((d i : ℝ)*t)) s
        (c i * (d i:ℂ)^(-s) * mellin F s) := by
      simpa only [smul_eq_mul, mellin_comp_mul_left F s hdi, Complex.ofReal_natCast, mul_assoc]
        using hscale
    simpa only [Finset.sum_insert hi, add_mul, ← hscale'.2, ← htail.2] using
      hasMellin_add hscale'.1 htail.1

private theorem twist_euler_prod_cpow (U : Finset ℕ) (s : ℂ) :
    (((∏ l ∈ U, l : ℕ) : ℂ)^s) = ∏ l ∈ U, (l : ℂ)^s := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

private theorem twist_euler_local {q p : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hp : p.Prime) (hs : 0 < s.re) :
    (p : ℂ)^s - χ p ≠ 0 ∧ 1 - χ p * (p : ℂ)^(-s) ≠ 0 ∧
      (1 - χ p * (p : ℂ)^(-s)) * (χ p / ((p : ℂ)^s - χ p)) = χ p * (p : ℂ)^(-s) := by
  have hnorm : 1 < ‖(p : ℂ)^s‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.one_lt_rpow (Nat.one_lt_cast.mpr hp.one_lt) hs
  have ha : (p:ℂ)^s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hb : (p:ℂ)^s - χ p ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hnorm
    exact hnorm.not_ge (χ.norm_le_one _)
  refine ⟨hb, ?_, ?_⟩
  · rw [Complex.cpow_neg]
    intro h
    apply hb
    field_simp [ha] at h
    linear_combination h
  · rw [Complex.cpow_neg]
    field_simp [ha, hb]

theorem MasulloRH.finite_twisted_prime_shell_mellin {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (p : ℕ) (hp : p ∈ P)
    (hP : ∀ l ∈ P, Nat.Prime l) (F : ℝ → ℂ) (s M : ℂ)
    (hs : 0 < s.re) (hF : HasMellin F s (χ.LFunction s * M)) :
    let G := fun t : ℝ => ∑ U ∈ (P.erase p).powerset,
      (χ p * ∏ l ∈ U, -χ l) * F (((p * ∏ l ∈ U, l : ℕ) : ℝ)*t)
    let W := χ.LFunction s * ∏ l ∈ P, (1 - χ l * (l : ℂ)^(-s))
    HasMellin G s (W * (χ p / ((p : ℂ)^s - χ p)) * M) ∧
      (W = 0 ↔ χ.LFunction s = 0) ∧
      (mellin G s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q ∨ M = 0) := by
  classical
  have hchi_ne : χ p ≠ 0 ↔ ¬ p ∣ q := (MulChar.apply_ne_zero_iff.trans
    (ZMod.isUnit_iff_coprime p q)).trans (hP p hp).coprime_iff_not_dvd
  have hchi : χ p = 0 ↔ p ∣ q := by simpa using not_congr hchi_ne
  let v (l : ℕ) : ℂ := χ l * (l : ℂ)^(-s)
  let V := ∏ l ∈ P, (1 - v l)
  let Q := P.erase p
  have hlocal := twist_euler_local χ s (hP p hp) hs
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l hl => (twist_euler_local χ s (hP l hl) hs).2.1
  have hsplit : V = (1 - v p) * ∏ l ∈ Q, (1-v l) :=
    (Finset.mul_prod_erase P (fun l => 1 - v l) hp).symm
  let d (U : Finset ℕ) : ℕ := p * ∏ l ∈ U, l
  let c (U : Finset ℕ) : ℂ := χ p * ∏ l ∈ U, -χ l
  have hd (U : Finset ℕ) (hU : U ∈ Q.powerset) : 0 < d U := by
    refine Nat.mul_pos (hP p hp).pos (Finset.prod_pos (fun l hl => ?_))
    exact (hP l (Finset.mem_of_mem_erase (Finset.mem_powerset.mp hU hl))).pos
  have hw (U : Finset ℕ) : c U * (d U : ℂ)^(-s) = v p * ∏ l ∈ U, -v l := by
    dsimp only [c, d, v]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, twist_euler_prod_cpow]
    simp only [← neg_mul, Finset.prod_mul_distrib]
    ring
  have hsum : (∑ U ∈ Q.powerset, c U * (d U : ℂ)^(-s)) = v p * ∏ l ∈ Q, (1 - v l) := by
    simp_rw [hw]
    rw [← Finset.mul_sum]
    congr 1
    simp only [sub_eq_add_neg, Finset.prod_one_add]
  have hres := twist_euler_dilates Q.powerset d c F s hF.1 hd
  rw [hsum, hF.2] at hres
  have hid : (v p * ∏ l ∈ Q, (1-v l)) * (χ.LFunction s * M) =
      (χ.LFunction s * V) * (χ p / ((p:ℂ)^s - χ p)) * M := by
    rw [hsplit]
    calc
      _ = ((1 - v p) * (χ p / ((p:ℂ)^s - χ p)) * ∏ l ∈ Q, (1-v l)) * (χ.LFunction s * M) := by
        rw [hlocal.2.2]
      _ = _ := by ring
  rw [hid] at hres
  refine ⟨hres, ?_, ?_⟩
  · change χ.LFunction s * V = 0 ↔ _
    simp [hV]
  · rw [hres.2]
    simp [mul_eq_zero, div_eq_zero_iff, hV, hlocal.1, hchi, or_assoc]
end

section
open Complex MeasureTheory Set ENNReal
open scoped ENNReal

namespace MasulloTwisted

private lemma weighted_dilation_norm (ψ : ℝ → ℂ) (s : ℂ) (b : ℝ) (hb : 0 < b) :
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

private lemma complex_tsum_integrable_of_summable_norm_integrals {F : ℕ → ℝ → ℂ}
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

theorem mellin_weighted_prime_powers (p : ℝ) (hp : 1 < p) (s c : ℂ) (hs : 0 < s.re)
    (hc : ‖c‖ ≤ 1) (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ s) :
    HasMellin (fun t : ℝ => ∑' j : ℕ, c ^ (j+1) * ψ (p^(j+1) * t)) s
      (c / ((p : ℂ)^s - c) * mellin ψ s) := by
  let D (j : ℕ) : ℝ := p^(j+1)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hD (j : ℕ) : 0 < D j := pow_pos hp0 _
  let d := c * (p : ℂ)^(-s)
  have hbase : ‖(p : ℂ)^(-s)‖ = p ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  have hd : ‖d‖ < 1 := by
    calc ‖d‖ = ‖c‖ * ‖(p:ℂ)^(-s)‖ := norm_mul _ _
         _ ≤ ‖(p:ℂ)^(-s)‖ := mul_le_of_le_one_left (norm_nonneg _) hc
         _ < 1 := by rw [hbase, Real.rpow_neg hp0.le]; exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp hs)
  have hpow (n : ℕ) : ((p^n : ℝ) : ℂ)^(-s) = ((p : ℂ)^(-s))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ p n, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
                         (pow_nonneg hp0.le n) hp0.le, ih, pow_succ]
  let F (j : ℕ) (t : ℝ) := c^(j+1) * ((t:ℂ)^(s-1) * ψ (D j * t))
  let ν := volume.restrict (Ioi (0 : ℝ))
  have hF (j : ℕ) : Integrable (F j) ν :=
    ((MellinConvergent.comp_mul_left (f := ψ) (hD j)).mpr hψ).const_mul (c ^ (j+1))
  let L := ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^(s-1) * ψ t‖
  have hnorm (j : ℕ) : (∫ t, ‖F j t‖ ∂ν) = ‖d‖^(j+1)*L := by
    change (∫ t in Ioi (0:ℝ), ‖c^(j+1) * ((t:ℂ)^(s-1) * ψ (D j * t))‖) = _
    simp only [norm_mul, integral_const_mul]
    have hw := weighted_dilation_norm ψ s (D j) (hD j)
    simp only [norm_mul] at hw
    rw [hw]
    dsimp only [D, d, L]
    have hpn := Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hp0 (j+1)) (-s)
    rw [Complex.neg_re] at hpn
    rw [← hpn, hpow, norm_mul, mul_pow, norm_pow, norm_pow, mul_assoc]
    simp only [norm_mul]
  have hsum : Summable (fun j => ∫ t, ‖F j t‖ ∂ν) := by
    simp_rw [hnorm]
    exact ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hd)).mul_right L
  have hpoint (t : ℝ) : (t:ℂ)^(s-1) * (∑' j : ℕ, c^(j+1) * ψ (D j*t)) = ∑' j : ℕ, F j t := by
    rw [← tsum_mul_left]
    congr 1
    funext j
    dsimp [F]
    ring
  constructor
  · change Integrable (fun t : ℝ => (t:ℂ)^(s-1) * (∑' j : ℕ, c^(j+1) * ψ (D j*t))) ν
    simp_rw [hpoint]; exact complex_tsum_integrable_of_summable_norm_integrals hF hsum
  · change (∫ t : ℝ, (t:ℂ)^(s-1) * (∑' j : ℕ, c^(j+1) * ψ (D j*t)) ∂ν) = _
    simp_rw [hpoint]
    rw [← integral_tsum_of_summable_integral_norm hF hsum]
    have hline (j : ℕ) : (∫ t, F j t ∂ν) = d^(j+1)*mellin ψ s := by
      change (∫ t in Ioi (0 : ℝ), c^(j+1) * ((t:ℂ)^(s-1) * ψ (D j*t))) = _
      rw [integral_const_mul]
      change c^(j+1) * mellin (fun t => ψ (D j*t)) s = _
      rw [mellin_comp_mul_left ψ s (hD j)]
      simp only [d, D, hpow, smul_eq_mul, mul_pow]
      ring
    simp_rw [hline]
    rw [tsum_mul_right]
    congr 1
    simp_rw [pow_succ]
    rw [tsum_mul_right, (hasSum_geometric_of_norm_lt_one hd).tsum_eq]
    have hz : (p:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hp0.ne'))
    have hne : 1-d ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h,norm_one] at hd; exact hd.false)
    dsimp only [d] at hne ⊢
    rw [Complex.cpow_neg] at hne ⊢
    have hden : (p:ℂ)^s-c ≠ 0 := by
      intro he
      have he' : (p:ℂ)^s = c := sub_eq_zero.mp he
      apply hne
      rw [← he',mul_inv_cancel₀ hz,sub_self]
    field_simp

theorem mellin_character_prime_powers {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (p : ℕ) (hp : 1 < p) (s : ℂ) (hs : 0 < s.re) (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ s) :
    HasMellin (fun t : ℝ => ∑' j : ℕ, (χ p)^(j+1) * ψ ((p:ℝ)^(j+1) * t)) s
      (χ p / ((p : ℂ)^s - χ p) * mellin ψ s) := by
  simpa only [Complex.ofReal_natCast] using mellin_weighted_prime_powers (p:ℝ)
    (by exact_mod_cast hp) s (χ p) hs (χ.norm_le_one _) ψ hψ

end MasulloTwisted
end

section
open Complex MeasureTheory Set Finset

theorem MasulloRH.twisted_prime_shell_calibration_and_zeros {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (p : ℕ) (hp : p ∈ P)
    (hP : ∀ l ∈ P, Nat.Prime l) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → u x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), u x) = 0) :
    let ψ : ℝ → ℂ := fun t => (u t : ℂ)
    let F (t : ℝ) := ∑' n : ℕ, χ (n+1:ℕ) * ψ (((n:ℝ)+1)*t)
    let G (t : ℝ) := ∑ U ∈ (P.erase p).powerset,
      (χ p * ∏ l ∈ U, -χ l) * F (((p * ∏ l ∈ U, l : ℕ) : ℝ)*t)
    let J (t : ℝ) := ∑' j : ℕ, (χ p)^(j+1) * ψ ((p:ℝ)^(j+1)*t)
    let W := χ.LFunction s * ∏ l ∈ P, (1 - χ l * (l : ℂ)^(-s))
    HasMellin F s (χ.LFunction s * mellin ψ s) ∧
    HasMellin J s (χ p / ((p:ℂ)^s - χ p) * mellin ψ s) ∧
    HasMellin G s (W * mellin J s) ∧ (W = 0 ↔ χ.LFunction s = 0) ∧
    (χ.LFunction s ≠ 0 → mellin G s / W = mellin J s) ∧
    (mellin G s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q ∨ mellin ψ s = 0) := by
  dsimp only
  have hF := TwistedSieve.character_lattice_muntz χ u hu hc R hR hvan hmean s h0 h1
  have htest := (smooth_test_mellin_data u hu hc R (fun t ht => hvan t (Or.inr ht))).1 s h0
  have hJ := MasulloTwisted.mellin_character_prime_powers χ p (hP p hp).one_lt s h0 _ htest
  obtain ⟨hg,hw,hzero⟩ := MasulloRH.finite_twisted_prime_shell_mellin χ P p hp hP _ s _ h0 hF
  refine ⟨hF,hJ,?_,hw,?_,hzero⟩
  · rw [hJ.2, ← mul_assoc]
    exact hg
  · intro hne
    apply (div_eq_iff (hw.not.mpr hne)).mpr
    exact hg.2.trans (by rw [hJ.2]; ring)
end

section
open Finset
open scoped Classical

namespace MasulloTwistStabil

def Survives (p B n : ℕ) : Prop :=
  p ∣ n ∧ ∀ q ≤ B, q.Prime → q ≠ p → ¬q ∣ n

theorem survives_iff_prime_power {p B n : ℕ} (hp : p.Prime) (hn : 0 < n) (hnB : n ≤ B) :
    Survives p B n ↔ ∃ j : ℕ, 0 < j ∧ n = p ^ j := by
  constructor
  · rintro ⟨hpn, hs⟩
    have heq := Nat.eq_prime_pow_of_unique_prime_dvd (p := p) hn.ne' (fun {q} hq hqn ↦ by
      by_contra hne
      exact hs q ((Nat.le_of_dvd hn hqn).trans hnB) hq hne hqn)
    refine ⟨_, Nat.pos_of_ne_zero (fun hzero ↦ hp.not_dvd_one ?_), heq⟩
    have hn1 : n = 1 := heq.trans (by rw [hzero, pow_zero])
    simpa only [hn1] using hpn
  · rintro ⟨j, hj, rfl⟩
    exact ⟨dvd_pow_self _ hj.ne', fun q _ hq hne hqd ↦
      hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd))⟩

theorem sum_surviving_eq_sum_prime_powers {A : Type*} [AddCommMonoid A]
    {p N B : ℕ} (hp : p.Prime) (hNB : N ≤ B) (f : ℕ → A) :
    ∑ n ∈ (Icc 1 N).filter (Survives p B), f n =
      ∑ j ∈ (Icc 1 N).filter (fun j ↦ p ^ j ≤ N), f (p ^ j) := by
  symm
  apply sum_bij (fun j _ ↦ p ^ j)
  · intro j hj
    obtain ⟨hj, hjN⟩ := mem_filter.mp hj
    have hpos : 0 < p ^ j := Nat.pow_pos hp.pos
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, hjN⟩,
      (survives_iff_prime_power hp hpos (hjN.trans hNB)).mpr ⟨j, (mem_Icc.mp hj).1, rfl⟩⟩
  · intro j _ k _ h
    exact Nat.pow_right_injective hp.two_le h
  · intro n hn
    obtain ⟨hn, hs⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := mem_Icc.mp hn
    obtain ⟨j, hj, rfl⟩ := (survives_iff_prime_power hp hnpos (hnN.trans hNB)).mp hs
    exact ⟨j, mem_filter.mpr ⟨mem_Icc.mpr ⟨hj, (Nat.lt_pow_self hp.one_lt).le.trans hnN⟩, hnN⟩, rfl⟩
  · intro _ _
    rfl

private theorem multiple_sum (d N : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ m ∈ Icc 1 (N / d), f (d*m) =
      ∑ n ∈ Icc 1 N, if d ∣ n then f n else 0 := by
  rw [← sum_filter]
  apply sum_bij (fun m _ ↦ d*m)
  · intro m hm
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hm0, by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN⟩, dvd_mul_right _ _⟩
  · intro m _ k _ he
    exact Nat.mul_left_cancel hd he
  · intro n hn
    obtain ⟨hn, m, rfl⟩ := mem_filter.mp hn
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hn
    refine ⟨m, mem_Icc.mpr ⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hmN)⟩, rfl⟩
    exact Nat.pos_of_ne_zero (fun h ↦ by simp [h] at hm0)
  · intro _ _
    rfl

private theorem product_dvd_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (U : Finset ℕ)
    (hU : ∀ q ∈ U, q.Prime ∧ q ≠ p) :
    p * ∏ q ∈ U, q ∣ n ↔ p ∣ n ∧ ∀ q ∈ U, q ∣ n := by
  have h2 : p ∉ U := fun h ↦ (hU p h).2 rfl
  rw [← prod_insert h2 (f := fun q : ℕ ↦ q)]
  constructor
  · intro h
    exact ⟨(dvd_prod_of_mem id (mem_insert_self p U)).trans h,
      fun q hq ↦ (dvd_prod_of_mem id (mem_insert_of_mem hq)).trans h⟩
  · rintro ⟨he, hall⟩
    apply dvd_trans _ (Nat.prod_primeFactors_dvd n)
    apply prod_dvd_prod_of_subset _ _ id
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact Nat.mem_primeFactors.mpr ⟨hp, he, hn.ne'⟩
    · exact Nat.mem_primeFactors.mpr ⟨(hU q hq).1, hall q hq, hn.ne'⟩

private theorem exclusion_weight (Q : Finset ℕ) (n : ℕ) :
    (∑ U ∈ Q.powerset, (-1 : ℂ)^U.card * (if ∀ q ∈ U, q ∣ n then 1 else 0)) =
      if ∀ q ∈ Q, ¬q ∣ n then 1 else 0 := by
  let w (q : ℕ) : ℂ := if q ∣ n then 1 else 0
  have hwm (U : Finset ℕ) : (∏ q ∈ U, w q) = (if ∀ q ∈ U, q ∣ n then 1 else 0) := by
    simp [w, prod_ite_zero]
  have hpm (q : ℕ) : 1 - w q = if ¬q ∣ n then 1 else 0 := by by_cases h : q ∣ n <;> simp [w, h]
  have h := prod_sub (fun _ : ℕ ↦ (1 : ℂ)) w Q
  simp only [hpm, hwm, prod_const_one, mul_one, prod_ite_zero] at h
  exact h.symm

def otherPrimesThrough (p B : ℕ) : Finset ℕ :=
  ((range (B+1)).filter Nat.Prime).erase p

theorem finite_sieve_indicator {p N B : ℕ} (hp : p.Prime) (hNB : N ≤ B) (f : ℕ → ℂ) :
    (∑ U ∈ (otherPrimesThrough p B).powerset, (-1 : ℂ)^U.card *
      ∑ m ∈ Icc 1 (N / (p * ∏ q ∈ U, q)), f ((p * ∏ q ∈ U, q) * m)) =
    ∑ j ∈ (Icc 1 N).filter (fun j ↦ p ^ j ≤ N), f (p ^ j) := by
  let Q := otherPrimesThrough p B
  have hQ {q : ℕ} : q ∈ Q ↔ q ≤ B ∧ q.Prime ∧ q ≠ p := by simp [Q, otherPrimesThrough, and_comm, and_left_comm]
  have hU (U : Finset ℕ) (hu : U ∈ Q.powerset) (q : ℕ) (hq : q ∈ U) : q.Prime ∧ q ≠ p :=
    (hQ.mp (mem_powerset.mp hu hq)).2
  rw [← sum_surviving_eq_sum_prime_powers hp hNB, sum_filter]
  change (∑ U ∈ Q.powerset, _) = _
  calc
    _ = ∑ U ∈ Q.powerset, ∑ n ∈ Icc 1 N, (-1 : ℂ)^U.card *
          (if p * ∏ q ∈ U, q ∣ n then f n else 0) := by
      apply sum_congr rfl
      intro U hu
      rw [multiple_sum _ _ (Nat.mul_pos hp.pos (prod_pos fun q hq ↦ (hU U hu q hq).1.pos)), mul_sum]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      have hnp := (mem_Icc.mp hn).1
      by_cases he : p ∣ n
      · have hrew (U : Finset ℕ) (hu : U ∈ Q.powerset) :
            (-1 : ℂ)^U.card * (if p * ∏ q ∈ U, q ∣ n then f n else 0) =
              ((-1 : ℂ)^U.card * (if ∀ q ∈ U, q ∣ n then 1 else 0)) * f n := by
          by_cases h : ∀ q ∈ U, q ∣ n <;> simp [product_dvd_iff hp hnp U (hU U hu), he, h]
        rw [sum_congr rfl hrew, ← sum_mul, exclusion_weight]
        have hs : (∀ q ∈ Q, ¬q ∣ n) ↔ Survives p B n := by
          constructor
          · exact fun h ↦ ⟨he, fun q hq hP hne ↦ h q (hQ.mpr ⟨hq, hP, hne⟩)⟩
          · exact fun h q hq ↦ h.2 q (hQ.mp hq).1 (hQ.mp hq).2.1 (hQ.mp hq).2.2
        by_cases h : Survives p B n <;> simp [hs, h]
      · have hs : ¬Survives p B n := fun h ↦ he h.1
        rw [if_neg hs]
        apply sum_eq_zero
        intro U hu
        simp [product_dvd_iff hp hnp U (hU U hu), he]

private lemma lattice_cutoff (f : ℕ → ℂ) (N c : ℕ) (hc : 0 < c)
    (hvan : ∀ n, N < n → f n = 0) :
    (∑' j : ℕ, f (c*(j+1))) = ∑ m ∈ Icc 1 (N/c), f (c*m) := by
  have ht (j : ℕ) (hj : j ∉ range (N/c)) : f (c*(j+1)) = 0 := by
    simp only [mem_range,not_lt] at hj
    apply hvan
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul hc).mp (by omega)
  rw [tsum_eq_sum ht]
  refine sum_bij' (fun j _ => j+1) (fun m _ => m-1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range] at hj; exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro m hm; obtain ⟨h1,h2⟩ := mem_Icc.mp hm; apply mem_range.mpr; omega
  · intro _ _; omega
  · intro m hm; have := (mem_Icc.mp hm).1; omega
  · intro _ _; rfl

private lemma power_cutoff {p : ℕ} (hp : p.Prime) (f : ℕ → ℂ) (N : ℕ) (hvan : ∀ n, N < n → f n = 0) :
    (∑ j ∈ (Icc 1 N).filter (fun j => p^j≤N), f (p^j)) = ∑' j : ℕ, f (p^(j+1)) := by
  have ht (j : ℕ) (hj : j ∉ range N) : f (p^(j+1)) = 0 := by
    simp only [mem_range,not_lt] at hj
    apply hvan
    exact lt_of_le_of_lt hj ((Nat.lt_succ_self j).trans (show j+1 < p^(j+1) from Nat.lt_pow_self hp.one_lt))
  rw [tsum_eq_sum ht, sum_filter]
  calc
      _ = ∑ j ∈ Icc 1 N, f (p^j) := by
        apply sum_congr rfl
        intro j _
        split_ifs with h
        · rfl
        · rw [hvan _ (lt_of_not_ge h)]
      _ = _ := by
        symm; refine sum_bij' (fun j _ => j+1) (fun m _ => m-1) ?_ ?_ ?_ ?_ ?_
        · intro j hj; simp only [mem_range] at hj; exact mem_Icc.mpr ⟨by omega,by omega⟩
        · intro m hm; obtain ⟨h1,h2⟩ := mem_Icc.mp hm; apply mem_range.mpr; omega
        · intro _ _; omega
        · intro m hm; have := (mem_Icc.mp hm).1; omega
        · intro _ _; rfl

theorem weighted_halfline_stabilization {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : ℕ) (hp : p.Prime) (ψ : ℝ → ℂ) (R : ℝ) (hcut : ∀ y : ℝ, R ≤ y → ψ y = 0) :
    let F (t : ℝ) := ∑' n : ℕ, χ (n+1:ℕ) * ψ (((n:ℝ)+1)*t)
    let Q (B : ℕ) := ((range (B+1)).filter Nat.Prime).erase p
    let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
      (χ p * ∏ l ∈ U, -χ l) * F (((p*∏ l ∈ U,l : ℕ) : ℝ)*t)
    ∀ a : ℝ, 0 < a → ∀ᶠ B : ℕ in Filter.atTop, ∀ t : ℝ, a ≤ t →
        G B t = ∑' j : ℕ, (χ p)^(j+1) * ψ ((p:ℝ)^(j+1)*t) := by
  intro F Q G a ha
  obtain ⟨N,hN⟩ := exists_nat_ge (R/a)
  filter_upwards [Filter.eventually_ge_atTop N] with B hB
  intro t ht
  let f (n : ℕ) := χ n * ψ ((n:ℝ)*t)
  have hvan (n : ℕ) (hn : N<n) : f n = 0 := by
    dsimp only [f]
    rw [hcut, mul_zero]
    have hna : R ≤ (N:ℝ)*a := (div_le_iff₀ ha).mp hN
    exact hna.trans (mul_le_mul (by exact_mod_cast hn.le) ht ha.le (Nat.cast_nonneg _))
  let d (U : Finset ℕ) := p * ∏ l ∈ U, l
  have hcoef (U : Finset ℕ) :
      χ p * ∏ l ∈ U, -χ l = (-1:ℂ)^U.card * χ (d U) := by
    simp [d,prod_neg,map_prod]
    ring
  have hU (U : Finset ℕ) (hU : U ∈ (Q B).powerset) :
      χ (d U) * F ((d U:ℝ)*t) = ∑ m ∈ Icc 1 (N/d U), f (d U * m) := by
    have hd : 0 < d U := Nat.mul_pos hp.pos (Finset.prod_pos fun l hl =>
      (mem_filter.mp (mem_of_mem_erase (mem_powerset.mp hU hl))).2.pos)
    rw [← lattice_cutoff f N (d U) hd hvan]
    dsimp only [F]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp only [f]
    push_cast
    rw [map_mul]
    ring_nf
  calc
    G B t = ∑ U ∈ (Q B).powerset, (-1:ℂ)^U.card *
        ∑ m ∈ Icc 1 (N/d U), f (d U*m) := by
      apply sum_congr rfl
      intro U h
      rw [hcoef U, mul_assoc, hU U h]
    _ = ∑ j ∈ (Icc 1 N).filter (fun j => p^j≤N), f (p^j) :=
      finite_sieve_indicator hp hB f
    _ = ∑' j : ℕ, f (p^(j+1)) := power_cutoff hp f N hvan
    _ = _ := by simp [f]

end MasulloTwistStabil
end

section
open Set MeasureTheory Filter
open scoped Topology

namespace MasulloUniversal

private theorem positive_powers_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (max t 0)^(n+2)) (((n:ℝ)+2)*(max x 0)^(n+1)) x := by
  have hpoly (y : ℝ) : HasDerivAt (fun t : ℝ => t^(n+2)) (((n:ℝ)+2)*y^(n+1)) y := by
    simpa using hasDerivAt_pow (n+2) y
  rcases lt_trichotomy x 0 with hx|rfl|hx
  · simp only [max_eq_right hx.le, zero_pow (Nat.succ_ne_zero _), mul_zero]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [max_eq_right hy.le]
  · simp only [max_self, zero_pow (Nat.succ_ne_zero _), mul_zero]
    have hL : HasDerivWithinAt (fun t : ℝ => (max t 0)^(n+2)) 0 (Iic 0) 0 :=
      (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
        (fun t ht => by simp [max_eq_right (mem_Iic.mp ht)]) (by simp)
    have hR' := (hpoly 0).hasDerivWithinAt (s:=Ici 0)
    simp only [zero_pow (Nat.succ_ne_zero _), mul_zero] at hR'
    have hR : HasDerivWithinAt (fun t : ℝ => (max t 0)^(n+2)) 0 (Ici 0) 0 :=
      hR'.congr (fun t ht => by simp [max_eq_left (mem_Ici.mp ht)]) (by simp)
    simpa using hL.union hR
  · rw [max_eq_left hx.le]
    apply (hpoly x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp [max_eq_left hy.le]

private theorem positive_cube_smooth : ContDiff ℝ 2 (fun t : ℝ => (max t 0)^3) := by
  have h2 (x : ℝ) : HasDerivAt (fun t : ℝ => (max t 0)^2) (2 * max x 0) x := by
    simpa using positive_powers_deriv 0 x
  have h3 (x : ℝ) : HasDerivAt (fun t : ℝ => (max t 0)^3) (3 * (max x 0)^2) x := by
    convert positive_powers_deriv 1 x using 1; norm_num
  have hs2 : ContDiff ℝ 1 (fun t : ℝ => (max t 0)^2) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (h2 x).differentiableAt, ?_⟩
    simp_rw [funext fun x => (h2 x).deriv]
    fun_prop
  apply (contDiff_succ_iff_deriv (n:=1)).mpr
  refine ⟨fun x => (h3 x).differentiableAt, by simp, ?_⟩
  rw [funext fun x => (h3 x).deriv]
  exact contDiff_const.mul hs2

theorem beta_test_smooth :
    ContDiff ℝ 2 (fun t : ℝ =>
      if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0) := by
  have hh : (fun t : ℝ => if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0) =
      fun t : ℝ => (max t 0)^3 * (max (1-t) 0)^3 := by
    funext t
    by_cases h1 : 0<t
    · by_cases h2 : t≤1
      · simp [h1,h2,max_eq_left h1.le]
      · simp [h2,max_eq_right (sub_nonpos.mpr (le_of_not_ge h2))]
    · simp [h1,max_eq_right (le_of_not_gt h1)]
  rw [hh]
  exact positive_cube_smooth.mul (positive_cube_smooth.comp (contDiff_const.sub contDiff_id))

end MasulloUniversal
end

section
open Complex Set

private theorem beta_mellin_sub {f g : ℝ → ℂ} {s A B : ℂ}
    (hf : HasMellin f s A) (hg : HasMellin g s B) :
    HasMellin (fun t => f t - g t) s (A-B) := by
  simpa only [← hf.2, ← hg.2] using hasMellin_sub hf.1 hg.1

private theorem beta_mellin_add {f g : ℝ → ℂ} {s A B : ℂ}
    (hf : HasMellin f s A) (hg : HasMellin g s B) :
    HasMellin (fun t => f t + g t) s (A+B) := by
  simpa only [← hf.2, ← hg.2] using hasMellin_add hf.1 hg.1

private theorem beta_mellin_scale {f : ℝ → ℂ} {s A : ℂ}
    (c : ℂ) (hf : HasMellin f s A) : HasMellin (fun t => c * f t) s (c*A) := by
  simpa only [smul_eq_mul, ← hf.2] using hasMellin_const_smul hf.1 c

theorem MasulloRH.hasMellin_cubic_beta_test (s : ℂ) (hs : -3 < s.re) :
    let b : ℝ → ℝ := fun t : ℝ => if t ∈ Ioc (0:ℝ) 1 then t^3 * (1-t)^3 else 0
    HasMellin (fun t : ℝ => (b t:ℂ)) s (6/((s+3)*(s+4)*(s+5)*(s+6))) ∧
      mellin (fun t : ℝ => (b t:ℂ)) s ≠ 0 := by
  intro b
  let T (n : ℕ) := (Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^n)
  have hT (n : ℕ) (hn : 3 ≤ n) : HasMellin (T n) s (1 / (s + n)) := by
    have hr : (3:ℝ) ≤ n := by exact_mod_cast hn
    have hn' : 0 < s.re + (n:ℂ).re := by simp; linarith
    simpa only [Complex.cpow_natCast] using hasMellin_cpow_Ioc (n:ℂ) hn'
  have h := beta_mellin_sub (beta_mellin_add
    (beta_mellin_sub (hT 3 (by decide)) (beta_mellin_scale 3 (hT 4 (by decide))))
    (beta_mellin_scale 3 (hT 5 (by decide)))) (hT 6 (by decide))
  have hf : (fun t : ℝ => T 3 t - 3 * T 4 t + 3 * T 5 t - T 6 t) =
      fun t : ℝ => (b t:ℂ) := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1
    · simp only [b,T,Set.indicator_of_mem ht,if_pos ht,Complex.ofReal_mul,
        Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_one]
      ring
    · simp only [b,T,Set.indicator_of_notMem ht,if_neg ht,Complex.ofReal_zero,
        mul_zero,sub_zero,add_zero]
  have hne (n : ℕ) (hn : 3 ≤ n) : s + (n:ℂ) ≠ 0 := by
    have hr : (3:ℝ) ≤ n := by exact_mod_cast hn
    intro hz
    have hz' := congrArg Complex.re hz
    simp at hz'
    linarith
  have h3 : s+3 ≠ 0 := by simpa using hne 3 (by decide)
  have h4 : s+4 ≠ 0 := by simpa using hne 4 (by decide)
  have h5 : s+5 ≠ 0 := by simpa using hne 5 (by decide)
  have h6 : s+6 ≠ 0 := by simpa using hne 6 (by decide)
  norm_num only [Nat.cast_ofNat] at h
  rw [hf] at h
  have hrat : 1/(s+3) - 3*(1/(s+4)) + 3*(1/(s+5)) - 1/(s+6) =
      6/((s+3)*(s+4)*(s+5)*(s+6)) := by
    field_simp [h3,h4,h5,h6]
    ring
  rw [hrat] at h
  exact ⟨h, h.2 ▸ div_ne_zero (by norm_num) (by simp [h3,h4,h5,h6])⟩
end

section
open Set

theorem MasulloRH.cubic_beta_four_differences_vanish :
    let b : ℝ → ℝ := fun t => if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0
    let D (k : ℕ) (f : ℝ → ℝ) (t : ℝ) := f t - ((2:ℝ)^k)⁻¹ * f (2*t)
    let v := D 6 (D 5 (D 4 (D 3 b)))
    (∀ t : ℝ, t ≤ 1/16 → v t = 0) ∧ (∀ t : ℝ, 1 ≤ t → v t = 0) := by
  intro b D v
  constructor
  · intro t ht
    by_cases h : 0 < t
    · have h0 : t ∈ Ioc (0:ℝ) 1 := by
        constructor <;> linarith
      have h1 : (2*t) ∈ Ioc (0:ℝ) 1 := by
        constructor <;> linarith
      have h2 : (2*(2*t)) ∈ Ioc (0:ℝ) 1 := by
        constructor <;> linarith
      have h3 : (2*(2*(2*t))) ∈ Ioc (0:ℝ) 1 := by
        constructor <;> linarith
      have h4 : (2*(2*(2*(2*t)))) ∈ Ioc (0:ℝ) 1 := by
        constructor <;> linarith
      dsimp only [v,D]
      simp only [b,if_pos h0,if_pos h1,if_pos h2,if_pos h3,if_pos h4]
      ring
    · have h0 : t ∉ Ioc (0:ℝ) 1 := by
        intro hh; linarith [hh.1]
      have h1 : (2*t) ∉ Ioc (0:ℝ) 1 := by
        intro hh; linarith [hh.1]
      have h2 : (2*(2*t)) ∉ Ioc (0:ℝ) 1 := by
        intro hh; linarith [hh.1]
      have h3 : (2*(2*(2*t))) ∉ Ioc (0:ℝ) 1 := by
        intro hh; linarith [hh.1]
      have h4 : (2*(2*(2*(2*t)))) ∉ Ioc (0:ℝ) 1 := by
        intro hh; linarith [hh.1]
      dsimp only [v,D]
      simp only [b,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,mul_zero,sub_zero]

  · intro t ht
    have hb (y : ℝ) (hy : 1 ≤ y) : b y = 0 := by
      by_cases h : y = 1
      · simp [b,h]
      · have hz : y ∉ Ioc (0:ℝ) 1 := fun hh => h (le_antisymm hh.2 hy)
        exact if_neg hz
    dsimp only [v,D]
    simp only [hb _ ht,hb (2*t) (by linarith),hb (2*(2*t)) (by linarith),hb (2*(2*(2*t))) (by linarith),hb (2*(2*(2*(2*t)))) (by linarith),mul_zero,sub_zero]
end

section
open Complex Set MeasureTheory

namespace MasulloUniversal

private noncomputable def dilation (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :=
  f t - c*f (2*t)

private theorem dilation_smooth (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (dilation c f) := by
  change ContDiff ℝ 2 (fun t => f t - c*f (2*t))
  fun_prop

private theorem dilation_mellin (c : ℝ) (f : ℝ → ℝ) (s A : ℂ)
    (h : HasMellin (fun t : ℝ => (f t:ℂ)) s A) :
    HasMellin (fun t : ℝ => (dilation c f t:ℂ)) s
      ((1-(c:ℂ)*(2:ℂ)^(-s))*A) := by
  have hi := (MellinConvergent.comp_mul_left (show (0:ℝ)<2 by norm_num)).mpr h.1
  have h2 := hasMellin_const_smul hi (c:ℂ)
  have he := hasMellin_sub h.1 h2.1
  have h2' := h2.2
  have hcomp := mellin_comp_mul_left (fun t : ℝ => (f t:ℂ)) s (show (0:ℝ)<2 by norm_num)
  simp only [Complex.ofReal_ofNat,smul_eq_mul,h.2] at hcomp
  simp only [smul_eq_mul] at h2' he
  rw [h2',h.2,hcomp] at he
  convert he using 1
  · simp [dilation]
  · ring

private theorem dilation_preserves (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) (s : ℂ) (hs : 0 < s.re)
    (hf : MellinConvergent (fun t : ℝ => (f t:ℂ)) s ∧ mellin (fun t : ℝ => (f t:ℂ)) s ≠ 0) :
    MellinConvergent (fun t : ℝ => (dilation c f t:ℂ)) s ∧
      mellin (fun t : ℝ => (dilation c f t:ℂ)) s ≠ 0 := by
  have hw := dilation_mellin c f s _ (show HasMellin _ _ _ from ⟨hf.1,rfl⟩)
  have hpow : ‖(2:ℂ)^(-s)‖ < 1 := by
    have hp := Complex.norm_cpow_eq_rpow_re_of_pos (show (0:ℝ)<2 by norm_num) (-s)
    rw [Complex.ofReal_ofNat,neg_re,Real.rpow_neg (by norm_num)] at hp
    rw [hp]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hs)
  have hm : ‖(c:ℂ)*(2:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt hpow
  refine ⟨hw.1, ?_⟩
  rw [hw.2]
  apply mul_ne_zero _ hf.2
  intro h
  rw [← sub_eq_zero.mp h,norm_one] at hm
  exact hm.false

private theorem dilation_two_mellin_ne (f : ℝ → ℝ) (s : ℂ) (h1 : s.re < 1)
    (hf : MellinConvergent (fun t : ℝ => (f t:ℂ)) s ∧ mellin (fun t : ℝ => (f t:ℂ)) s ≠ 0) :
    mellin (fun t : ℝ => (dilation 2 f t:ℂ)) s ≠ 0 := by
  have hw := dilation_mellin 2 f s _ (show HasMellin _ _ _ from ⟨hf.1,rfl⟩)
  rw [hw.2]
  apply mul_ne_zero _ hf.2
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  have hp := Complex.norm_cpow_eq_rpow_re_of_pos (show (0:ℝ)<2 by norm_num) (-s)
  rw [Complex.ofReal_ofNat,neg_re,Real.rpow_neg (by norm_num)] at hp
  simp only [Complex.ofReal_ofNat,norm_one,norm_mul,Complex.norm_ofNat,hp] at hh
  have hlt : (2:ℝ)^s.re < 2 := by
    simpa using (Real.rpow_lt_rpow_of_exponent_lt (x:=(2:ℝ)) (by norm_num) h1)
  have hn : 0 < (2:ℝ)^s.re := Real.rpow_pos_of_pos (by norm_num) _
  field_simp at hh
  linarith

private theorem dilation_two_zero_mean (f : ℝ → ℝ) (hi : IntegrableOn f (Ioi 0)) :
    (∫ t in Ioi (0:ℝ), dilation 2 f t) = 0 := by
  have h2 : IntegrableOn (fun t : ℝ => f (2*t)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff f 0 (show (0:ℝ)<2 by norm_num)).mpr (by simpa using hi)
  have hv := integral_comp_mul_left_Ioi f 0 (show (0:ℝ)<2 by norm_num)
  simp only [mul_zero, smul_eq_mul] at hv
  unfold dilation
  rw [integral_sub hi (h2.const_mul 2), integral_const_mul,hv]
  ring
end MasulloUniversal
end

section
open Complex Set MeasureTheory

theorem MasulloUniversal.fixed_test_data (s : ℂ) (h0 : 0<s.re) (h1 : s.re<1) :
    let b : ℝ → ℝ := fun t => if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0
    let D (c : ℝ) (f : ℝ → ℝ) (t : ℝ) := f t - c * f (2*t)
    let v := D ((2:ℝ)^6)⁻¹ (D ((2:ℝ)^5)⁻¹ (D ((2:ℝ)^4)⁻¹ (D ((2:ℝ)^3)⁻¹ b)))
    let w := D 2 v
    ContDiff ℝ 2 w ∧ HasCompactSupport w ∧
      (∀ x : ℝ, x ≤ 1/32 ∨ 1 ≤ x → w x = 0) ∧ (∫ t in Ioi (0:ℝ), w t) = 0 ∧
      mellin (fun t : ℝ => (w t:ℂ)) s ≠ 0 := by
  intro b D v w
  have hs (c : ℝ) {f : ℝ → ℝ} (h : ContDiff ℝ 2 f) : ContDiff ℝ 2 (D c f) :=
    dilation_smooth c h
  have hv : ContDiff ℝ 2 v := hs _ (hs _ (hs _ (hs _ beta_test_smooth)))
  obtain ⟨hl,hr⟩ := MasulloRH.cubic_beta_four_differences_vanish
  have hl' (t : ℝ) (ht : t ≤ 1/16) : v t = 0 := hl t ht
  have hr' (t : ℝ) (ht : 1 ≤ t) : v t = 0 := hr t ht
  have hc (f : ℝ → ℝ) (hz : ∀ t : ℝ, t ≤ 0 ∨ 1 ≤ t → f t = 0) : HasCompactSupport f := by
    apply HasCompactSupport.intro (K:=Icc (0:ℝ) 1) isCompact_Icc
    intro x hx
    apply hz
    by_cases h : x ≤ 0
    · exact Or.inl h
    · right; by_contra! h'; exact hx ⟨le_of_not_ge h,h'.le⟩
  have hcV := hc v (fun t ht => ht.elim (fun h => hl' t (by linarith)) (hr' t))
  have hcut (t : ℝ) (ht : t ≤ 1/32 ∨ 1 ≤ t) : w t = 0 := by
    change v t - 2 * v (2*t) = 0
    rcases ht with h|h
    · rw [hl' t (by linarith),hl' (2*t) (by linarith)]; ring
    · rw [hr' t h,hr' (2*t) (by linarith)]; ring
  have hb := MasulloRH.hasMellin_cubic_beta_test s (by linarith)
  have keep (c : ℝ) (hcl : 0≤c) (hcu : c≤1) {f : ℝ → ℝ}
      (hf : MellinConvergent (fun t : ℝ => (f t:ℂ)) s ∧ mellin (fun t : ℝ => (f t:ℂ)) s ≠ 0) :
      MellinConvergent (fun t : ℝ => (D c f t:ℂ)) s ∧ mellin (fun t : ℝ => (D c f t:ℂ)) s ≠ 0 :=
    dilation_preserves c hcl hcu f s h0 hf
  have base : MellinConvergent (fun t : ℝ => (b t:ℂ)) s ∧ mellin (fun t : ℝ => (b t:ℂ)) s ≠ 0 :=
    ⟨hb.1.1,hb.2⟩
  refine ⟨hs 2 hv,hc w (fun t ht => hcut t (ht.imp_left fun h => by linarith)),hcut,
    dilation_two_zero_mean v (hv.continuous.integrable_of_hasCompactSupport hcV).integrableOn,
    dilation_two_mellin_ne v s h1 ?_⟩
  exact keep _ (by norm_num) (by norm_num) (keep _ (by norm_num) (by norm_num)
    (keep _ (by norm_num) (by norm_num) (keep _ (by norm_num) (by norm_num) base)))
end

section
open Complex MeasureTheory Set Finset Filter

theorem solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (p : ℕ) (hp : Nat.Prime p)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    let admissible (u : ℝ → ℝ) := ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      ∃ R : ℝ, 0 < R ∧ (∀ x : ℝ, x ≤ 0 ∨ R ≤ x → u x = 0) ∧ (∫ x in Ioi (0:ℝ), u x) = 0
    let ψ (u : ℝ → ℝ) (t : ℝ) := (u t : ℂ)
    let F (u : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, χ (n+1:ℕ) * ψ u (((n:ℝ)+1)*t)
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let G (u : ℝ → ℝ) (B : ℕ) (t : ℝ) := ∑ U ∈ ((P B).erase p).powerset,
      (χ p * ∏ l ∈ U, -χ l) * F u (((p * ∏ l ∈ U, l : ℕ) : ℝ)*t)
    let J (u : ℝ → ℝ) (t : ℝ) := ∑' j : ℕ, (χ p)^(j+1) * ψ u ((p:ℝ)^(j+1)*t)
    let W (B : ℕ) := χ.LFunction s * ∏ l ∈ P B, (1 - χ l * (l : ℂ)^(-s))
    let b : ℝ → ℝ := fun t => if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0
    let D (c : ℝ) (f : ℝ → ℝ) (t : ℝ) := f t - c * f (2*t)
    let v := D ((2:ℝ)^6)⁻¹ (D ((2:ℝ)^5)⁻¹ (D ((2:ℝ)^4)⁻¹ (D ((2:ℝ)^3)⁻¹ b)))
    let w := D 2 v
    (∀ u : ℝ → ℝ, admissible u →
      (∀ a : ℝ, 0 < a → ∀ᶠ B : ℕ in atTop, ∀ t : ℝ, a ≤ t → G u B t = J u t) ∧
      HasMellin (F u) s (χ.LFunction s * mellin (ψ u) s) ∧
      HasMellin (J u) s (χ p / ((p:ℂ)^s - χ p) * mellin (ψ u) s) ∧
      ∀ B : ℕ, p ≤ B → HasMellin (G u B) s (W B * mellin (J u) s) ∧
        (W B = 0 ↔ χ.LFunction s = 0) ∧
        (χ.LFunction s ≠ 0 → mellin (G u B) s / W B = mellin (J u) s) ∧
        (mellin (G u B) s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q ∨ mellin (ψ u) s = 0)) ∧
    (admissible w ∧ (∀ x : ℝ, x ≤ 1/32 ∨ 1 ≤ x → w x = 0) ∧ mellin (ψ w) s ≠ 0 ∧
      ∀ B : ℕ, p ≤ B → (mellin (G w B) s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q)) := by
  intro admissible ψ F P G J W b D v w
  have hfinite (u : ℝ → ℝ) (hu : admissible u) (B : ℕ) (hB : p ≤ B) :
      HasMellin (F u) s (χ.LFunction s * mellin (ψ u) s) ∧
      HasMellin (J u) s (χ p / ((p:ℂ)^s - χ p) * mellin (ψ u) s) ∧
      HasMellin (G u B) s (W B * mellin (J u) s) ∧
        (W B = 0 ↔ χ.LFunction s = 0) ∧
        (χ.LFunction s ≠ 0 → mellin (G u B) s / W B = mellin (J u) s) ∧
        (mellin (G u B) s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q ∨ mellin (ψ u) s = 0) := by
    rcases hu with ⟨hsm,hc,R,hR,hcut,hm⟩
    exact MasulloRH.twisted_prime_shell_calibration_and_zeros χ (P B) p
      (mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩)
      (fun _ h => (mem_filter.mp h).2) s h0 h1 u hsm hc R hR hcut hm
  constructor
  · intro u had
    rcases had with ⟨hsm,hc,R,hR,hcut,hm⟩
    have had : admissible u := ⟨hsm,hc,R,hR,hcut,hm⟩
    have hw := hfinite u had p le_rfl
    refine ⟨MasulloTwistStabil.weighted_halfline_stabilization χ p hp (ψ u) R
      (fun t ht => by simp [ψ,hcut t (Or.inr ht)]), hw.1, hw.2.1, ?_⟩
    intro B hB
    exact (hfinite u had B hB).2.2
  · obtain ⟨hsm,hc,hcut,hm,hn⟩ := MasulloUniversal.fixed_test_data s h0 h1
    have hw0 (x : ℝ) (hx : x ≤ 0 ∨ 1 ≤ x) : w x = 0 :=
      hcut x (hx.imp_left (fun h => by linarith))
    have had : admissible w := ⟨hsm,hc,1,by norm_num,hw0,hm⟩
    refine ⟨had,hcut,hn,?_⟩
    intro B hB
    have he := (hfinite w had B hB).2.2.2.2.2
    constructor
    · intro hz
      exact (he.mp hz).elim Or.inl (fun h => h.elim Or.inr (fun hz' => (hn hz').elim))
    · intro h
      exact he.mpr (h.elim Or.inl (fun hr => Or.inr (Or.inl hr)))
end
