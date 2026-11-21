-- Prove2me | solution 1 for MasulloRH.principal_theta_endpoint_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:34:09.855481+00:00
-- url     : https://prove2.me/submissions/ebbb0630-7b3e-4dcd-a7f8-978caa1cf40b

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

private theorem endpoint_pole_cancel (L A B : ℂ → ℂ) (r b : ℂ)
    (hres : Tendsto (fun z : ℂ => (z-1)*L z) (𝓝[≠] 1) (𝓝 r)) (hA : ContinuousAt A 1)
    (hB : HasDerivAt B b 1) (hzero : B 1 = 0)
    (hr : ∀ z : ℂ, 1 < z.re → A z = L z * B z) : A 1 = r*b := by
  let z (e : ℝ) : ℂ := ((1+e : ℝ) : ℂ)
  have ht : Tendsto z (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous z := by dsimp [z]; fun_prop
      simpa [z] using (hc.continuousAt.continuousWithinAt (x := (0:ℝ)) (s := Ioi 0)).tendsto
    · filter_upwards [self_mem_nhdsWithin] with e he
      change ((1+e:ℝ):ℂ) ≠ 1
      exact_mod_cast (by linarith [show 0<e from he] : 1+e ≠ 1)
  have h := (hres.mul hB.tendsto_slope).comp ht
  have he : Tendsto (fun e : ℝ => A (z e)) (𝓝[>] 0) (𝓝 (r*b)) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have hr' : 1 < (z e).re := by simp [z]; exact he
    have hn : z e - 1 ≠ 0 := sub_ne_zero.mpr (fun hi => by rw [hi] at hr'; norm_num at hr')
    rw [hr _ hr']
    change ((z e-1)*L (z e))*slope B 1 (z e) = _
    rw [slope_def_module, hzero, sub_zero]
    simp only [smul_eq_mul]
    field_simp
  exact tendsto_nhds_unique (hA.tendsto.comp (tendsto_nhds_of_tendsto_nhdsWithin ht)) he

theorem principal_lattice_endpoint_log_moment {q : ℕ} [NeZero q]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0)
    :
    (∫ t in Ioi (0:ℝ), ∑' n : ℕ,
      (1 : DirichletCharacter ℂ q) (n+1:ℕ) * (ψ (((n:ℝ)+1)*t):ℂ)) =
      (∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)) *
        ∫ t in Ioi (0:ℝ), (Real.log t : ℂ) * (ψ t : ℂ) := by
  let χ : DirichletCharacter ℂ q := 1
  let f (t : ℝ) : ℂ := ψ t
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
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hp : (1:ℂ) ∈ {z : ℂ | 0 < z.re} := by change 0 < (1:ℂ).re; norm_num
  have hA1 := ((hFA 1 hp).differentiableAt (hopen.mem_nhds hp)).continuousAt
  have hzero : mellin f 1 = 0 := by
    simp only [mellin,f,sub_self,cpow_zero,one_smul]
    exact (integral_ofReal (𝕜:=ℂ) (μ:=volume.restrict (Ioi (0:ℝ))) (f:=ψ)).trans
      (by simp [hmean])
  have hfbot : f =O[𝓝[>] 0] (fun t : ℝ => t^(-(0:ℝ))) := by
    have hc0 : Continuous f := Complex.continuous_ofReal.comp hψ.continuous
    simpa only [neg_zero,Real.rpow_zero] using
      ((hc0.continuousAt.continuousWithinAt (x:=0) (s:=Ioi 0)).tendsto.isBigO_one ℝ)
  have hftop : f =O[atTop] (fun t : ℝ => t^(-(2:ℝ))) := by
    apply (isBigO_zero _ _).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop R] with t ht
    simp [f,hvan t (Or.inr ht)]
  have hint : LocallyIntegrableOn f (Ioi 0) :=
    (hψ.continuous.integrable_of_hasCompactSupport hc).ofReal.integrableOn.locallyIntegrableOn
  have hd := (mellin_hasDerivAt_of_isBigO_rpow (s:=1) hint hftop (by norm_num) hfbot (by norm_num)).2
  have hv := endpoint_pole_cancel χ.LFunction (mellin (lattice χ ψ)) (mellin f) _ _
    (DirichletCharacter.LFunctionTrivChar_residue_one (N:=q)) hA1 hd hzero hre
  simpa [mellin, lattice, f, χ, Algebra.smul_def] using hv
end TwistedSieve

open Set MeasureTheory

theorem solution {q : ℕ} [NeZero q]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0)
    :
    (∫ t in Ioi (0:ℝ), ∑' n : ℕ,
      (1 : DirichletCharacter ℂ q) (n+1:ℕ) * (ψ (((n:ℝ)+1)*t):ℂ)) =
      (∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)) *
        ∫ t in Ioi (0:ℝ), (Real.log t : ℂ) * (ψ t : ℂ) :=
  TwistedSieve.principal_lattice_endpoint_log_moment ψ hψ hc R hR hvan hmean
