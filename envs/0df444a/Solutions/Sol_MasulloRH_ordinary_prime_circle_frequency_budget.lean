-- Prove2me | solution 1 for MasulloRH.ordinary_prime_circle_frequency_budget
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:38:36.848929+00:00
-- url     : https://prove2.me/submissions/9ac0cc3d-0bfc-4bb6-a325-5b16c8d2c864

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Fourier.PoissonSummation

section
open Real Set MeasureTheory Complex
open scoped FourierTransform

namespace PrimeCircle

theorem fourier_sampling_bound (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (L : ℝ) (hL : 0<L) (j : ℤ) (hj : j ≠ 0) :
    ‖𝓕 f ((j:ℝ)/L)‖ ≤ (L^2 * (∫ x : ℝ, ‖deriv (deriv f) x‖) / (4*π^2)) / (j.natAbs:ℝ)^2 := by
  let ξ : ℝ := (j:ℝ)/L
  have hd : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv (n:=1)).mp hf |>.2.2
  have h0 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have h1 : Integrable (deriv f) := hd.continuous.integrable_of_hasCompactSupport hc.deriv
  have h2 : Integrable (deriv (deriv f)) := hd.continuous_deriv_one.integrable_of_hasCompactSupport hc.deriv.deriv
  have hF2 := congrFun (Real.fourier_deriv h1 (hd.differentiable one_ne_zero) h2) ξ
  have hF1 := congrFun (Real.fourier_deriv h0 (hf.differentiable (by norm_num)) h1) ξ
  rw [hF1] at hF2
  have hb : ‖𝓕 (deriv (deriv f)) ξ‖ ≤ ∫ x : ℝ, ‖deriv (deriv f) x‖ := by
    rw [Real.fourier_real_eq]
    exact (norm_integral_le_integral_norm _).trans_eq (by simp)
  rw [hF2] at hb
  simp only [norm_smul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos,mul_one] at hb
  have hu : |ξ| = (j.natAbs:ℝ)/L := by simp [ξ,abs_div,abs_of_pos hL,Nat.cast_natAbs]
  rw [hu] at hb
  have hj0 : 0 < (j.natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hj
  apply (le_div_iff₀ (sq_pos_of_pos hj0)).mpr
  apply (le_div_iff₀ (by positivity : 0<(4:ℝ)*π^2)).mpr
  have h := mul_le_mul_of_nonneg_left hb (sq_nonneg L)
  convert h using 1
  · field_simp
    ring
end PrimeCircle
end

section
open Finset

private theorem orbit_frequency_one_sided_tail (f : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (K : ℝ) (hK : 0 ≤ K) (hf : ∀ j : ℕ, ‖f j‖ ≤ K / ((N:ℝ)+j+1)^2) :
    Summable (fun j => ‖f j‖) ∧ ∑' j, ‖f j‖ ≤ K/N := by
  let g (i : ℕ) := K/((N:ℝ) + i)
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have step (j : ℕ) : ‖f j‖ ≤ g j - g (j+1) := by
    refine (hf j).trans ?_
    dsimp only [g]
    push_cast
    have h0 : 0 < (N:ℝ) + j := by positivity
    have h1 : 0 < (N:ℝ) + j + 1 := by positivity
    rw [← add_assoc (N:ℝ) j 1]
    field_simp [h0,h1]
    nlinarith
  have hsum (b : ℕ) : ∑ j ∈ range b, ‖f j‖ ≤ K/N := by
    calc
      _ ≤ ∑ j ∈ range b, (g j - g (j+1)) := sum_le_sum (fun j _ => step j)
      _ = g 0 - g b := sum_range_sub' g b
      _ ≤ K/N := by simp only [g,Nat.cast_zero,add_zero]; exact sub_le_self _ (by positivity)
  exact ⟨summable_of_sum_range_le (fun _ => norm_nonneg _) hsum,
    Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) hsum⟩

theorem MasulloRH.bilateral_frequency_tail_bound (c : ℤ → ℂ) (N : ℕ) (hN : 0 < N)
    (K : ℝ) (hK : 0 ≤ K) (hc : ∀ j : ℤ, N < j.natAbs → ‖c j‖ ≤ K/(j.natAbs:ℝ)^2) :
    let pos := fun k : ℕ => c ((N+k+1 : ℕ) : ℤ)
    let neg := fun k : ℕ => c (-((N+k+1 : ℕ) : ℤ))
    Summable (fun k => ‖pos k‖) ∧ Summable (fun k => ‖neg k‖) ∧
    (∑' k, ‖pos k‖) + (∑' k, ‖neg k‖) ≤ 2*K/N ∧
    ‖(∑' k, pos k) + (∑' k, neg k)‖ ≤ 2*K/N := by
  intro pos neg
  have hp := orbit_frequency_one_sided_tail pos N hN K hK (fun k => by
    simpa [pos] using hc (N+k+1:ℕ) (by change N < N+k+1; omega))
  have hm := orbit_frequency_one_sided_tail neg N hN K hK (fun k => by
    have hh := hc (-((N+k+1:ℕ):ℤ)) (by rw [Int.natAbs_neg]; change N < N+k+1; omega)
    rw [Int.natAbs_neg] at hh
    simpa [neg] using hh)
  have hboth : (∑' k, ‖pos k‖) + (∑' k, ‖neg k‖) ≤ 2*K/N := by
    calc
      _ ≤ K/N + K/N := add_le_add hp.2 hm.2
      _ = _ := by ring
  refine ⟨hp.1,hm.1,hboth, (norm_add_le _ _).trans ?_⟩
  exact (add_le_add (norm_tsum_le_tsum_norm hp.1) (norm_tsum_le_tsum_norm hm.1)).trans hboth


theorem MasulloRH.symmetric_frequency_truncation_bound (c : ℤ → ℂ) (N : ℕ) (hN : 0 < N)
    (K : ℝ) (hK : 0 ≤ K) (hc : ∀ j : ℤ, N < j.natAbs → ‖c j‖ ≤ K/(j.natAbs:ℝ)^2) :
    Summable c ∧
      ‖(∑' j : ℤ, c j) - (c 0 + ∑ k ∈ range N, (c ((k+1:ℕ):ℤ) + c (-((k+1:ℕ):ℤ))))‖
        ≤ 2*K/N := by
  let pos (k : ℕ) := c ((k+1:ℕ):ℤ)
  let neg (k : ℕ) := c (-((k+1:ℕ):ℤ))
  obtain ⟨hp,hm,_,hb⟩ := bilateral_frequency_tail_bound c N hN K hK hc
  have hp' : Summable (fun k => pos (k+N)) := by
    simpa only [pos, Nat.add_comm N] using hp.of_norm
  have hm' : Summable (fun k => neg (k+N)) := by
    simpa only [neg, Nat.add_comm N] using hm.of_norm
  have sp : Summable pos := (summable_nat_add_iff N).mp hp'
  have sm : Summable neg := (summable_nat_add_iff N).mp hm'
  have sp0 : Summable (fun k : ℕ => c k) := (summable_nat_add_iff 1).mp sp
  have sm0 : Summable (fun k : ℕ => c (-(k+1))) := by simpa [neg] using sm
  have hz : Summable c := Summable.of_nat_of_neg_add_one sp0 sm0
  refine ⟨hz,?_⟩
  have he : (∑' j : ℤ, c j) = c 0 + ∑' k : ℕ, (pos k + neg k) := by
    rw [← tsum_nat_add_neg_add_one hz,sp0.tsum_add sm0,sp0.tsum_eq_zero_add,sp.tsum_add sm]
    simp [pos,neg,add_assoc]
  have ht := (sp.add sm).sum_add_tsum_nat_add N
  change (∑ k ∈ range N, (pos k + neg k)) +
      (∑' k : ℕ, (pos (k+N) + neg (k+N))) = ∑' k : ℕ, (pos k + neg k) at ht
  rw [he, ← ht, hp'.tsum_add hm']
  change ‖c 0 + ((∑ k ∈ range N, (pos k + neg k)) +
      ((∑' k, pos (k+N)) + ∑' k, neg (k+N))) - (c 0 + ∑ k ∈ range N, (pos k + neg k))‖ ≤ _
  rw [show ∀ a b d : ℂ, a+(b+d)-(a+b)=d from by intros; ring]
  simpa only [pos,neg,Nat.add_comm N] using hb
end

section
open Set Filter MeasureTheory TopologicalSpace Asymptotics Real
open scoped Topology FourierTransform

namespace MasulloOrbit

private theorem norm_translates_summable (g : C(ℝ, ℂ)) (hgC : HasCompactSupport g) :
    ∀ K : Compacts ℝ, Summable (fun n : ℤ => ‖(g.comp (ContinuousMap.addRight n)).restrict K‖) := by
  have hgO : (g : ℝ → ℂ) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hgC
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hgC] with x hx
    rw [hx]
    simp [sq_nonneg]
  intro K
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((isBigO_norm_restrict_cocompact g (by norm_num : (0:ℝ)<2) hgO K).comp_tendsto Int.tendsto_coe_cofinite)

private theorem fourier_dilate (f : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (j : ℤ) :
    𝓕 (fun x : ℝ => f (L*x)) (j:ℝ) = L⁻¹ • 𝓕 f ((j:ℝ)/L) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  let G (y : ℝ) := Complex.exp ((↑(-2 * π * y * ((j:ℝ)/L)) : ℂ) * Complex.I) • f y
  have hG (x : ℝ) : Complex.exp ((↑(-2 * π * x * (j:ℝ)) : ℂ) * Complex.I) • f (L*x) = G (L*x) := by
    dsimp only [G]
    congr 3
    field_simp [hL.ne']
  simp_rw [hG]
  simpa only [abs_of_pos (inv_pos.mpr hL)] using Measure.integral_comp_mul_left G L

/-- Periodizing in a log coordinate of period `L` samples the Fourier transform at `j/L`,
with coefficient `1/L` for the normalized circle measure. -/
theorem fourierCoeffOn_periodization {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (j : ℤ) :
    fourierCoeffOn hL (fun x : ℝ => ∑' n : ℤ, f (x + (n:ℝ)*L)) j =
      L⁻¹ • 𝓕 f ((j:ℝ)/L) := by
  let g : C(ℝ, ℂ) := ⟨fun x => f (L*x), hf.comp (continuous_const.mul continuous_id)⟩
  have hnorm := norm_translates_summable g (hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne'))
  let P := Function.Periodic.lift (g.periodic_tsum_comp_add_zsmul 1)
  have hP (x : ℝ) : P (x : UnitAddCircle) = ∑' n : ℤ, f (L*x+(n:ℝ)*L) := by
    dsimp only [P]
    rw [Function.Periodic.lift_coe]
    simp only [zsmul_one]
    rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hnorm)]
    congr 1
    funext n
    change f (L*(x+(n:ℝ))) = f _
    congr 1; ring
  have hphase (x : ℝ) : fourier (-j) ((L*x : ℝ) : AddCircle L) =
      fourier (-j) (x : UnitAddCircle) := by
    rw [fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  let v (x : ℝ) := fourier (-j) (x : AddCircle L) • ∑' n : ℤ, f (x+(n:ℝ)*L)
  have hcoeff : fourierCoeffOn hL (fun x : ℝ => ∑' n : ℤ, f (x + (n:ℝ)*L)) j = fourierCoeff P j := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral P j 0]
    simp only [sub_zero,zero_add,div_one,one_smul,one_div]
    have hfour (x : ℝ) : fourier (-j) (x : AddCircle (L-0)) = fourier (-j) (x : AddCircle L) := by
      simp only [fourier_coe_apply,sub_zero]
    simp_rw [hfour]
    change L⁻¹ • (∫ x in (0:ℝ)..L, v x) = _
    have hres := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) v hL.ne'
    rw [mul_zero,mul_one] at hres
    rw [← hres]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [v]
    rw [hphase, hP]
  rw [hcoeff, Real.fourierCoeff_tsum_comp_add hnorm]
  exact fourier_dilate f hL j

/-- Poisson reconstruction of the unweighted log-lattice trace under absolute frequency summability. -/
theorem sum_frequency_samples_eq_periodic_trace {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hfreq : Summable (fun j : ℤ => 𝓕 f ((j:ℝ)/L))) :
    (∑' j : ℤ, 𝓕 f ((j:ℝ)/L)) = (L:ℂ) * (∑' n : ℤ, f ((n:ℝ)*L)) := by
  let g : C(ℝ, ℂ) := ⟨fun x => f (L*x), hf.comp (continuous_const.mul continuous_id)⟩
  have hnorm := norm_translates_summable g (hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL.ne'))
  have hsample (j : ℤ) : 𝓕 (g : ℝ → ℂ) (j:ℝ) = L⁻¹ • 𝓕 f ((j:ℝ)/L) := fourier_dilate f hL j
  have hsg : Summable (fun j : ℤ => 𝓕 (g : ℝ → ℂ) (j:ℝ)) := by
    simp_rw [hsample]
    exact hfreq.const_smul L⁻¹
  have hpoisson := Real.tsum_eq_tsum_fourier hnorm hsg 0
  have hchar (n : ℤ) : fourier n ((0:ℝ) : UnitAddCircle) = 1 := fourier_eval_zero n
  simp only [zero_add, hchar, mul_one, hsample] at hpoisson
  have hphys : (∑' n : ℤ, f ((n:ℝ)*L)) = L⁻¹ • (∑' j : ℤ, 𝓕 f ((j:ℝ)/L)) := by
    simpa only [g, ContinuousMap.coe_mk, mul_comm L, tsum_const_smul''] using hpoisson
  rw [hphys, Complex.real_smul, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

end MasulloOrbit
end

section
open MeasureTheory Set Finset Complex
open scoped FourierTransform

theorem solution
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (a : ℝ) (ha : 0 < a) :
    let L (p : ℕ) := Real.log (p:ℝ)
    let c (p : ℕ) (j : ℤ) := 𝓕 f ((j:ℝ)/L p)
    let T (p : ℕ) := (L p : ℂ) * ∑' n : ℤ, f ((n:ℝ)*L p)
    let S (p N : ℕ) := c p 0 + ∑ k ∈ range N, (c p ((k+1:ℕ):ℤ) + c p (-((k+1:ℕ):ℤ)))
    let M := ∫ x : ℝ, ‖deriv (deriv f) x‖
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let A (B : ℕ) := (∑ p ∈ P B, (L p)^2) * M / (2*Real.pi^2)
    let W (B : ℕ) := riemannZeta (a:ℂ) * ((∏ p ∈ P B, (1-(p:ℝ)^(-a)) : ℝ):ℂ)
    let Nstar (B : ℕ) := ⌈((B:ℝ)+1)*A B/‖W B‖⌉₊ + 1
    (∀ p : ℕ, ∀ hp : p.Prime,
      (∀ j : ℤ, fourierCoeffOn (show (0:ℝ)<L p from Real.log_pos (by exact_mod_cast hp.one_lt))
        (fun x : ℝ => ∑' n : ℤ, f (x+(n:ℝ)*L p)) j = (L p)⁻¹ • c p j) ∧
      ∀ N : ℕ, 0 < N →
        ‖T p - S p N‖ ≤ (L p)^2*M/(2*Real.pi^2*N) ∧
        ((∀ n : ℤ, f ((n:ℝ)*L p) = if n=1 then 1 else 0) →
          (∀ j : ℤ, j.natAbs ≤ N → c p j=0) →
            2 * Real.pi^2 * N / (L p) ≤ M)) ∧
    (∀ B N : ℕ, 0 < N →
      ‖(∑ p ∈ P B, T p) - (∑ p ∈ P B, S p N)‖ ≤ A B/N) ∧
    (riemannZeta (a:ℂ) ≠ 0 → ∀ B N : ℕ, Nstar B ≤ N →
      ‖(∑ p ∈ P B, T p) - (∑ p ∈ P B, S p N)‖ / ‖W B‖ ≤ 1/((B:ℝ)+1)) := by
  intro L c T S M P A W Nstar
  have hM : 0≤M := integral_nonneg (fun x => norm_nonneg _)
  have hpos (p : ℕ) (hp : p.Prime) : 0<L p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have localBound (p N : ℕ) (hp : p.Prime) (hN : 0<N) :
      ‖T p - S p N‖ ≤ (L p)^2*M/(2*Real.pi^2*N) := by
    let K := (L p)^2*M/(4*Real.pi^2)
    have hk : 0≤K := by dsimp [K]; positivity
    obtain ⟨hs,hb⟩ := MasulloRH.symmetric_frequency_truncation_bound (c p) N hN K hk (fun j hj =>
      PrimeCircle.fourier_sampling_bound f hf hc _ (hpos p hp) _ (fun h => by simp [h] at hj))
    have hP := MasulloOrbit.sum_frequency_samples_eq_periodic_trace (hpos p hp) f hf.continuous hc hs
    calc ‖T p-S p N‖ = ‖(∑' j : ℤ, c p j)-S p N‖ := by rw [show T p = ∑' j : ℤ,c p j from hP.symm]
         _ ≤ 2*K/(N:ℝ) := hb
         _ = _ := by dsimp only [K]; ring
  have hsum (B N : ℕ) (hn : 0<N) :
      ‖(∑ p ∈ P B, T p) - (∑ p ∈ P B, S p N)‖ ≤ A B/N := by
    rw [← sum_sub_distrib]
    calc _ ≤ ∑ p ∈ P B, (L p)^2*M/(2*Real.pi^2*N) :=
           norm_sum_le_of_le _ (fun p hp => localBound p N (mem_filter.mp hp).2 hn)
         _ = _ := by simp only [A,← sum_div,← sum_mul]; ring
  refine ⟨?_,hsum,?_⟩
  · intro p hp
    refine ⟨MasulloOrbit.fourierCoeffOn_periodization (hpos p hp) f hf.continuous hc, ?_⟩
    intro N hN
    refine ⟨localBound p N hp hN,?_⟩
    intro hone hsmall
    have hs0 : S p N = 0 := by
      dsimp only [S]
      rw [hsmall 0 (by simp),zero_add]
      apply sum_eq_zero
      intro k hk
      have hkN : k+1≤N := by have := Finset.mem_range.mp hk; omega
      rw [hsmall ((k+1:ℕ):ℤ) (by exact hkN), hsmall (-((k+1:ℕ):ℤ)) (by rw [Int.natAbs_neg]; exact hkN), add_zero]
    have hT : T p = (L p:ℂ) := by simp [T,hone]
    have he := localBound p N hp hN
    rw [hs0,sub_zero,hT,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos p hp)] at he
    have hden : 0 < 2*Real.pi^2*(N:ℝ) := by positivity
    have ht := (le_div_iff₀ hden).mp he
    apply (div_le_iff₀ (hpos p hp)).mpr
    nlinarith only [ht,hpos p hp, mul_pos (hpos p hp) (hpos p hp),sq_nonneg (L p)]
  · intro hz B N hN
    have hE : 0 < ∏ p ∈ P B, (1 - (p:ℝ)^(-a)) := by
      apply prod_pos
      intro p hp
      have hpr : p.Prime := (mem_filter.mp hp).2
      rw [Real.rpow_neg (Nat.cast_nonneg p)]
      exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hpr.one_lt) ha))
    have hW : 0 < ‖W B‖ := norm_pos_iff.mpr (mul_ne_zero hz (Complex.ofReal_ne_zero.mpr hE.ne'))
    have hnpos : 0<N := (Nat.zero_lt_succ _).trans_le hN
    have hNreal : 0<(N:ℝ) := Nat.cast_pos.mpr hnpos
    have hBreal : 0<(B:ℝ)+1 := by positivity
    have hsize : ((B:ℝ)+1)*A B/‖W B‖ ≤ (N:ℝ) := by
      exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hN)
    have hs := hsum B N hnpos
    apply (div_le_iff₀ hW).mpr
    apply hs.trans
    rw [div_le_iff₀ hW] at hsize
    field_simp [hNreal.ne', hBreal.ne']
    linarith
end

