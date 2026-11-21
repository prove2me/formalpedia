-- Prove2me | solution 1 for MasulloRH.double_angular_orbit_mass_and_prime_shell_majorant_escape
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:08:23.285368+00:00
-- url     : https://prove2.me/submissions/2077bfc6-dfd5-4833-9993-a0627c099352

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Filter Finset
open scoped ENNReal Topology

private theorem mass_prime_escape {a c : ℝ} (ha : a ≤ 1) (hc : 0 < c)
    (shell : ℕ → Nat.Primes → ℝ) (bound : ℕ → ℝ)
    (hbound : ∀ n (S : Finset Nat.Primes), ∑ p ∈ S, shell n p ≤ bound n)
    (hlim : ∀ p : Nat.Primes, Tendsto (fun n => shell n p) atTop (𝓝 (c*(p:ℝ)^(-a)))) :
    Tendsto bound atTop atTop := by
  have hn : ¬ Summable (fun p : Nat.Primes => c*(p:ℝ)^(-a)) := by
    intro hs
    have hh := hs.mul_left c⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hh
    have he := Nat.Primes.summable_rpow.mp hh
    linarith
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨S,hS⟩ : ∃ S : Finset Nat.Primes, b < ∑ p ∈ S, c*(p:ℝ)^(-a) := by
    by_contra! h
    exact hn (summable_of_sum_le (fun p => by positivity) h)
  have hconv : Tendsto (fun n => ∑ p ∈ S, shell n p) atTop (𝓝 (∑ p ∈ S, c*(p:ℝ)^(-a))) :=
    tendsto_finsetSum _ (fun p _ => hlim p)
  filter_upwards [hconv.eventually_const_lt hS] with n hn
  exact hn.le.trans (hbound n S)

private theorem marginal_mass {D K : Type*} [Group D] [Countable D] [Group K] [MeasurableSpace K]
    [MeasurableMul₂ K] (μ : Measure K) [SFinite μ] [μ.IsMulLeftInvariant]
    (w : D → K → ℝ≥0∞) (hw : ∀ r, Measurable (w r))
    (hprob : ∑' r : D, ∫⁻ h : K, w r h ∂μ = 1) :
    let b := fun r : D => ∫⁻ h : K, w r h ∂μ
    let C := fun ξ : D =>
      ∫⁻ g : K, ∑' r : D, ∫⁻ h : K, w r h * w (r * ξ) (h * g) ∂μ ∂μ
    (∀ ξ : D, C ξ = ∑' r : D, b r * b (r * ξ)) ∧
      ∑' ξ : D, C ξ = 1 := by
  intro b C
  have hjoint (r ξ : D) : Measurable (fun p : K × K => w r p.2 * w (r * ξ) (p.2 * p.1)) :=
    ((hw r).comp measurable_snd).mul ((hw _).comp (measurable_snd.mul measurable_fst))
  have heval (ξ : D) : C ξ = ∑' r, b r * b (r * ξ) := by
    unfold C
    rw [lintegral_tsum (fun r => (hjoint r ξ).lintegral_prod_right.aemeasurable)]
    apply tsum_congr
    intro r
    rw [lintegral_lintegral_swap (hjoint r ξ).aemeasurable]
    have inner (h : K) : (∫⁻ g : K, w r h * w (r * ξ) (h * g) ∂μ) = w r h * b (r * ξ) := by
      have hf : Measurable (fun g : K => w (r * ξ) (h * g)) := (hw _).comp (measurable_const.mul measurable_id)
      rw [lintegral_const_mul (w r h) hf]
      rw [lintegral_mul_left_eq_self (μ := μ) (w (r * ξ)) h]
    simp_rw [inner]
    exact lintegral_mul_const _ (hw r)
  refine ⟨heval, ?_⟩
  simp_rw [heval]
  rw [ENNReal.tsum_comm]
  have hb (r : D) : ∑' ξ : D, b (r * ξ) = 1 :=
    ((Equiv.mulLeft r).tsum_eq b).trans hprob
  simp_rw [ENNReal.tsum_mul_left, hb, mul_one]
  exact hprob

theorem solution {D K : Type*} [Group D] [Countable D] [Group K] [MeasurableSpace K]
    [MeasurableMul₂ K] (μ : Measure K) [SFinite μ] [μ.IsMulLeftInvariant]
    (w : ℕ → D → K → ℝ≥0∞) (hw : ∀ n r, Measurable (w n r))
    (hprob : ∀ n, ∑' r : D, ∫⁻ h : K, w n r h ∂μ = 1) :
    let b := fun n (r : D) => ∫⁻ h : K, w n r h ∂μ
    let C := fun n (ξ : D) =>
      ∫⁻ g : K, ∑' r : D, ∫⁻ h : K, w n r h * w n (r*ξ) (h*g) ∂μ ∂μ
    (∀ n ξ, C n ξ = ∑' r : D, b n r * b n (r*ξ)) ∧ (∀ n, ∑' ξ : D, C n ξ = 1) ∧
      ∀ (mask : ℕ → Nat.Primes → D → ℝ≥0∞), (∀ n ξ, ∑' p : Nat.Primes, mask n p ξ ≤ 1) →
      ∀ (coeff : ℕ → Nat.Primes → ℂ) (M : ℕ → ℝ), (∀ n, 0 ≤ M n) →
        (∀ n p, ENNReal.ofReal ‖coeff n p‖ ≤ ENNReal.ofReal (M n) * ∑' ξ, mask n p ξ * C n ξ) →
        ∀ a c : ℝ, a ≤ 1 → 0 < c →
          (∀ p : Nat.Primes, Tendsto (fun n => ‖coeff n p‖) atTop (𝓝 (c * (p:ℝ)^(-a)))) →
          Tendsto M atTop atTop := by
  intro b C
  have hf (n : ℕ) := marginal_mass μ (w n) (hw n) (hprob n)
  have htotal (n : ℕ) : ∑' ξ, C n ξ = 1 := (hf n).2
  refine ⟨fun n => (hf n).1, htotal, ?_⟩
  intro mask hmask coeff M hM hdom a c ha hc hlim
  apply mass_prime_escape ha hc (fun n p => ‖coeff n p‖) M _ hlim
  intro n S
  have hbudget : ∑' p : Nat.Primes, ∑' ξ, mask n p ξ * C n ξ ≤ 1 := by
    rw [ENNReal.tsum_comm]
    calc
      _ = ∑' ξ, (∑' p, mask n p ξ) * C n ξ := by simp_rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' ξ, 1 * C n ξ := ENNReal.tsum_le_tsum (fun ξ => mul_le_mul_of_nonneg_right (hmask n ξ) zero_le)
      _ = 1 := by simpa using htotal n
  have H : ENNReal.ofReal (∑ p ∈ S, ‖coeff n p‖) ≤ ENNReal.ofReal (M n) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    calc
      _ ≤ ∑ p ∈ S, ENNReal.ofReal (M n) * ∑' ξ, mask n p ξ * C n ξ :=
        Finset.sum_le_sum (fun p _ => hdom n p)
      _ = ENNReal.ofReal (M n) * ∑ p ∈ S, ∑' ξ, mask n p ξ * C n ξ :=
        (Finset.mul_sum ..).symm
      _ ≤ ENNReal.ofReal (M n) * 1 := mul_le_mul_of_nonneg_left ((ENNReal.sum_le_tsum S).trans hbudget) zero_le
      _ = _ := mul_one _
  exact (ENNReal.ofReal_le_ofReal_iff (hM n)).mp H
