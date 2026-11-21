-- Prove2me | solution 1 for MomentSearch.rakhmanov_equilibrium_product_envelope
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:52:43.590082+00:00
-- url     : https://prove2.me/submissions/39ec4889-1284-495c-85c7-05c75dbf99a3

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_phase_amplitude
import Theorems.Thm_MomentSearch_rakhmanov_equilibrium_potential

open Filter
open scoped Topology

private theorem hasDerivAt_mul_of_zero {f g : ℝ → ℝ} {y d : ℝ}
    (hf : HasDerivAt f d y) (hfy : f y = 0) (hg : ContinuousAt g y) :
    HasDerivAt (fun z => g z * f z) (g y * d) y := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim := (hg.tendsto.mono_left nhdsWithin_le_nhds).mul hf.tendsto_slope
  have heq : (fun z => g z * slope f y z) = slope (fun z => g z * f z) y := by
    funext z
    rw [slope_def_field, slope_def_field, hfy]
    simp [mul_div_assoc]
  rwa [heq] at hlim

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
    ∃ S : Polynomial ℝ, ∃ a : ℝ → ℝ,
      S.natDegree ≤ N-k ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < a z ∧ |S.eval z| * w z = a z * |f z|) ∧
      (∀ x ∈ Set.Ioo (-r) r, ∀ z ∈ Set.Icc (-1 : ℝ) 1, a z ≤ 12 * a x) ∧
      (∀ y ∈ Set.Ioo (-r) r, f y = 0 →
        |S.derivative.eval y| * w y = a y * (Real.pi * ρ y)) := by
  let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
  let ρ : ℝ → ℝ := fun t => (N : ℝ) / Real.pi * Real.arctan
    ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - t ^ 2))
  let φ : ℝ → ℝ := fun z => Real.pi * ∫ t in z..1, ρ t
  let f : ℝ → ℝ := fun z => Real.cos (φ z)
  let L : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
  let V : ℝ → ℝ := fun z => (N : ℝ) / 2 *
    ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z))
  let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
    ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
  have hw_def : w = (fun z => Real.exp (-V z)) := by
    funext z
    dsimp [w, V]
    congr 1
    ring
  obtain ⟨S, A, hdeg, hcont, hamp, hcomp⟩ :=
    MomentSearch.rakhmanov_phase_amplitude N k hk hkN
  obtain ⟨K, hflat, hupper⟩ := MomentSearch.rakhmanov_equilibrium_potential N k hk hkN
  change ∀ x ∈ Set.Icc (-r) r, L x - V x = K at hflat
  change ∀ z ∈ Set.Icc (-1 : ℝ) 1, L z - V z ≤ K at hupper
  change ∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < A z ∧
    S.eval z = A z * Real.exp (L z) * f z at hamp
  let a (z : ℝ) := A z * Real.exp (L z - V z)
  change ∃ S : Polynomial ℝ, ∃ a : ℝ → ℝ,
    S.natDegree ≤ N - k ∧
    (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < a z ∧ |S.eval z| * w z = a z * |f z|) ∧
    (∀ x ∈ Set.Ioo (-r) r, ∀ z ∈ Set.Icc (-1 : ℝ) 1, a z ≤ 12 * a x) ∧
    (∀ y ∈ Set.Ioo (-r) r, f y = 0 →
      |S.derivative.eval y| * w y = a y * (Real.pi * ρ y))
  have hr : r ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨zero_le_one, by nlinarith [div_nonneg (sq_nonneg (k : ℝ)) (sq_nonneg (N : ℝ))]⟩
  have hinside (z : ℝ) (hz : z ∈ Set.Ioo (-r) r) : z ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have ha_pos (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : 0 < a z :=
    mul_pos (hamp z hz).1 (Real.exp_pos _)
  have hweighted (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
      S.eval z * w z = a z * f z := by
    rw [(hamp z hz).2]
    simp only [a, hw_def, sub_eq_add_neg, Real.exp_add]
    ring
  refine ⟨S, a, hdeg, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨ha_pos z hz, ?_⟩
    simpa only [abs_mul, abs_of_pos (show 0 < w z from Real.exp_pos _), abs_of_pos (ha_pos z hz)] using
      congrArg abs (hweighted z hz)
  · intro x hx z hz
    have hx' := hinside x hx
    have hexp := Real.exp_le_exp.mpr (hupper z hz)
    dsimp [a]
    rw [hflat x ⟨hx.1.le, hx.2.le⟩]
    calc
      A z * Real.exp (L z - V z) ≤ A z * Real.exp K :=
        mul_le_mul_of_nonneg_left hexp (hamp z hz).1.le
      _ ≤ 12 * (A x * Real.exp K) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hcomp x hx' z hz) (Real.exp_pos _).le
  · intro y hy hfy
    have hy' := hinside y hy
    have hrho : Continuous ρ := by unfold ρ; fun_prop
    have hρnonneg : 0 ≤ ρ y := by
      apply mul_nonneg (div_nonneg (Nat.cast_nonneg N) Real.pi_pos.le)
      apply Real.arctan_nonneg.mpr
      positivity
    have hφ : HasDerivAt φ (Real.pi * -ρ y) y :=
      (intervalIntegral.integral_hasDerivAt_left (hrho.intervalIntegrable y 1)
        hrho.stronglyMeasurable.stronglyMeasurableAtFilter hrho.continuousAt).const_mul Real.pi
    have hf : HasDerivAt f (Real.sin (φ y) * (Real.pi * ρ y)) y := by
      convert hφ.cos using 1
      ring
    have hsin : |Real.sin (φ y)| = 1 := by
      change Real.cos (φ y) = 0 at hfy
      have hs := Real.sin_sq_add_cos_sq (φ y)
      rw [hfy, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hs
      rcases sq_eq_one_iff.mp hs with hs | hs <;> simp [hs]
    have hSzero : S.eval y = 0 := by rw [(hamp y hy').2, hfy, mul_zero]
    have hwcont : Continuous w := by
      have hV : Continuous V := by
        unfold V
        have hplus : Continuous (fun z : ℝ => 1 + z) := by fun_prop
        have hminus : Continuous (fun z : ℝ => 1 - z) := by fun_prop
        exact continuous_const.mul ((Real.continuous_mul_log.comp hplus).add
          (Real.continuous_mul_log.comp hminus))
      rw [hw_def]
      exact hV.neg.rexp
    have hy_nhds : Set.Ioo (-r) r ∈ 𝓝 y := isOpen_Ioo.mem_nhds hy
    have ha_local : a =ᶠ[𝓝 y] (fun z => A z * Real.exp K) := by
      filter_upwards [hy_nhds] with z hz
      simp only [a, hflat z ⟨hz.1.le, hz.2.le⟩]
    have ha_cont : ContinuousAt a y := by
      have hA := hcont.continuousAt (Filter.mem_of_superset hy_nhds fun z hz => hinside z hz)
      exact (hA.mul continuousAt_const).congr_of_eventuallyEq ha_local
    have hleft := hasDerivAt_mul_of_zero (S.hasDerivAt y) hSzero hwcont.continuousAt
    have hright := hasDerivAt_mul_of_zero hf hfy ha_cont
    have hlocal : (fun z => w z * S.eval z) =ᶠ[𝓝 y] (fun z => a z * f z) := by
      filter_upwards [hy_nhds] with z hz
      rw [mul_comm (w z), hweighted z (hinside z hz)]
    have hsign := hleft.unique (hright.congr_of_eventuallyEq hlocal)
    have habs := congrArg abs hsign
    simpa only [abs_mul, abs_of_pos (show 0 < w y from Real.exp_pos _), abs_of_pos (ha_pos y hy'),
      hsin, one_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hρnonneg, mul_comm (w y)] using habs
