-- Prove2me | solution 1 for MasulloRH.compensated_shifted_resolvent_local_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T23:42:26.55079+00:00
-- url     : https://prove2.me/submissions/ea06a4a0-2e5f-480c-8fe7-de5c6c57a104

import Mathlib

/-!
Compensated shifted resolvents for local zero-count certificates.
The proof uses pure real and complex algebra from Mathlib. The height-six strip
conditions are explicit hypotheses; no zeta-zero-location theorem or
Riemann-hypothesis statement is imported or assumed.

The compensation term uses probes at 3 and 5/2. Its coefficient 8 makes the
kernel positive on every point satisfying the height-six strip hypotheses.
The shifted probe at 13/8 yields the rational unit-window bound 104/233.
-/

open scoped BigOperators

namespace MasulloRH.R6CompensatedKernelProof
noncomputable section

/-- Eight copies of the original real resolvent gap dominate the unwanted
subtraction term uniformly throughout the unconditional height-six region. -/
theorem compensation (β u : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hu : 36 ≤ u) :
    (5/2-β) / ((5/2-β)^2 + u) ≤
      8 * ((3-β) / ((3-β)^2 + u) - (5/2-β) / ((5/2-β)^2 + u)) := by
  let A := 3-β
  let B := 5/2-β
  have hA0 : 0 < A := by dsimp [A]; linarith
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  have hA3 : A ≤ 3 := by dsimp [A]; linarith
  have hB0 : 0 < B := by dsimp [B]; linarith
  have hB25 : B ≤ 5/2 := by dsimp [B]; linarith
  have ha : 0 < A^2+u := by nlinarith [sq_nonneg A]
  have hb : 0 < B^2+u := by nlinarith [sq_nonneg B]
  have hgap : 8 * (A/(A^2+u)-B/(B^2+u)) =
      (4*(u-A*B)/(A^2+u))/(B^2+u) := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
    dsimp [A, B]
    ring
  change B/(B^2+u) ≤ 8 * (A/(A^2+u)-B/(B^2+u))
  rw [hgap]
  apply (div_le_div_iff_of_pos_right hb).mpr
  apply (le_div_iff₀ ha).mpr
  have hAB : A*B ≤ (15/2 : ℝ) := by
    calc
      A*B ≤ 3*(5/2 : ℝ) := mul_le_mul hA3 hB25 hB0.le (by norm_num)
      _ = 15/2 := by norm_num
  have hprod : A*B*(4+A) ≤ (105/2 : ℝ) := by
    have h := mul_le_mul hAB (show 4+A ≤ 7 by linarith)
      (show 0 ≤ 4+A by linarith) (by norm_num : (0 : ℝ) ≤ 15/2)
    norm_num at h
    exact h
  have hlower : (54 : ℝ) ≤ (4-B)*u := by
    have h := mul_le_mul (show (3/2 : ℝ) ≤ 4-B by linarith) hu
      (by norm_num : (0 : ℝ) ≤ 36) (show 0 ≤ 4-B by linarith)
    norm_num at h
    exact h
  nlinarith


/-- The shifted probe can be moved horizontally without changing its
height-six compensation. -/
def shiftedKernelAt (σ T : ℝ) (z : ℂ) : ℝ :=
  (((σ : ℂ) + (T : ℂ) * Complex.I - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re +
    8 * (((3 : ℂ) - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re

theorem shiftedKernelAt_ge_poisson (σ T : ℝ) (z : ℂ)
    (hβ0 : 0 ≤ z.re) (hβ1 : z.re ≤ 1) (hγ : 36 ≤ z.im^2) :
    (σ-z.re) / ((σ-z.re)^2+(T-z.im)^2) ≤ shiftedKernelAt σ T z := by
  have heq : shiftedKernelAt σ T z =
      (σ-z.re) / ((σ-z.re)^2+(T-z.im)^2) -
        (5/2-z.re) / ((5/2-z.re)^2+z.im^2) +
      8 * ((3-z.re) / ((3-z.re)^2+z.im^2) -
        (5/2-z.re) / ((5/2-z.re)^2+z.im^2)) := by
    simp [shiftedKernelAt, Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [heq]
  have h := compensation z.re (z.im^2) hβ0 hβ1 hγ
  linarith

theorem shiftedKernelAt_pos (σ T : ℝ) (z : ℂ) (hσ : 1 < σ)
    (hβ0 : 0 ≤ z.re) (hβ1 : z.re ≤ 1) (hγ : 36 ≤ z.im^2) :
    0 < shiftedKernelAt σ T z := by
  apply lt_of_lt_of_le _ (shiftedKernelAt_ge_poisson σ T z hβ0 hβ1 hγ)
  apply div_pos (by linarith)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (sq_nonneg (T-z.im))

/-- The rational probe 13/8 is close to the optimal real part for a unit
window, while remaining in the Re s > 3/2 domain of the full-strip identity. -/
theorem rationalProbe_bounds (T : ℝ) (z : ℂ)
    (hβ0 : 0 ≤ z.re) (hβ1 : z.re ≤ 1) (hγ : 36 ≤ z.im^2) :
    (13/8-z.re) / ((13/8-z.re)^2+(T-z.im)^2) ≤ shiftedKernelAt (13/8) T z ∧
    0 < shiftedKernelAt (13/8) T z ∧
    (|z.im-T| ≤ 1 → (104/233 : ℝ) ≤ shiftedKernelAt (13/8) T z) := by
  refine ⟨shiftedKernelAt_ge_poisson _ _ _ hβ0 hβ1 hγ,
    shiftedKernelAt_pos _ _ _ (by norm_num) hβ0 hβ1 hγ, ?_⟩
  intro hwindow
  apply le_trans _ (shiftedKernelAt_ge_poisson (13/8) T z hβ0 hβ1 hγ)
  have hd : (T-z.im)^2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (z.im-T)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hwindow
    nlinarith [sq_abs (z.im-T)]
  have hden : 0 < (13/8-z.re)^2+(T-z.im)^2 := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith)) (sq_nonneg (T-z.im))
  apply (le_div_iff₀ hden).mpr
  have hp : 0 ≤ (13/8-(13/8-z.re)) * (104*(13/8-z.re)-64) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem finite_rational_window_mass_bound {ι : Type*} (S F : Finset ι) (hSF : S ⊆ F)
    (z : ι → ℂ) (m : ι → ℝ) (hm : ∀ i ∈ F, 0 ≤ m i) (T : ℝ)
    (hβ0 : ∀ i ∈ F, 0 ≤ (z i).re) (hβ1 : ∀ i ∈ F, (z i).re ≤ 1)
    (hγ : ∀ i ∈ F, 36 ≤ (z i).im^2)
    (hwindow : ∀ i ∈ S, |(z i).im-T| ≤ 1) :
    (∑ i ∈ S, m i) ≤
      (233/104 : ℝ) * ∑ i ∈ F, m i * shiftedKernelAt (13/8) T (z i) := by
  have hlocal : (104/233 : ℝ) * (∑ i ∈ S, m i) ≤
      ∑ i ∈ S, m i * shiftedKernelAt (13/8) T (z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := (rationalProbe_bounds T (z i) (hβ0 i (hSF hi)) (hβ1 i (hSF hi))
      (hγ i (hSF hi))).2.2 (hwindow i hi)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (hm i (hSF hi))
  have htotal : (∑ i ∈ S, m i * shiftedKernelAt (13/8) T (z i)) ≤
      ∑ i ∈ F, m i * shiftedKernelAt (13/8) T (z i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSF
    intro i hi _
    exact mul_nonneg (hm i hi)
      (rationalProbe_bounds T (z i) (hβ0 i hi) (hβ1 i hi) (hγ i hi)).2.1.le
  linarith


end
end MasulloRH.R6CompensatedKernelProof

theorem solution (T : ℝ) :
    let K : ℂ → ℝ := fun z =>
      (((13/8 : ℂ) + (T : ℂ) * Complex.I - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re +
        8 * (((3 : ℂ) - z)⁻¹ - ((5/2 : ℂ) - z)⁻¹).re
    (∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 36 ≤ z.im^2 →
      (13/8-z.re) / ((13/8-z.re)^2+(T-z.im)^2) ≤ K z ∧
      0 < K z ∧ (|z.im-T| ≤ 1 → (104/233 : ℝ) ≤ K z)) ∧
    (∀ (n : ℕ) (z : Fin n → ℂ) (m : Fin n → ℝ) (S : Finset (Fin n)),
      (∀ i, 0 ≤ m i) → (∀ i, 0 ≤ (z i).re) → (∀ i, (z i).re ≤ 1) →
      (∀ i, 36 ≤ (z i).im^2) → (∀ i ∈ S, |(z i).im-T| ≤ 1) →
      (∑ i ∈ S, m i) ≤ (233/104 : ℝ) * ∑ i, m i * K (z i)) := by
  dsimp only
  constructor
  · intro z h0 h1 hγ
    simpa [MasulloRH.R6CompensatedKernelProof.shiftedKernelAt] using
      MasulloRH.R6CompensatedKernelProof.rationalProbe_bounds T z h0 h1 hγ
  · intro n z m S hm h0 h1 hγ hwindow
    simpa [MasulloRH.R6CompensatedKernelProof.shiftedKernelAt] using
      MasulloRH.R6CompensatedKernelProof.finite_rational_window_mass_bound
      S Finset.univ (Finset.subset_univ _) z m (fun i _ => hm i) T
      (fun i _ => h0 i) (fun i _ => h1 i) (fun i _ => hγ i) hwindow
