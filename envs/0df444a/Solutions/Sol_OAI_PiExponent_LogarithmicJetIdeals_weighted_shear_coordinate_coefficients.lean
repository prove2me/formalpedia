-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:32:29.522054+00:00
-- url     : https://prove2.me/submissions/3bce0874-da8a-435b-a8a7-dcb22bd0454c

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_support_bound
import Mathlib.Algebra.Order.Floor.Ring

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

/-- Every inverse-shear coordinate `X i - liftLogSeries m (D i)` has its coefficients
supported above the weight `q i`: if the coefficient of a monomial `b` does not vanish,
then the weighted degree `∑ j, q j * b j` is at least `q i`. -/
theorem solution {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0) :
    ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)) i) ≠ 0 →
      q i ≤ ∑ j, q j * (b j : ℝ) := by
  classical
  have hq0 : 0 < q 0 := hq 0
  -- Uniform support thresholds for the coefficient cutoffs.
  let T : Fin m → ℕ := fun i => Nat.ceil (q i.succ / q 0)
  have hTle : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0 := by
    intro i
    have h := Nat.le_ceil (q i.succ / q 0)
    have h' : q i.succ / q 0 * q 0 ≤ (T i : ℝ) * q 0 :=
      mul_le_mul_of_nonneg_right h hq0.le
    rwa [div_mul_cancel₀ _ hq0.ne'] at h'
  have hDzero : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (D i) = 0 := by
    intro i k hk
    apply hD i k
    have hTlt : (T i : ℝ) < q i.succ / q 0 + 1 :=
      Nat.ceil_lt_add_one (div_pos (hq _) hq0).le
    have hk1 : (k : ℝ) + 1 ≤ (T i : ℝ) := by
      have hk' : k + 1 ≤ T i := hk
      exact_mod_cast hk'
    have hkx : (k : ℝ) < q i.succ / q 0 := by linarith
    have := mul_lt_mul_of_pos_right hkx hq0
    rwa [div_mul_cancel₀ _ hq0.ne'] at this
  intro i
  refine Fin.cases ?_ ?_ i
  · -- distinguished coordinate: the series is `X 0`
    intro b hb
    have hb' : MvPowerSeries.coeff b
        ((MvPowerSeries.X (0 : Fin (m + 1))) : MvPowerSeries (Fin (m + 1)) ℂ) ≠ 0 := by
      simpa using hb
    have hbs : b = Finsupp.single (0 : Fin (m + 1)) 1 := by
      by_contra hne
      refine hb' ?_
      rw [MvPowerSeries.coeff_X]
      simp [hne]
    rw [hbs]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp
    · intro t _ ht
      rw [Finsupp.single_eq_of_ne ht]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (m + 1))) h
  · -- inverse shear coordinate: the series is `X (j+1) - liftLogSeries m (D j)`
    intro j b hb
    by_contra hcon
    have hcon : (∑ t : Fin (m + 1), q t * (b t : ℝ)) < q j.succ := not_le.mp hcon
    set a : Fin (m + 1) → ℕ := fun t => b t with ha
    have hbexp : b = InterpolationMatrix.exponentVector a := by
      ext t
      simp [InterpolationMatrix.exponentVector, ha]
    have hsub : MvPowerSeries.coeff b
        (MvPowerSeries.X j.succ - liftLogSeries m (D j)) =
        MvPowerSeries.coeff b (MvPowerSeries.X j.succ) -
          MvPowerSeries.coeff b (liftLogSeries m (D j)) :=
      map_sub (MvPowerSeries.coeff b) _ _
    have hb' : MvPowerSeries.coeff b
        (MvPowerSeries.X j.succ - liftLogSeries m (D j)) ≠ 0 := by
      simpa [Fin.cases_succ] using hb
    have hlift : MvPowerSeries.coeff b (liftLogSeries m (D j)) = 0 := by
      by_contra hne
      have hne' : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (liftLogSeries m (D j)) ≠ 0 := by rwa [← hbexp]
      have hbnd := liftLogSeries_support_bound (q := q) (T := T) (R := D)
        hq hTle hDzero j a hne'
      simp only [ha] at hbnd
      exact absurd hbnd (not_le.mpr hcon)
    have hX : MvPowerSeries.coeff b
        ((MvPowerSeries.X j.succ) : MvPowerSeries (Fin (m + 1)) ℂ) ≠ 0 := by
      intro hzero
      exact hb' (by rw [hsub, hzero, hlift]; simp)
    have hbs : b = Finsupp.single j.succ 1 := by
      by_contra hne
      refine hX ?_
      rw [MvPowerSeries.coeff_X]
      simp [hne]
    have hweight : ∑ t : Fin (m + 1), q t * (b t : ℝ) = q j.succ := by
      rw [hbs]
      rw [Finset.sum_eq_single j.succ]
      · simp
      · intro t _ ht
        rw [Finsupp.single_eq_of_ne ht]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hweight] at hcon
    exact lt_irrefl _ hcon
