-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.triangular_tail_substitution_support
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:51:02.368532+00:00
-- url     : https://prove2.me/submissions/1d801cde-76ac-4c04-ab12-d74d73d88d80

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_support_bound

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

/-- Triangular tail substitutions satisfy the weighted support bound: for the coordinate family
`X 0, X (j+1) + liftLogSeries m (R j)`, a nonzero coefficient at an exponent vector `a` forces the
weighted degree of `a` to be at least the coordinate weight `q i`. -/
theorem solution {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0) :
    ∀ (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (Fin.cases (MvPowerSeries.X 0)
          (fun j : Fin m => MvPowerSeries.X j.succ + liftLogSeries m (R j)) i) ≠ 0 →
      q i ≤ ∑ j, q j * (a j : ℝ) := by
  classical
  -- exponent vectors evaluate to the corresponding coordinates
  have hexp : ∀ (a : Fin (m + 1) → ℕ) (k : Fin (m + 1)),
      InterpolationMatrix.exponentVector a k = a k := by
    intro a k
    simp [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_apply_apply]
  intro i
  refine Fin.cases ?_ ?_ i
  · -- distinguished coordinate `X 0`: only the unit vector at `0` is supported
    intro a ha
    have ha' : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        ((MvPowerSeries.X (0 : Fin (m + 1))) : MvPowerSeries (Fin (m + 1)) ℂ) ≠ 0 := by
      simpa using ha
    have hs : InterpolationMatrix.exponentVector a =
        Finsupp.single (0 : Fin (m + 1)) 1 := by
      by_contra hne
      exact ha' (by rw [MvPowerSeries.coeff_X]; simp [hne])
    have ha0 : a 0 = 1 := by
      have h := congrArg (fun d : Fin (m + 1) →₀ ℕ => d 0) hs
      rw [hexp] at h
      simpa using h
    have hane : ∀ k : Fin (m + 1), k ≠ 0 → a k = 0 := by
      intro k hk
      have h := congrArg (fun d : Fin (m + 1) →₀ ℕ => d k) hs
      rw [hexp, Finsupp.single_eq_of_ne hk] at h
      exact h
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp [ha0]
    · intro k _ hk
      simp [hane k hk]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (m + 1))) h
  · -- shear coordinate `X (j+1) + liftLogSeries m (R j)`
    intro j a ha
    have ha' : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.X j.succ + liftLogSeries m (R j)) ≠ 0 := by
      simpa [Fin.cases_succ] using ha
    by_contra hcon
    have hlt : (∑ k : Fin (m + 1), q k * (a k : ℝ)) < q j.succ := not_le.mp hcon
    by_cases hlift : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (liftLogSeries m (R j)) ≠ 0
    · -- a nonzero lifted coefficient already forces the weighted bound
      exact absurd
        (liftLogSeries_support_bound (q := q) (T := T) (R := R) hq hT hR j a hlift)
        (not_le.mpr hlt)
    · -- otherwise the variable `X (j+1)` itself carries the coefficient
      have hlift0 : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (liftLogSeries m (R j)) = 0 := not_not.mp hlift
      have hX : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          ((MvPowerSeries.X j.succ) : MvPowerSeries (Fin (m + 1)) ℂ) ≠ 0 := by
        intro h0
        apply ha'
        rw [map_add, h0, hlift0]
        simp
      have hs : InterpolationMatrix.exponentVector a = Finsupp.single j.succ 1 := by
        by_contra hne
        exact hX (by rw [MvPowerSeries.coeff_X]; simp [hne])
      have hpoint : ∀ k : Fin (m + 1), a k = if k = j.succ then 1 else 0 := by
        intro k
        have h := congrArg (fun d : Fin (m + 1) →₀ ℕ => d k) hs
        rw [hexp] at h
        rw [h]
        by_cases hk : k = j.succ
        · subst hk
          simp
        · rw [Finsupp.single_eq_of_ne hk]
          simp [hk]
      have hweight : (∑ k : Fin (m + 1), q k * (a k : ℝ)) = q j.succ := by
        simp only [hpoint]
        rw [Finset.sum_eq_single j.succ]
        · simp
        · intro k _ hk
          simp [hk]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hweight] at hlt
      exact lt_irrefl _ hlt
