-- Prove2me | solution 1 for MasulloRH.even_derivative_endpoint_interpolation_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:34.895964+00:00
-- url     : https://prove2.me/submissions/a0f30ea5-5705-4905-acbb-0031fd12cadb

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
import Mathlib.Tactic.Ring

open Set MasulloRH.ThetaDerivativeCertificate

theorem solution (n : ℕ) (f : ℕ → ℝ → ℝ) (A : ℕ → ℝ) (l r : ℝ)
    (hd : ∀ k < 2*n, ∀ t, HasDerivAt (f k) (f (k+1) t) t)
    (he : ∀ i < n, |f (2*i) l| ≤ A i ∧ |f (2*i) r| ≤ A i)
    (ht : ∀ t ∈ Icc l r, |f (2*n) t| ≤ A n) (x : ℝ) (hx : x ∈ Icc l r) :
    |f 0 x| ≤ majorant ((r-l)^2/8) A n 0 := by
  have aux (k : ℕ) : ∀ i : ℕ, i+k=n → ∀ t ∈ Icc l r,
      |f (2*i) t| ≤ majorant ((r-l)^2/8) A k i := by
    induction k with
    | zero =>
      intro i hi t h
      have hi' : i=n := by omega
      simpa [hi',majorant] using ht t h
    | succ k ih =>
      intro i hi t h
      have hs := ih (i+1) (by omega)
      have hh := MasulloRH.scalar_curvature_endpoint_bound (f (2*i)) (f (2*i+1))
        (f (2*(i+1))) l r _ (A i) ((abs_nonneg _).trans (hs t h))
        (hd _ (by omega))
        (by simpa only [show 2*i+1+1=2*(i+1) by omega] using hd (2*i+1) (by omega))
        hs (he i (by omega)).1 (he i (by omega)).2 t h
      calc _ ≤ _ := hh
           _ = _ := by rw [majorant];ring
  simpa using aux n 0 (by omega) x hx
