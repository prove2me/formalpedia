-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.nat_scalar_centers_pairwise_distinct
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T23:04:28.780434+00:00
-- url     : https://prove2.me/submissions/69df45dc-ff1a-4c86-8e1c-0822cff54185

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (hr : ∃ i, r i ≠ 0) :
    ∀ j l : Fin K, j ≠ l → ∃ i : Fin m, (j.val : ℂ) * r i ≠ (l.val : ℂ) * r i := by
  intro j l hjl
  obtain ⟨i, hi⟩ := hr
  refine ⟨i, ?_⟩
  intro hmulr
  have hzero : ((j.val : ℂ) - (l.val : ℂ)) * r i = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr hmulr
  have hcastdiff : (j.val : ℂ) - (l.val : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hi
  have hvals : j.val = l.val := Nat.cast_injective (sub_eq_zero.mp hcastdiff)
  exact hjl (Fin.ext hvals)