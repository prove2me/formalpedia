-- Prove2me | solution 1 for HardyLittlewood.no_constellation_of_complete_residues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:56:29.347654+00:00
-- url     : https://prove2.me/submissions/ad4e2fb8-b2d6-4b86-a7f9-1a210cd54fe2

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

theorem solution {k : ℕ} (m : Fin k.succ → ℕ)
    (q p : ℕ) (hq : q.Prime) (hqp : q < p)
    (h : Function.Surjective (fun i : Fin k.succ => (p + 2 * m i : ZMod q))) :
    ¬ IsPrimeConstellation m p := by
  rintro ⟨_, _, hpr⟩
  obtain ⟨i, hi⟩ := h 0
  have hdvd : q ∣ p + 2 * m i := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact hi
  have := (Nat.prime_dvd_prime_iff_eq hq (hpr i)).mp hdvd
  omega
