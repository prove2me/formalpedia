-- Prove2me | solution 1 for JRPHard.Periodic.exists_small_divisor
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:53:11.486769+00:00
-- url     : https://prove2.me/submissions/945ecf3d-dd4e-40c3-96f1-573ff07e4ccf

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 2.
theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    ∃ p : ℕ, p ∣ M ∧ 3 ≤ p ∧ 3 * p ≤ M := by
  have hp := Nat.minFac_prime (ne_of_gt h1)
  have hd := Nat.minFac_dvd M
  have hp3 : 3 ≤ M.minFac := by
    have hp2 := hp.two_le
    have hne : M.minFac ≠ 2 := by
      intro he
      rw [he] at hd
      exact hodd.not_two_dvd_nat hd
    omega
  refine ⟨M.minFac, hd, hp3, ?_⟩
  have hs := Nat.minFac_sq_le_self (by omega : 0 < M) hcomp
  nlinarith
