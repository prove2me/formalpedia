-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_tail_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:55:57.910797+00:00
-- url     : https://prove2.me/submissions/f490a3ff-ed48-43e9-9d7c-6c9f8bb8022d

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution (q y : ℕ) (hlo : 12 * q < y) (hhi : y ≤ 12 * q + 10) :
    ∃ i : ℕ, i < 12 * q + 10 ∧
      (if i = 12 * q + 7 then i + 3 else KnodelPrimeCordial.labelF i) = y := by
  let k : ℕ := y - 12 * q
  have hklo : 1 ≤ k := by
    dsimp [k]
    omega
  have hkhi : k ≤ 10 := by
    dsimp [k]
    omega
  have hy : y = 12 * q + k := by
    dsimp [k]
    omega
  let i : ℕ := 12 * q + (match k with
    | 1 => 3
    | 2 => 0
    | 3 => 4
    | 4 => 1
    | 5 => 2
    | 6 => 5
    | 7 => 8
    | 8 => 6
    | 9 => 9
    | _ => 7)
  refine ⟨i, ?_, ?_⟩
  · dsimp [i]
    interval_cases k <;> simp_all <;> omega
  · rw [hy]
    dsimp [i]
    interval_cases k <;>
      simp_all [KnodelPrimeCordial.labelF, Nat.add_mod, Nat.mul_mod] <;> omega
