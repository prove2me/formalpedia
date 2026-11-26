-- Prove2me | solution 1 for MurtySimon.choose_two_add_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:17.022803+00:00
-- url     : https://prove2.me/submissions/c97c0e68-e6ab-4320-a331-76f8530aa479

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
namespace MurtySimon
theorem _root_.solution (n : ℕ) : n.choose 2 + n / 2 = 2 * (n ^ 2 / 4) := by
  rw [Nat.choose_two_right]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) by ring,
      show (2 * k) ^ 2 = 4 * k ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]; ring
  · rw [show 2 * k + 1 - 1 = 2 * k by omega,
      show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
      show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring, Nat.mul_div_cancel_left _ (by norm_num),
      show (2 * k + 1) / 2 = k by omega, show (4 * (k ^ 2 + k) + 1) / 4 = k ^ 2 + k by omega]
    ring
end MurtySimon
