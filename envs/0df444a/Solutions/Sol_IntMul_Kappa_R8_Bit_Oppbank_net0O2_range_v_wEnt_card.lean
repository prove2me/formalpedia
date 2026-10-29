-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_range_v_wEnt_card
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:36:55.485002+00:00
-- url     : https://prove2.me/submissions/affc666f-dc3a-4d7e-8535-6b96de7535fd

import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

theorem solution :
    ((List.range 1771).flatMap fun _ => List.range 3542).length = 1771 * 3542 := by
  rw [List.length_flatMap]
  simp only [List.length_range]
  have hmap :
      List.map (fun _ : Nat => (3542 : Nat)) (List.range 1771) =
        List.replicate 1771 3542 :=
    List.map_eq_replicate_iff.mpr fun _ _ => rfl
  rw [hmap, List.sum_replicate]
  ring
