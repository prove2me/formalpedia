-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_grid_length
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:56:31.07892+00:00
-- url     : https://prove2.me/submissions/6f5d6733-6751-453c-bcf1-c88632aa0ecb

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem solution :
    ((List.range v).flatMap fun a =>
      (List.range wEnt).map fun w =>
        NB.entE (toNB ch0O) a w).length = 1771 * 3542 := by
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [show v = 1771 from rfl, show wEnt = 3542 from rfl]
  have hmap :
      List.map (fun _ : Nat => (3542 : Nat)) (List.range 1771) =
        List.replicate 1771 3542 :=
    List.map_eq_replicate_iff.mpr fun _ _ => rfl
  rw [hmap, List.sum_replicate]
  ring
